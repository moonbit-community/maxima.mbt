// Port of src/defint.lisp (part 3): beta integrals, log integrals,
// ggr, radicals, poles, and integrals of log and exp functions.

///|
/// Check e for an expression of the form x^kk*(b*x^n+a)^l.  If it
/// matches, Return the two values kk and (list l a n b).
fn bata0(e : Value, ivar : Value) -> (Value, Value) raise {
  if atom(e) {
    (Nil, Nil)
  } else if mexptp(e).truthy() {
    // We have f(x)^y.  Look to see if f(x) has the desired form.  Then
    // f(x)^y has the desired form too, with suitably modified values.
    //
    // XXX: Should we ask for the sign of f(x) if y is not an integer?
    // This transformation we're going to do requires that f(x)^y be
    // real.
    let base = nth(1, e)
    let power = nth(2, e)
    let (kk, cc) = bata0(base, ivar)
    if kk.truthy() {
      // Got a match.  Adjust kk and cc appropriately.
      let l = nth(0, cc)
      let a = nth(1, cc)
      let n = nth(2, cc)
      let b = nth(3, cc)
      (mul2(kk, power), list([mul2(l, power), a, n, b]))
    } else {
      (Nil, Nil)
    }
  } else {
    let mut k : Value = Nil
    let mut c : Value = Nil
    if mtimesp(e).truthy() &&
      cdddr(e) is Nil &&
      (
        {
          k = findp(cadr(e), ivar)
          k.truthy() &&
          {
            c = bxm(caddr(e), polyinx(caddr(e), ivar, Nil), ivar)
            c.truthy()
          }
        } ||
        {
          k = findp(caddr(e), ivar)
          k.truthy() &&
          {
            c = bxm(cadr(e), polyinx(cadr(e), ivar, Nil), ivar)
            c.truthy()
          }
        }
      ) {
      (k, c)
    } else {
      c = bxm(e, polyinx(e, ivar, Nil), ivar)
      if c.truthy() {
        k = Fix(0L)
        (k, c)
      } else {
        (Nil, Nil)
      }
    }
  }
}

///|
/// Integrals of the form i(log(x)^m*x^k*(a+b*x^n)^l,x,0,ul).  There are
/// two cases to consider: One case has ul>0, b<0, a=-b*ul^n, k>-1, l>-1,
/// n>0, m a nonnegative integer.  The second case has ul=inf, l < 0.
///
/// These integrals are essentially partial derivatives of the Beta
/// function (i.e. the Eulerian integral of the first kind).  Note that,
/// currently, with the default setting intanalysis:true, this function
/// might not even be called for some of these integrals.  However, this
/// can be palliated by setting intanalysis:false.
fn zto1(e : Value, ivar : Value, ul : Value) -> Value raise {
  if !(mtimesp(e).truthy() || mexptp(e).truthy()) {
    return Nil
  }
  let m : Ref[Value] = Ref(Fix(0L))
  let log = list2(list1(q_p_log), ivar)
  let set_m = lfunc("set-m", args => {
    m.val = arg(args, 0)
    m.val
  })
  find_if(fac => powerofx(fac, log, set_m, ivar).truthy(), cdr(e)) |> ignore
  if freeof(ivar, m.val).truthy() &&
    eq(ask_integer(m.val, q_d_integer), q_d_yes) &&
    !eq(d_asksign(m.val), q_d_neg) {
    let e = div(e, list3(list1(q_mexpt), log, m.val))
    if eq(ul, q_d_inf) {
      let (kk, s, d, r, cc) = batap_inf(e, ivar)
      // We have i(x^kk/(d+cc*x^r)^s,x,0,inf) = beta(aa,bb)/(cc^aa*d^bb*r).
      // Compute this, and then differentiate it m times to get the log
      // term incorporated.
      if kk.truthy() {
        let aa = div(add2(Fix(1L), ivar), r)
        let bb = sub(s, aa)
        let m : Value = if eq(d_asksign(m.val), q_d_zero) { Fix(0L) } else { m.val }
        let res = div(
          mk(q_p_beta, [aa, bb]),
          mul3(power(cc, aa), power(d, bb), r),
        )
        d_at(d_diff(list3(res, ivar, m)), list3(list1(q_mequal), ivar, kk))
      } else {
        Nil
      }
    } else {
      let (k_sln, l, n, b) = batap_new(e, ivar, ul)
      if k_sln.truthy() {
        let beta = ftake_star(q_p_beta, [k_sln, l])
        let m : Value = if eq(d_asksign(m.val), q_d_zero) { Fix(0L) } else { m.val }
        // The result looks like B(k/n,l) ( ... ).  Perhaps, we should
        // just $factor, instead of pulling out beta like this.
        mul2(
          beta,
          d_fullratsimp(
            div(
              muln_([
                power(neg(b), add2(Fix(-1L), l)),
                power(ul, mul2(n, add2(Fix(-1L), l))),
                power(n, neg(add2(Fix(1L), m))),
                d_at(
                  d_diff(
                    list3(
                      mul2(power(ul, mul2(n, ivar)), list3(list1(q_p_beta), ivar, l)),
                      ivar,
                      m,
                    ),
                  ),
                  list3(list1(q_mequal), ivar, k_sln),
                ),
              ]),
              beta,
            ),
            Nil,
          ),
        )
      } else {
        Nil
      }
    }
  } else {
    Nil
  }
}

///|
/// If e is of the form given below, make the obvious change of variables
/// (substituting ul*x^(1/n) for x) in order to reduce e to the usual form
/// of the integrand in the Eulerian integral of the first kind.
fn batap_new(e : Value, ivar : Value, ul : Value) -> (Value, Value, Value, Value) raise {
  // Parse e
  let (k, c) = bata0(e, ivar)
  if k.truthy() {
    // e=x^k*(a+b*x^n)^l
    let mut k = k
    let mut l = nth(0, c)
    let a = nth(1, c)
    let n = nth(2, c)
    let b = nth(3, c)
    if freeof(ivar, k).truthy() &&
      freeof(ivar, n).truthy() &&
      freeof(ivar, l).truthy() &&
      alike1(a, neg(mul2(b, power(ul, n)))).truthy() &&
      eq(d_asksign(b), q_d_neg) &&
      eq(
        d_asksign({
          k = add2(Fix(1L), k)
          k
        }),
        q_d_pos,
      ) &&
      eq(
        d_asksign({
          l = add2(Fix(1L), l)
          l
        }),
        q_d_pos,
      ) &&
      eq(d_asksign(n), q_d_pos) {
      return (div(k, n), l, n, b)
    }
  }
  (Nil, Nil, Nil, Nil)
}

///|
/// Wang p. 71 gives the following formula for a beta function:
///
/// integrate(x^(k-1)/(c*x^r+d)^s,x,0,inf)
///   = beta(a,b)/(c^a*d^b*r)
///
/// where a = k/r > 0, b = s - a > 0, s > k > 0, r > 0, c*d > 0.
///
/// This function matches this and returns k-1, d, r, c, a, b.  And also
/// checks that all the conditions hold.  If not, NIL is returned.
fn batap_inf(e : Value, ivar : Value) -> (Value, Value, Value, Value, Value) raise {
  let (k, c) = bata0(e, ivar)
  if k.truthy() {
    let l = nth(0, c)
    let d = nth(1, c)
    let r = nth(2, c)
    let cc = nth(3, c)
    let s = mul2(Fix(-1L), l)
    let kk = add2(k, Fix(1L))
    let a = div(kk, r)
    let b = sub(s, a)
    if freeof(ivar, k).truthy() &&
      freeof(ivar, r).truthy() &&
      freeof(ivar, l).truthy() &&
      eq(d_asksign(kk), q_d_pos) &&
      eq(d_asksign(a), q_d_pos) &&
      eq(d_asksign(b), q_d_pos) &&
      eq(d_asksign(sub(s, k)), q_d_pos) &&
      eq(d_asksign(r), q_d_pos) &&
      eq(d_asksign(mul2(cc, d)), q_d_pos) {
      return (k, s, d, r, cc)
    }
  }
  (Nil, Nil, Nil, Nil, Nil)
}

///|
/// Handles beta integrals.
fn batapp(e : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  if !eq(ul, q_d_inf) {
    lisp_error("The assertion (EQ UL '$INF) failed.") |> ignore
  }
  let mut e = e
  if !(equal(ll, Fix(0L)) || eq(ll, q_d_minf)) {
    e = subin_var(add2_star(ll, ivar), e, ivar)
  }
  let (k, c) = bata0(e, ivar)
  if k is Nil {
    Nil
  } else {
    let mut l = nth(0, c)
    let d = nth(1, c)
    let al = nth(2, c)
    let c = nth(3, c)
    // e = x^k*(d+c*x^al)^l.
    let new_k = div_star(add2_star(Fix(1L), k), al)
    if ratgreaterp(al, Fix(0L)).truthy() &&
      eq(d_asksign(new_k), q_d_pos) &&
      ratgreaterp(
        {
          l = mul2_star(Fix(-1L), l)
          l
        },
        new_k,
      ).truthy() &&
      eq(d_asksign(mul2_star(d, c)), q_d_pos) {
      l = add2_star(l, mul2(Fix(-1L), new_k))
      div_star(
        mk(q_p_beta, [new_k, l]),
        muln_star([al, power_star(c, new_k), power_star(d, l)]),
      )
    } else {
      Nil
    }
  }
}

///|
/// Compute exp(d)*gamma((c+1)/b)/b/a^((c+1)/b).  In essence, this is the
/// value of integrate(x^c*exp(d-a*x^b),x,0,inf).
fn gamma1(c : Value, a : Value, b : Value, d : Value) -> Value raise {
  let e1 = power(q_d__pcte, d)
  let c = div_star(add2(c, Fix(1L)), b)
  let e2 = power_star(mul2_star(b, power_star(a, c)), Fix(-1L))
  muln_star([e1, e2, mk(q_p_gamma, [c])])
}

///|
fn zto_pctpi2(grand : Value, ivar : Value) -> Value raise {
  let result = unitcir(sratsimp(div_star(grand, ivar)), ivar)
  if result.truthy() {
    sratsimp(mul2_star(defint__mneg(q_d__pcti), result))
  } else {
    Nil
  }
}

///|
/// Evaluates the contour integral of GRAND around the unit circle using
/// residues.
fn unitcir(grand : Value, ivar : Value) -> Value raise {
  let (nn, dn) = numden_var(grand, ivar)
  let sgn : Ref[Value] = Ref(Nil)
  let result = princip(
    res_var(
      ivar,
      nn,
      dn,
      lfunc("unitcir-region", args => {
        let pt = arg(args, 0)
        // Is pt stricly inside the unit circle?
        sgn.val = with_special(q_limitp, Nil, fn() {
          d_asksign(add2_star(Fix(-1L), cabs(pt)))
        })
        lbool(eq(sgn.val, q_d_neg))
      }),
      lfunc("unitcir-region1", _ => {
        // Is pt on the unit circle?  (Use the cached value computed
        // above.)
        let v = lbool(eq(sgn.val, q_d_zero))
        sgn.val = Nil
        v
      }),
    ),
  )
  if result.truthy() {
    mul2_star(q_d__pctpi, result)
  } else {
    Nil
  }
}

///|
fn logx1(exp_ : Value, ll : Value, ul : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  if eq(ivar, q_yx) {
    return Nil // new ivar cannot be same as old ivar
  }
  if notinvolve_var(
      defint__exp(),
      ivar,
      list([q_p_sin, q_p_cos, q_p_tan, q_p_atan, q_p_asin, q_p_acos]),
    ).truthy() {
    let arg = involve_var(defint__exp(), ivar, list1(q_p_log))
    if arg.truthy() {
      if eq(arg, ivar) {
        if ratgreaterp(Fix(1L), ll).truthy() {
          if !eq(ul, q_d_inf) {
            intcv1(
              power(q_d__pcte, defint__mneg(q_yx)),
              defint__mneg(mk(q_p_log, [ivar])),
              ivar,
              ll,
              ul,
            )
          } else {
            intcv1(power(q_d__pcte, q_yx), mk(q_p_log, [ivar]), ivar, ll, ul)
          }
        } else {
          Nil
        }
      } else {
        intcv(arg, Nil, ivar, ll, ul)
      }
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// Wang 81-83.  integrate(cos(k*t^n),t,0,inf) = G * cos(%pi/2/n) and
/// integrate(sin(k*t^n),t,0,inf) = G * sin(%pi/2/n) where
/// G = gamma(1/n)/k^(1/n)/n (from a contour integral of exp(%i*k*t^n)
/// over a sector of angle %pi/(2*n)).
fn scaxn(e : Value, ivar : Value) -> Value raise {
  if atom(e) {
    return Nil
  }
  let mut e = e
  let mut ind : Value = Nil
  if (eq(caar(e), q_p_sin) || eq(caar(e), q_p_cos)) &&
    {
      ind = caar(e)
      ind.truthy()
    } &&
    {
      e = bx_star_starn(cadr(e), ivar)
      e.truthy()
    } {
    // Ok, we have cos(b*x^n) or sin(b*x^n), and we set e = (n b)
    if equal(car(e), Fix(1L)) {
      // n = 1.  Give up.  (Why not divergent?)
      return Nil
    }
    let sign = d_asksign(cadr(e))
    let s : Value = if eq(sign, q_d_pos) {
      Fix(1L)
    } else if eq(sign, q_d_neg) {
      Fix(-1L)
    } else if eq(sign, q_d_zero) {
      Fix(0L)
    } else {
      Nil
    }
    if zerop(s) {
      // s is the sign of b.  Give up if it's zero.
      Nil
    } else if !eq(d_asksign(add2_star(Fix(-1L), car(e))), q_d_pos) {
      // Give up if n-1 <= 0.  (Why give up?  Isn't the integral
      // divergent?)
      Nil
    } else {
      // We can apply our formula now.  g = gamma(1/n)/n/b^(1/n)
      let g = gamma1(Fix(0L), mul2_star(s, cadr(e)), car(e), Fix(0L))
      e = mul2_star(g, mk(ind, [div_star(symval(q_half_pctpi), car(e))]))
      mul2_star(
        if eq(ind, q_p_sin) && equal(s, Fix(-1L)) {
          Fix(-1L)
        } else {
          Fix(1L)
        },
        e,
      )
    }
  } else {
    Nil
  }
}

// this is the second part of the definite integral package

///|
fn p_starlognxp(a : Value, s : Value, ivar : Value) -> Value raise {
  if !among(q_p_log, a).truthy() {
    return Nil
  }
  let b = maxima_substitute(Fix(1L), mk(q_p_log, [ivar]), a)
  if polyinx(b, ivar, t).truthy() &&
    eq(
      d_sign(add2_star(s, defint__mneg(add2_star(Fix(1L), deg_var(b, ivar))))),
      q_d_pos,
    ) &&
    evenfn(b, ivar).truthy() {
    let a = lognxp(sratsimp(div_star(a, b)), ivar)
    if a.truthy() {
      return list2(b, a)
    }
  }
  Nil
}

///|
fn lognxp(a : Value, ivar : Value) -> Value raise {
  if atom(a) {
    Nil
  } else if eq(caar(a), q_p_log) && eq(cadr(a), ivar) {
    Fix(1L)
  } else if mexptp(a).truthy() &&
    numberp(caddr(a)) &&
    lognxp(cadr(a), ivar).truthy() {
    caddr(a)
  } else {
    Nil
  }
}

///|
fn logcpi0(
  n : Value,
  d : Value,
  ivar : Value,
) -> (Value, Value, Value, Value, Value, Value, Value) raise {
  let mut polelist = polelist_var(
    ivar,
    d,
    lfunc("upperhalf", args => upperhalf(arg(args, 0))),
    lfunc("logcpi0-region1", args => {
      let j = arg(args, 0)
      if zerop1(j).truthy() {
        Nil
      } else if equal(d_imagpart(j), Fix(0L)) {
        t
      } else {
        Nil
      }
    }),
  )
  if polelist is Nil {
    return (Nil, Nil, Nil, Nil, Nil, Nil, Nil)
  }
  let factors = car(polelist)
  polelist = cdr(polelist)
  let mut dp : Value = Nil
  if cadr(polelist).truthy() || caddr(polelist).truthy() {
    dp = sdiff(d, ivar)
  }
  let plm = car(polelist)
  let mut rlm : Value = Nil
  if plm.truthy() {
    rlm = residue_var(
      ivar,
      n,
      if symval(q_ear_leadcoef).truthy() {
        factors
      } else {
        d
      },
      plm,
    )
  }
  let pl = cadr(polelist)
  let mut rl : Value = Nil
  if pl.truthy() {
    rl = res1_var(ivar, n, dp, pl)
  }
  let pl1 = caddr(polelist)
  let mut rl1 : Value = Nil
  if pl1.truthy() {
    rl1 = res1_var(ivar, n, dp, pl1)
  }
  let v = mul2(
    div(Fix(1L), Fix(2L)),
    mul2(
      q_d__pctpi,
      princip(
        list2(
          if set(q_nn_star, append(rl, rlm)).truthy() {
            addn(symval(q_nn_star), Nil)
          } else {
            Nil
          },
          if rl1.truthy() {
            addn(rl1, Nil)
          } else {
            Nil
          },
        ),
      ),
    ),
  )
  (v, plm, factors, pl, rl, pl1, rl1)
}

///|
fn lognx2(nn : Value, dn : Value, pl : Value, rl : Value) -> Value raise {
  let mut pl = pl
  let mut rl = rl
  let mut ans : Value = Nil
  while !(pl is Nil || rl is Nil) {
    // AFAICT, this call to PLOG doesn't need to bind VAR.
    ans = cons(
      muln_star([dn, car(rl), power_star(mk(q_p_plog, [car(pl)]), nn)]),
      ans,
    )
    pl = cdr(pl)
    rl = cdr(rl)
  }
  ans
}

///|
fn logcpj(
  n : Value,
  d : Value,
  i : Value,
  ivar : Value,
  plm : Value,
  pl : Value,
  rl : Value,
  pl1 : Value,
  rl1 : Value,
) -> Value raise {
  let pi2 = symval(q_p_pi2)
  let first = if plm.truthy() {
    // AFAICT, this call to PLOG doesn't need to bind VAR.  An example
    // where this is used is integrate(log(x)^2/(1+x^2),x,0,1) =
    // %pi^3/16.
    list1(
      mul2_star(
        mul2(q_d__pcti, pi2),
        addn(
          residue_var(
            ivar,
            mul2_star(power_star(mk(q_p_plog, [ivar]), i), n),
            d,
            plm,
          ),
          Nil,
        ),
      ),
    )
  } else {
    Nil
  }
  let second = lognx2(i, mul2(q_d__pcti, pi2), pl, rl)
  let third = lognx2(i, symval(q_p_p_pcti), pl1, rl1)
  let n = append(first, append(second, third))
  if n is Nil {
    Fix(0L)
  } else {
    simplify(addn(n, Nil))
  }
}

///|
/// Handle integral(n(x)/d(x)*log(x)^m,x,0,inf).  n and d are
/// polynomials.
fn log_starrat(n : Value, d : Value, m : Value, ivar : Value) -> Value raise {
  let mm = to_int(m)
  let i_vals : Array[Value] = Array::make(mm + 1, Fix(0L))
  let j_vals : Array[Value] = Array::make(mm + 1, Fix(0L))
  fn sumi(c : Int) -> Value raise {
    let mut ans : Value = Nil
    let mut k = 1
    while k != c {
      ans = cons(
        muln_star([
          d_makegamma(mk(q_p_binomial, [int(c), int(k)])),
          power(q_d__pctpi, int(k)),
          power(q_d__pcti, int(k)),
          i_vals[c - k],
        ]),
        ans,
      )
      k = k + 1
    }
    addn(ans, Nil)
  }
  fn logcpi(
    n : Value,
    d : Value,
    c : Int,
    ivar : Value,
  ) -> (Value, Value, Value, Value, Value, Value, Value) raise {
    if c == 0 {
      logcpi0(n, d, ivar)
    } else {
      (
        mul2_star(
          defint__rat(1L, 2L),
          add2_star(j_vals[c], mul2_star(Fix(-1L), sumi(c))),
        ),
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
      )
    }
  }
  j_vals[0] = Fix(0L)
  let b0 = bind(q_ear_leadcoef, Nil)
  defer unbind(b0)
  for c in 0..<mm {
    let (res, plm, factors, pl, rl, pl1, rl1) = logcpi(n, d, c, ivar)
    i_vals[c] = res
    j_vals[c] = logcpj(n, factors, int(c), ivar, plm, pl, rl, pl1, rl1)
  }
  logcpi(n, d, mm, ivar).0
}

///|
fn fan(p : Value, m : Value, a : Value, n : Value, b : Value) -> Value raise {
  let povern = div_star(p, n)
  let ab = div_star(a, b)
  if eq(ask_integer(povern, q_d_integer), q_d_yes) ||
    !equal(d_imagpart(ab), Fix(0L)) {
    Nil
  } else {
    let ind = d_asksign(ab)
    if eq(ind, q_d_zero) {
      Nil
    } else if eq(ind, q_d_neg) {
      Nil
    } else if !ratgreaterp(m, povern).truthy() {
      Nil
    } else {
      div_star(
        muln_star([
          q_d__pctpi,
          d_makegamma(
            mk(q_p_binomial, [
              addn_star([Fix(-1L), m, defint__mneg(povern)]),
              add2(Fix(-1L), m),
            ]),
          ),
          mk(q_mabs, [
            power_star(a, add2_star(povern, defint__mneg(m))),
          ]),
        ]),
        muln_star([
          power_star(b, povern),
          n,
          mk(q_p_sin, [mul2(q_d__pctpi, povern)]),
        ]),
      )
    }
  }
}

///|
/// Makes a new poly such that np(x)-np(x+2*%i*%pi)=p(x).  Constructs
/// general POLY of degree one higher than P with arbitrary coeff. and
/// then solves for coeffs by equating like powers of the varibale of
/// integration.  Can probably be made simpler now.
fn makpoly(p : Value, ivar : Value) -> Value raise {
  let n = deg_var(p, ivar)
  let b0 = bind(q_varlist, Nil)
  defer unbind(b0)
  // Make poly with gensyms of 1 higher deg.
  let mut ans = genpoly(add2_star(Fix(1L), n), ivar)
  let cl = cdr(ans) // Coefficient list
  set(q_varlist, append(cl, list1(ivar))) |> ignore // Make VAR most important.
  let gp = car(ans) // This is the poly with gensym coeffs.
  // Now, poly(x)-poly(x+2*%i*%pi)=p(x), P is the original poly.
  ans = addn_star([
    gp,
    subin_var(
      add2(mul2(q_d__pcti, symval(q_p_pi2)), ivar),
      defint__mneg(gp),
      ivar,
    ),
    defint__mneg(p),
  ])
  newvar(ans) |> ignore
  ans = ratrep_star(ans) // Rational rep with VAR leading.
  let zz = coefsolve(
    n,
    cl,
    if !eq(caadr(ans), genfind(car(ans), ivar)) {
      // What is Lead Var.
      list2(Fix(0L), cadr(ans)) // No VAR in ans.
    } else {
      cdadr(ans) // The real Poly.
    },
  )
  if zz is Nil || gp is Nil {
    Fix(-1L)
  } else {
    d_substitute(zz, gp) // Substitute Values for gensyms.
  }
}

///|
fn coefsolve(n : Value, cl : Value, e : Value) -> Value raise {
  let b0 = bind(q_d_breakup, Nil)
  defer unbind(b0)
  let mut eql = list1(pdis(ptterm(e, n)))
  let mut m = add2_star(n, Fix(-1L))
  while !(numberp(m) && num_lt(m, Fix(0L))) {
    let new_eql = cons(pdis(ptterm(e, m)), eql)
    let new_m = add2_star(m, Fix(-1L))
    eql = new_eql
    m = new_m
  }
  solvex(eql, cl, Nil, Nil)
}

///|
/// Integrate(p(x)*f(exp(x))/g(exp(x)),x,minf,inf) by applying the
/// transformation y = exp(x) to get
/// integrate(p(log(y))*f(y)/g(y)/y,y,0,inf).  This should be handled by
/// dintlog.
fn log_transform(p : Value, pe : Value, d : Value, ivar : Value, ul : Value) -> Value raise {
  let new_p = subst(list2(list1(q_p_log), ivar), ivar, p)
  let new_pe = subst(ivar, q_z_star, defint__catch_pin(pe, ivar))
  let new_d = subst(ivar, q_z_star, defint__catch_pin(d, ivar))
  defint(div(div(mul2(new_p, new_pe), new_d), ivar), ivar, Fix(0L), ul)
}

///|
/// This implements Wang's algorithm in Chapter 5.2, pp. 98-100.
///
/// We have integrate(R(exp(x))*p(x),x,minf,inf), where R(x) is a
/// rational function and p(x) is a polynomial.
///
/// We find a polynomial q(x) such that q(x) - q(x+2*%i*%pi) = p(x).
/// Then consider a contour integral of R(exp(z))*q(z) over a rectangular
/// contour.  Opposite corners of the rectangle are (-R, 2*%i*%pi) and
/// (R, 0).
///
/// Wang shows that this contour integral, in the limit, is the integral
/// of R(exp(x))*q(x)-R(exp(x))*q(x+2*%i*%pi), which is exactly the
/// integral we're looking for.
///
/// Thus, to find the value of the contour integral, we just need the
/// residues of R(exp(z))*q(z).  The only tricky part is that we want the
/// log function to have an imaginary part between 0 and 2*%pi instead of
/// -%pi to %pi.
fn rectzto_pctpi2(p : Value, pe : Value, d : Value, ivar : Value) -> Value raise {
  // We have R(exp(x))*p(x) represented as p(x)*pe(exp(x))/d(exp(x)).
  let denom_exponential = defint__catch_pin(d, ivar)
  if !(
      denom_exponential.truthy() &&
      p_e_integer_coeff(pe, ivar).truthy() &&
      p_e_integer_coeff(d, ivar).truthy()
    ) {
    return Nil
  }
  let pi2 = symval(q_p_pi2)
  // At this point denom-exponential has converted d(exp(x)) to the
  // polynomial d(z), where z = exp(x).
  let n = mul2_star(
    if p is Nil {
      Fix(-1L)
    } else {
      d_expand(muln_([q_d__pcti, pi2, makpoly(p, ivar)]))
    },
    pe,
  )
  // Find the poles of the denominator.  denom-exponential is the
  // denominator of R(x).
  //
  // It seems as if polelist returns a list of several items.  The first
  // element is a list consisting of the pole and (z - pole).  We don't
  // care about this, so we take the rest of the result.
  let pl = with_special(q_ear_leadcoef, Nil, fn() {
    cdr(
      polelist_var(
        q_z_star,
        denom_exponential,
        lfunc("rectzto%pi2-region", args => {
          let j = arg(args, 0)
          // The imaginary part is nonzero, or the realpart is negative.
          lbool(
            !equal(d_imagpart(j), Fix(0L)) ||
            eq(d_asksign(d_realpart(j)), q_d_neg),
          )
        }),
        lfunc("rectzto%pi2-region1", args => {
          let j = arg(args, 0)
          // The realpart is not zero.
          lbool(!eq(d_asksign(d_realpart(j)), q_d_zero))
        }),
      ),
    )
  })
  let mut dp : Value = Nil
  // Not sure what this does.
  if pl is Nil {
    // No roots at all, so return
    return Nil
  } else if cadr(pl).truthy() || caddr(pl).truthy() {
    // We have simple roots or roots in REGION1
    dp = sdiff(d, ivar)
  }
  let b = if cadr(pl).truthy() {
    // The cadr of pl is the list of the simple poles of
    // denom-exponential.  Take the log of them to find the poles of the
    // original expression.  Then compute the residues at each of these
    // poles and sum them up and put the result in B.  (If no simple
    // poles set B to 0.)
    let b = mapcar(x => log_imag_0_2_pctpi(x), cadr(pl))
    let b = res1_var(ivar, n, dp, b)
    addn(b, Nil)
  } else {
    Fix(0L)
  }
  let c = if caddr(pl).truthy() {
    // I think this handles the case of poles outside the regions.  The
    // sum of these residues are placed in C.
    let temp = mapcar(x => log_imag_0_2_pctpi(x), caddr(pl))
    let c = append(temp, mapcar(j => add2_star(mul2(q_d__pcti, pi2), j), temp))
    let c = res1_var(ivar, n, dp, c)
    addn(c, Nil)
  } else {
    Fix(0L)
  }
  let a = if car(pl).truthy() {
    // We have the repeated poles of deonom-exponential, so we need to
    // convert them to the actual pole values for R(exp(x)), by taking
    // the log of the value of poles.
    let poles = mapcar(p => log_imag_0_2_pctpi(car(p)), car(pl))
    let b_exp = bind(
      q_exp,
      div_star(n, subst(power(q_d__pcte, ivar), q_z_star, denom_exponential)),
    )
    defer unbind(b_exp)
    // Compute the residues at all of these poles and sum them up.
    let a = mapcar(j => d_residue(defint__exp(), ivar, j), poles)
    addn(a, Nil)
  } else {
    Fix(0L)
  }
  sratsimp(addn_star([a, b, mul2_star(defint__rat(1L, 2L), c)]))
}

///|
fn genpoly(i : Value, ivar : Value) -> Value raise {
  let mut i = i
  let mut c = gensym()
  let mut cl : Value = Nil
  let mut ans : Value = Nil
  while !zerop(i) {
    ans = cons(mul2_star(c, power(ivar, i)), ans)
    cl = cons(c, cl)
    i = add2_star(i, Fix(-1L))
    c = gensym()
  }
  cons(addn(ans, Nil), cl)
}

///|
/// Check to see if each term in exp that is of the form exp(k*x) has an
/// integer value for k.
fn p_e_integer_coeff(exp_ : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let e = defint__exp()
  if mapatom(e).truthy() {
    t
  } else if mexptp(e).truthy() && eq(cadr(e), q_d__pcte) {
    lbool(eq(ask_integer(d_coeff(caddr(e), ivar), q_d_integer), q_d_yes))
  } else {
    lbool(every(x => p_e_integer_coeff(x, ivar).truthy(), cdr(e)))
  }
}

///|
fn wlinearpoly(e : Value, ivar : Value) -> Value raise {
  let e = polyinx(e, ivar, t)
  if e.truthy() && equal(deg_var(e, ivar), Fix(1L)) {
    subin_var(Fix(1L), e, ivar)
  } else {
    Nil
  }
}

///|
/// Test to see if exp is of the form f(exp(x)), and if so, replace
/// exp(x) with 'z*.  That is, basically return f(z*).
fn pin_pctex(exp_ : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  pin_pctex0(
    if notinvolve_var(
        defint__exp(),
        ivar,
        list([q_p_sinh, q_p_cosh, q_p_tanh]),
      ).truthy() {
      defint__exp()
    } else {
      with_special(q_d_exponentialize, t, fn() {
        set(q_exp, d_expand(defint__exp()))
      })
    },
    ivar,
  )
}

///|
fn pin_pctex0(e : Value, ivar : Value) -> Value raise {
  if !among(ivar, e).truthy() {
    e
  } else if atom(e) {
    throw_tag(q_pin_pctex, Nil)
  } else if mexptp(e).truthy() && eq(cadr(e), q_d__pcte) {
    if eq(caddr(e), ivar) {
      q_z_star
    } else {
      let linterm = wlinearpoly(caddr(e), ivar)
      let v = if linterm.truthy() {
        mul2_star(subin_var(Fix(0L), e, ivar), power(q_z_star, linterm))
      } else {
        Nil
      }
      if v.truthy() {
        v
      } else {
        throw_tag(q_pin_pctex, Nil)
      }
    }
  } else if mtimesp(e).truthy() {
    muln(mapcar(ee => pin_pctex0(ee, ivar), cdr(e)), Nil)
  } else if mplusp(e).truthy() {
    addn(mapcar(ee => pin_pctex0(ee, ivar), cdr(e)), Nil)
  } else {
    throw_tag(q_pin_pctex, Nil)
  }
}

///|
fn findsub(p : Value, ivar : Value) -> Value raise {
  if findp(p, ivar).truthy() {
    return Nil
  }
  let nd = bx_star_starn(p, ivar)
  if nd.truthy() {
    return power(ivar, car(nd))
  }
  let p = bx_star_starn_plusa(p, ivar)
  if p.truthy() {
    mul2_star(caddr(p), power(ivar, cadr(p)))
  } else {
    Nil
  }
}

///|
/// I think this is looking at f(exp(x)) and tries to find some rational
/// function R and some number k such that f(exp(x)) = R(exp(k*x)).
fn funclogor_pcte(e : Value, ivar : Value) -> Value raise {
  let mut arg : Value = Nil
  let mut r : Value = Nil
  if ratp(e, ivar).truthy() ||
    involve_var(e, ivar, list([q_p_sin, q_p_cos, q_p_tan])).truthy() ||
    {
      let a = {
        arg = involve_var(e, ivar, list1(q_p_log))
        if arg.truthy() {
          r = q_p_log
          r
        } else {
          Nil
        }
      }
      arg = xor(a, p_einvolve_var(e, ivar))
      !arg.truthy()
    } {
    return Nil
  }
  while true {
    // ag
    let nvar = if eq(r, q_p_log) {
      mk(q_p_log, [arg])
    } else {
      power(q_d__pcte, arg)
    }
    let ans = maxima_substitute(
      power(q_yx, Fix(-1L)),
      power(nvar, Fix(-1L)),
      maxima_substitute(q_yx, nvar, e),
    )
    if !among(ivar, ans).truthy() {
      return list2(subst(ivar, q_yx, ans), nvar)
    } else if r is Nil &&
      {
        arg = findsub(arg, ivar)
        arg.truthy()
      } {
      continue
    } else {
      return Nil
    }
  }
  Nil
}

///|
/// Integration by parts.
///
/// integrate(u(x)*diff(v(x),x),x,a,b)
///              |b
///   = u(x)*v(x)| - integrate(v(x)*diff(u(x),x))
///              |a
fn dintbypart(u : Value, v : Value, a : Value, b : Value, ivar : Value) -> Value raise {
  // SINCE ONLY CALLED FROM DINTLOG TO get RID OF LOGS - IF LOG REMAINS,
  // QUIT
  let ad = antideriv(v, ivar)
  if ad is Nil || involve_var(ad, ivar, list1(q_p_log)).truthy() {
    Nil
  } else {
    let p1 = mul2_star(u, ad)
    let p2 = mul2_star(ad, sdiff(u, ivar))
    let p1_part1 = get_limit(p1, ivar, b, dir=q_d_minus)
    let p1_part2 = get_limit(p1, ivar, a, dir=q_d_plus)
    if p1_part1 is Nil || p1_part2 is Nil {
      Nil
    } else {
      let p2 = defint(p2, ivar, a, b)
      if p2.truthy() {
        addn_star([p1_part1, defint__mneg(p1_part2), defint__mneg(p2)])
      } else {
        Nil
      }
    }
  }
}

///|
/// integrate(f(exp(k*x)),x,a,b), where f(z) is rational.
///
/// See Wang p. 96-97.
///
/// If the limits are minf to inf, we use the substitution y=exp(k*x) to
/// get integrate(f(y)/y,y,0,inf)/k.  If the limits are 0 to inf, use the
/// substitution s+1=exp(k*x) to get integrate(f(s+1)/(s+1),s,0,inf).
fn dintexp(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let b0 = bind(q_ear_dintexp_recur, t) // recursion stopper
  defer unbind(b0)
  let mut ans : Value = Nil
  if sinintp(defint__exp(), ivar).truthy() && // To be moved higher in the code.
    {
      ans = antideriv(defint__exp(), ivar)
      ans.truthy()
    } &&
    {
      ans = intsubs(ans, ll, ul, ivar)
      ans.truthy()
    } {
    // If we can integrate it directly, do so and take the appropriate
    // limits. INTSUBS builds the difference of two endpoint limits
    // without simplifying across it, so the parts that cancel have to be
    // brought together here.
    ans = d_expand(ans)
    ans
  } else {
    ans = funclogor_pcte(defint__exp(), ivar)
    if ans.truthy() {
      // ans is the list (f(x) exp(k*x)).
      if equal(ll, Fix(0L)) && eq(ul, q_d_inf) {
        // Use the substitution s + 1 = exp(k*x).  The integral becomes
        // integrate(f(s+1)/(s+1),s,0,inf)
        ans = add2(Fix(-1L), cadr(ans))
      } else {
        // Use the substitution y=exp(k*x) because the limits are minf to
        // inf.
        ans = cadr(ans)
      }
      // Apply the substitution and integrate it.  Skip nested radicals
      // (last argument T), since such integrals are never solved, but
      // instead take much time to return a noun form or exhaust the heap
      // (bug #5665).
      intcv(ans, Nil, ivar, ll, ul, skip_nested=t)
    } else {
      Nil
    }
  }
}

///|
/// integrate(log(g(x))*f(x),x,0,inf)
fn dintlog(exp_ : Value, arg : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  // recursion stopper
  let b0 = bind(q_ear_dintlog_recur, one_plus(symval(q_ear_dintlog_recur)))
  defer unbind(b0)
  if eq(ul, q_d_inf) &&
    equal(ll, Fix(0L)) &&
    eq(arg, ivar) &&
    equal(
      Fix(1L),
      sratsimp(
        div_star(
          defint__exp(),
          mul2_star(
            defint__mneg(
              subin_var(power(ivar, Fix(-1L)), defint__exp(), ivar),
            ),
            power(ivar, Fix(-2L)),
          ),
        ),
      ),
    ) {
    // Make the substitution y=1/x.  If the integrand has exactly the same
    // form, the answer has to be 0.
    return Fix(0L)
  }
  let mut ans = with_special(q_d_gamma_expand, t, fn() {
    logx1(defint__exp(), ll, ul, ivar)
  })
  if ans.truthy() && free(ans, q_p_limit).truthy() {
    return ans
  }
  ans = antideriv(defint__exp(), ivar)
  if ans.truthy() {
    // It's easy if we have the antiderivative.  but intsubs sometimes
    // gives results containing %limit
    return intsubs(ans, ll, ul, ivar)
  }
  // Ok, the easy cases didn't work.  We now try integration by parts.
  // Set ANS to f(x).
  ans = div_star(defint__exp(), mk(q_p_log, [arg]))
  if involve_var(ans, ivar, list1(q_p_log)).truthy() {
    // Bad. f(x) contains a log term, so we give up.
    return Nil
  }
  if eq(arg, ivar) && equal(Fix(0L), no_err_sub_var(Fix(0L), ans, ivar)) {
    let d = defint(mul2_star(ans, power(ivar, q_ear_z)), ivar, ll, ul)
    if d.truthy() {
      // The arg of the log function is the same as the integration
      // variable.  We can do something a little simpler than integration
      // by parts.  We have something like f(x)*log(x).  Consider
      // f(x)*x^z.  If we differentiate this wrt to z, the integrand
      // becomes f(x)*log(x)*x^z.  When we evaluate this at z = 0, we get
      // the desired integrand.
      //
      // So we need f(0) to be 0 at 0.  If we can integrate f(x)*x^z,
      // then we differentiate the result and evaluate it at z = 0.
      return derivat(q_ear_z, Fix(1L), d, Fix(0L))
    }
  }
  ans = dintbypart(mk(q_p_log, [arg]), ans, ll, ul, ivar)
  if ans.truthy() {
    // Try integration by parts.
    return ans
  }
  Nil
}

///|
/// Compute diff(e,ivar,n) at the point pt.
fn derivat(ivar : Value, n : Value, e : Value, pt : Value) -> Value raise {
  subin_var(pt, d_diff(list3(e, ivar, n)), ivar)
}

// GGR and friends

///|
/// MAYBPC returns (COEF EXPO CONST)
///
/// This basically picks off b*x^n+a and returns the list (b n a).
fn maybpc(e : Value, ivar : Value, nd_var : Value) -> (Value, Value) raise {
  let mut ivar = ivar
  if symval(q_ear_mtoinf).truthy() {
    throw_tag(q_ggrm, linpower0(e, ivar)) |> ignore
    return (Nil, Nil)
  }
  let e = bx_star_starn_plusa(e, ivar) // bx**n+a --> (a n b) or nil.
  if e is Nil {
    // with ivar being x.
    return (Nil, Nil)
  }
  // At this point, e is of the form (a n b)
  let mut zn : Value = Nil
  if among(q_d__pcti, caddr(e)).truthy() &&
    zerop1(d_realpart(caddr(e))).truthy() &&
    {
      zn = d_imagpart(caddr(e))
      zn.truthy()
    } &&
    eq(d_asksign(cadr(e)), q_d_pos) {
    // If we're here, b is complex, and n > 0.  zn = imagpart(b).
    //
    // Set ivar to the same sign as zn.
    if eq(d_asksign(zn), q_d_neg) {
      ivar = Fix(-1L)
      zn = defint__mneg(zn)
    } else {
      ivar = Fix(1L)
    }
    // zd = exp(ivar*%i*%pi*(1+nd)/(2*n). (ZD is special!)
    let zd = power(
      q_d__pcte,
      div_star(
        muln_star([ivar, q_d__pcti, q_d__pctpi, add2(Fix(1L), nd_var)]),
        mul2(Fix(2L), cadr(e)),
      ),
    )
    // Return zn, n, a, zd.
    return (list3(caddr(e), cadr(e), car(e)), zd)
  }
  if (
      {
        ivar = d_asksign(d_realpart(caddr(e)))
        eq(ivar, q_d_neg)
      } ||
      equal(ivar, q_d_zero)
    ) &&
    equal(d_imagpart(cadr(e)), Fix(0L)) &&
    ratgreaterp(cadr(e), Fix(0L)).truthy() {
    // We're here if realpart(b) <= 0, and n >= 0.  Then return -b, n, a.
    return (list3(caddr(e), cadr(e), car(e)), Nil)
  }
  (Nil, Nil)
}

///|
/// Integrate x^m*exp(b*x^n+a), with realpart(m) > -1.
///
/// See Wang, pp. 84-85.
///
/// I believe the formula Wang gives is incorrect.  The derivation is
/// correct except for the last step.  The result is
/// gamma((m+1)/n)/k^((m+1)/n)/n, which also handles
/// integrate(x^m*exp(-k*x^n),x,0,inf) for positive real k.
fn ggr(e : Value, ind : Value, ivar : Value) -> Value raise {
  let bs = bind_all([
    (q_nn_star, Nil),
    (q_dn_star, Nil),
    (q_dosimp, Nil),
    (q_d__pctemode, Nil),
  ])
  defer unbind_all(bs)
  let mut e = e
  let nd_var : Value = Fix(0L)
  if ind.truthy() {
    e = d_expand(e)
    if mplusp(e).truthy() &&
      {
        e = with_special(q_ear_nodiverg, t, fn() {
          defint__catch_divergent(fn() {
            defint__andmapcar(j => ggr(j, Nil, ivar), cdr(e))
          })
        })
        e.truthy()
      } {
      if eq(e, q_divergent) {
        ()
      } else {
        return sratsimp(cons(list1(q_mplus), e))
      }
    }
  }
  e = rmconst1(e, ivar)
  let c = car(e)
  e = cdr(e)
  let (e1, zd) = ggr1(e, ivar, nd_var)
  e = e1
  if e.truthy() {
    // e = (m b n a).  That is, the integral is of the form
    // x^m*exp(b*x^n+a).  I think we want to compute
    // gamma((m+1)/n)/b^((m+1)/n)/n.
    //
    // FIXME: If n > m + 1, the integral converges.  We need to check for
    // this.
    let m = nth(0, e)
    let b = nth(1, e)
    let n = nth(2, e)
    let a = nth(3, e)
    if !zerop1(d_realpart(b)).truthy() && !zerop1(d_imagpart(b)).truthy() {
      // The derivation only holds if b is purely real or purely
      // imaginary.  Give up if it's not.
      return Nil
    }
    // Check for convergence.  If b is complex, we need n - m > 1.  If b
    // is real, we need b < 0.
    if zerop1(d_imagpart(b)).truthy() && !eq(d_asksign(b), q_d_neg) {
      diverg() |> ignore
    }
    if !zerop1(d_imagpart(b)).truthy() &&
      !eq(d_asksign(sub(n, add2(m, Fix(1L)))), q_d_pos) {
      diverg() |> ignore
    }
    e = gamma1(
      m,
      if zerop1(d_imagpart(b)).truthy() {
        // If we're here, b must be negative.
        neg(b)
      } else {
        // Complex b.  Take the imaginary part
        mk(q_mabs, [d_imagpart(b)])
      },
      n,
      a,
    )
    if zd.truthy() {
      // FIXME: Why do we set %emode here?  Shouldn't we just bind it?
      // And why do we want it bound to T anyway?  Shouldn't the user
      // control that?  The same goes for dosimp.
      set(q_dosimp, t) |> ignore
      e = mul2_star(zd, e)
    }
  }
  if e.truthy() {
    mul2_star(c, e)
  } else {
    Nil
  }
}

///|
/// Match x^m*exp(b*x^n+a).  If it does, return (list m b n a).
fn ggr1(e : Value, ivar : Value, nd_var : Value) -> (Value, Value) raise {
  let mut nd_var = nd_var
  let mut zd : Value = Nil
  if atom(e) {
    (Nil, Nil)
  } else if mexptp(e).truthy() && eq(cadr(e), q_d__pcte) {
    // We're looking at something like exp(f(ivar)).  See if it's of the
    // form b*x^n+a, and return (list 0 b n a).  (The 0 is so we can graft
    // something onto it if needed.)
    let (e1, zd1) = maybpc(caddr(e), ivar, nd_var)
    if e1.truthy() {
      (cons(Fix(0L), e1), zd1)
    } else {
      (Nil, Nil)
    }
  } else if mtimesp(e).truthy() &&
    // E should be the product of exactly 2 terms
    cdddr(e) is Nil &&
    // Check to see if one of the terms is of the form ivar^p.  If so,
    // make sure the realpart of p > -1.  If so, check the other term has
    // the right form via another call to ggr1.
    (
      {
        set(q_dn_star, xtorterm(cadr(e), ivar)).truthy() &&
        ratgreaterp(
          {
            nd_var = d_realpart(symval(q_dn_star))
            nd_var
          },
          Fix(-1L),
        ).truthy() &&
        {
          let (a, b) = ggr1(caddr(e), ivar, nd_var)
          set(q_nn_star, a) |> ignore
          zd = b
          a.truthy()
        }
      } ||
      {
        set(q_dn_star, xtorterm(caddr(e), ivar)).truthy() &&
        ratgreaterp(
          {
            nd_var = d_realpart(symval(q_dn_star))
            nd_var
          },
          Fix(-1L),
        ).truthy() &&
        {
          let (a, b) = ggr1(cadr(e), ivar, nd_var)
          set(q_nn_star, a) |> ignore
          zd = b
          a.truthy()
        }
      }
    ) {
    // Both terms have the right form and nn* contains the ivar of the
    // exponential term.  Put dn* as the car of nn*.  The result is
    // something like (m b n a) when we have the expression
    // x^m*exp(b*x^n+a).
    (rplaca(symval(q_nn_star), symval(q_dn_star)), zd)
  } else {
    (Nil, Nil)
  }
}

///|
/// Match b*x^n+a.  If a match is found, return the list (a n b).
/// Otherwise, return NIL
fn bx_star_starn_plusa(e : Value, ivar : Value) -> Value raise {
  if eq(e, ivar) {
    list3(Fix(0L), Fix(1L), Fix(1L))
  } else if atom(e) || mnump(e).truthy() {
    Nil
  } else {
    let a = no_err_sub_var(Fix(0L), e, ivar)
    if a is Nil {
      Nil
    } else {
      let e = add2_star(e, mul2(Fix(-1L), a))
      let e = bx_star_starn(e, ivar)
      if e.truthy() {
        cons(a, e)
      } else {
        Nil
      }
    }
  }
}

///|
/// Match b*x^n.  Return the list (n b) if found or NIL if not.
fn bx_star_starn(e : Value, ivar : Value) -> Value raise {
  let n = xexponget(e, ivar)
  if n.truthy() {
    let e = with_specials([(q_d_maxposex, Fix(1L)), (q_d_maxnegex, Fix(1L))], fn() {
      d_expand(div_star(e, power(ivar, n)))
    })
    if !among(ivar, e).truthy() {
      return list2(n, e)
    }
  }
  Nil
}

///|
/// nn* should be the value of var.  This is only called by bx**n with
/// the second arg of var.
fn xexponget(e : Value, nn_star : Value) -> Value raise {
  let b0 = bind(q_nn_star, nn_star)
  defer unbind(b0)
  let v = symval(q_nn_star)
  if atom(e) {
    if eq(e, v) {
      Fix(1L)
    } else {
      Nil
    }
  } else if mnump(e).truthy() {
    Nil
  } else if mexptp(e).truthy() &&
    eq(cadr(e), v) &&
    !among(v, caddr(e)).truthy() {
    caddr(e)
  } else {
    some_value(j => xexponget(j, symval(q_nn_star)), cdr(e))
  }
}

///|
/// given (b*x^n+a)^m returns (m a n b)
fn bxm(e : Value, ind : Value, ivar : Value) -> Value raise {
  if atom(e) ||
    mnump(e).truthy() ||
    involve_var(e, ivar, list([q_p_log, q_p_sin, q_p_cos, q_p_tan])).truthy() ||
    p_einvolve_var(e, ivar).truthy() {
    return Nil
  }
  if mtimesp(e).truthy() {
    return Nil
  }
  if mexptp(e).truthy() {
    if among(ivar, caddr(e)).truthy() {
      return Nil
    }
    let r = bx_star_starn_plusa(cadr(e), ivar)
    if r.truthy() {
      return cons(caddr(e), r)
    } else {
      return Nil
    }
  }
  let r = bx_star_starn_plusa(e, ivar)
  if r.truthy() {
    return cons(Fix(1L), r)
  }
  if ind.truthy() {
    // Catches Unfactored forms.
    let (m0, r0) = numden_var(div_star(sdiff(e, ivar), e), ivar)
    let mut m = m0
    let mut e = e
    let r = bx_star_starn_plusa(sratsimp(r0), ivar)
    if r.truthy() &&
      !among(
        ivar,
        {
          m = div_star(
            m,
            muln_star([cadr(r), caddr(r), power(ivar, add2(Fix(-1L), cadr(r)))]),
          )
          m
        },
      ).truthy() &&
      {
        e = div_star(subin_var(Fix(0L), e, ivar), power(car(r), m))
        e.truthy()
      } {
      if equal(e, Fix(1L)) {
        cons(m, r)
      } else {
        e = power_star(e, div_star(Fix(1L), m))
        list([m, mul2_star(e, car(r)), cadr(r), mul2_star(e, caddr(r))])
      }
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// Is E = VAR raised to some power? If so return power or 0.
fn findp(e : Value, ivar : Value) -> Value raise {
  if !among(ivar, e).truthy() {
    Fix(0L)
  } else {
    xtorterm(e, ivar)
  }
}

///|
/// Is E = VAR1 raised to some power? If so return power.
fn xtorterm(e : Value, ivar : Value) -> Value raise {
  if alike1(e, ivar).truthy() {
    Fix(1L)
  } else if atom(e) {
    Nil
  } else if mexptp(e).truthy() &&
    alike1(cadr(e), ivar).truthy() &&
    !among(ivar, caddr(e)).truthy() {
    caddr(e)
  } else {
    Nil
  }
}

///|
fn tbf(l : Value) -> Value raise {
  power_star(
    mul2_star(
      power_star(caddr(l), defint__rat(1L, 2L)),
      add2_star(cadr(l), power_star(mul2_star(car(l), caddr(l)), defint__rat(1L, 2L))),
    ),
    Fix(-1L),
  )
}

///|
fn radbyterm(d : Value, l : Value, ivar : Value) -> Value raise {
  let mut ans : Value = Nil
  for x in l.iter() {
    let ci = rmconst1(x, ivar)
    let const_ = car(ci)
    let integrand = cdr(ci)
    ans = cons(mul2_star(const_, dintrad0(integrand, d, ivar)), ans)
  }
  addn(ans, Nil)
}

///|
fn sqdtc(e : Value, ind : Value, ivar : Value) -> Value raise {
  let b0 = bind(q_varlist, Nil)
  defer unbind(b0)
  set(q_varlist, list1(ivar)) |> ignore
  newvar(e) |> ignore
  let e = cdadr(ratrep_star(e))
  let c = pdis(ptterm(e, Fix(0L)))
  let b = mul2(div(Fix(1L), Fix(2L)), pdis(ptterm(e, Fix(1L))))
  let a = pdis(ptterm(e, Fix(2L)))
  if eq(
      d_asksign(add2_star(b, power_star(mul2_star(a, c), defint__rat(1L, 2L)))),
      q_d_pos,
    ) &&
    (
      (
        ind.truthy() &&
        !eq(d_asksign(a), q_d_neg) &&
        eq(d_asksign(c), q_d_pos)
      ) ||
      (eq(d_asksign(a), q_d_pos) && !eq(d_asksign(c), q_d_neg))
    ) {
    list3(a, b, c)
  } else {
    Nil
  }
}

///|
fn difap1(e : Value, pwr : Value, ivar : Value, m : Value, pt : Value) -> Value raise {
  div_star(
    muln_star([
      if eq(ask_integer(m, q_d_even), q_d_yes) {
        Fix(1L)
      } else {
        Fix(-1L)
      },
      mk(q_p_gamma, [pwr]),
      derivat(ivar, m, e, pt),
    ]),
    mk(q_p_gamma, [add2_star(pwr, m)]),
  )
}

///|
/// Note:  This doesn't seem be called from anywhere.
fn sqrtinvolve(e : Value, ivar : Value) -> Value raise {
  if atom(e) {
    Nil
  } else if mnump(e).truthy() {
    Nil
  } else if mexptp(e).truthy() &&
    mnump(caddr(e)).truthy() &&
    !numberp(caddr(e)) &&
    equal(caddr(caddr(e)), Fix(2L)) &&
    among(ivar, cadr(e)).truthy() {
    cadr(e)
  } else {
    some_value(a => sqrtinvolve(a, ivar), cdr(e))
  }
}

///|
fn bydif(r : Value, s : Value, d : Value, ivar : Value) -> Value raise {
  let mut b : Value = Fix(1L)
  let d = add2_star(mul2(q_ear_z, ivar), d)
  let p = add2_star(s, mul2(Fix(-1L), r))
  if zerop1(p).truthy() ||
    (
      zerop1(add2_star(Fix(1L), p)).truthy() &&
      {
        b = ivar
        b.truthy()
      }
    ) {
    difap1(
      dintrad0(b, power_star(d, defint__rat(3L, 2L)), ivar),
      defint__rat(3L, 2L),
      q_ear_z,
      r,
      Fix(0L),
    )
  } else if eq(d_asksign(p), q_d_pos) {
    difap1(
      difap1(
        dintrad0(
          Fix(1L),
          power_star(add2(q_z_star_star, d), defint__rat(3L, 2L)),
          ivar,
        ),
        defint__rat(3L, 2L),
        q_ear_z,
        r,
        Fix(0L),
      ),
      defint__rat(3L, 2L),
      q_z_star_star,
      p,
      Fix(0L),
    )
  } else {
    Nil
  }
}

///|
fn dintrad0(n : Value, d : Value, ivar : Value) -> Value raise {
  if mexptp(d).truthy() && equal(deg_var(cadr(d), ivar), Fix(2L)) {
    if alike1(caddr(d), defint__rat(3L, 2L)).truthy() {
      if equal(n, Fix(1L)) {
        let l = sqdtc(cadr(d), t, ivar)
        if l.truthy() {
          return tbf(l)
        }
      }
      if eq(n, ivar) {
        let l = sqdtc(cadr(d), Nil, ivar)
        if l.truthy() {
          return tbf(reverse(l))
        }
      }
      Nil
    } else {
      let r = findp(n, ivar)
      let mut s : Value = Nil
      if r.truthy() &&
        (
          eq(
            d_asksign(
              addn_star([Fix(-1L), defint__mneg(r), mul2(Fix(2L), caddr(d))]),
            ),
            q_d_pos,
          ) ||
          diverg().truthy()
        ) &&
        {
          s = add2_star(defint__rat(-3L, 2L), caddr(d))
          s.truthy()
        } &&
        eq(d_asksign(s), q_d_pos) &&
        eq(ask_integer(s, q_d_integer), q_d_yes) {
        bydif(r, s, cadr(d), ivar)
      } else if polyinx(n, ivar, Nil).truthy() {
        radbyterm(d, cdr(n), ivar)
      } else {
        Nil
      }
    }
  } else {
    Nil
  }
}

///|
/// Looks at the IMAGINARY part of a log and puts it in the interval 0
/// 2*%pi.
fn log_imag_0_2_pctpi(x : Value) -> Value raise {
  let plog = simplify(d_rectform(mk(q_p_plog, [x])))
  // We take the $rectform above to make sure that the log is expanded
  // out for the situations where simplifying plog itself doesn't do it.
  // This should probably be considered a bug in the plog simplifier and
  // should be fixed there.
  if !free(plog, q_p_plog).truthy() {
    subst(q_p_log, q_p_plog, plog)
  } else {
    let ri = trisplit(plog)
    let real = car(ri)
    let mut imag = cdr(ri)
    let pi2 = symval(q_p_pi2)
    if eq(d_asksign(imag), q_d_neg) {
      imag = add2_star(imag, pi2)
    } else if eq(d_asksign(sub_star(imag, pi2)), q_d_pos) {
      imag = sub_star(imag, pi2)
    }
    add2_star(real, mul2_star(q_d__pcti, imag))
  }
}

///|
/// Temporary fix for a lacking in taylor, which loses with %i in denom.
/// Besides doesn't seem like a bad thing to do in general.
fn p_i_out_of_denom(exp_ : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let (num, denom) = defint__dqd(fn() { num_denom_split(defint__exp()) })
  if among(q_d__pcti, denom).truthy() {
    // Multiply the denominator by it's conjugate to get rid of %i.
    let den_conj = maxima_substitute(defint__mneg(q_d__pcti), q_d__pcti, denom)
    let new_denom = sratsimp(mul2_star(denom, den_conj))
    let new_exp = sratsimp(div_star(mul2_star(num, den_conj), new_denom))
    // If the new denominator still contains %i, just give up.
    if among(q_d__pcti, defint__dqd(fn() { d_denom(new_exp) })).truthy() {
      defint__exp()
    } else {
      new_exp
    }
  } else {
    defint__exp()
  }
}

///|
/// LL and UL must be real otherwise this routine return $UNKNOWN.
/// Returns $no $unknown or a list of poles in the interval (ll ul) for
/// exp w.r.t. ivar.  Form of list ((pole . multiplicity) (pole1 .
/// multiplicity) ....)
fn poles_in_interval(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let e = defint__exp()
  let denom = if mplusp(e).truthy() {
    defint__dqd(fn() { d_denom(sratsimp(e)) })
  } else if mexptp(e).truthy() &&
    free(caddr(e), ivar).truthy() &&
    eq(d_asksign(caddr(e)), q_d_neg) {
    power_star(cadr(e), defint__mneg(caddr(e)))
  } else {
    defint__dqd(fn() { d_denom(e) })
  }
  let mut roots = real_roots(denom, ivar)
  let ll_pole = limit_pole(defint__exp(), ivar, ll, q_d_plus)
  let ul_pole = limit_pole(defint__exp(), ivar, ul, q_d_minus)
  if ll_pole is Nil || ul_pole is Nil {
    q_d_unknown
  } else if (
      eq(roots, q_d_no) ||
      defint__memq(d_csign(denom), [q_d_pos, q_d_neg, q_d_pn])
    ) &&
    // this clause handles cases where we can't find the exact roots, but
    // we know that they occur outside the interval of integration.
    //  example: integrate ((1+exp(t))/sqrt(t+exp(t)), t, 0, 1);
    eq(ll_pole, q_d_no) &&
    eq(ul_pole, q_d_no) {
    q_d_no
  } else {
    if equal(roots, q_d_no) {
      roots = Nil
    }
    let mut pole_list : Value = if !eq(ll_pole, q_d_no) {
      list1(cons(ll, Fix(1L)))
    } else {
      Nil
    }
    for root in roots.iter() {
      let soltn = car(root)
      let root_in_ll_ul = in_interval(soltn, ll, ul)
      if eq(root_in_ll_ul, q_d_no) {
        ()
      } else if eq(root_in_ll_ul, q_d_yes) {
        let lim_ans = is_a_pole(defint__exp(), soltn, ivar)
        if lim_ans is Nil {
          return q_d_unknown
        } else if equal(lim_ans, Fix(0L)) {
          ()
        } else {
          pole_list = cons(root, pole_list)
        }
      }
    }
    if !eq(ul_pole, q_d_no) {
      pole_list = cons(cons(ul, Fix(1L)), pole_list)
      sort_poles(pole_list)
    } else if pole_list.truthy() {
      sort_poles(pole_list)
    } else {
      q_d_no
    }
  }
}

///|
/// Returns $YES if there is no pole and $NO if there is one.
fn limit_pole(exp_ : Value, ivar : Value, limit : Value, direction : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let ans = if defint__memq(limit, [q_d_minf, q_d_inf]) {
    if eq(special_convergent_formp(defint__exp(), limit, ivar), q_d_yes) {
      q_d_no
    } else {
      get_limit(mul2_star(defint__exp(), ivar), ivar, limit, dir=direction)
    }
  } else {
    q_d_no
  }
  if eq(ans, q_d_no) {
    q_d_no
  } else if ans is Nil {
    Nil
  } else if defint__memq(ans, [q_d_und, q_d_infinity]) {
    // $INFINITY says the modulus grows without bound, but it says nothing
    // about the direction, so it establishes no pole that TAKE-PRINCIPAL
    // could cancel across. Treat it like UND, as in
    // integrate(exp(-%i*x^2),x,0,inf).
    q_d_no
  } else if equal(ans, Fix(0L)) {
    q_d_no
  } else {
    q_d_yes
  }
}

///|
/// Takes care of forms that the ratio test fails on.
fn special_convergent_formp(exp_ : Value, limit : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  if !oscip_var(defint__exp(), ivar).truthy() {
    q_d_no
  } else if eq(sc_converg_form(defint__exp(), limit, ivar), q_d_yes) ||
    eq(exp_converg_form(defint__exp(), limit, ivar), q_d_yes) {
    q_d_yes
  } else {
    q_d_no
  }
}

///|
fn exp_converg_form(exp_ : Value, limit : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let exparg = p_einvolve_var(defint__exp(), ivar)
  if exparg is Nil || freeof(q_d__pcti, exparg).truthy() {
    q_d_no
  } else if freeof(
      q_d__pcti,
      p_einvolve_var(
        set(q_exp, sratsimp(div_star(defint__exp(), power(q_d__pcte, exparg)))),
        ivar,
      ),
    ).truthy() &&
    equal(get_limit(defint__exp(), ivar, limit), Fix(0L)) {
    q_d_yes
  } else {
    q_d_no
  }
}

///|
fn sc_converg_form(exp_ : Value, limit : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  set(q_exp, d_expand(defint__exp())) |> ignore
  let scarg = involve_var(
    sin_sq_cos_sq_sub(defint__exp()),
    ivar,
    list([q_p_sin, q_p_cos]),
  )
  if scarg is Nil {
    return q_d_no
  } else if polyinx(scarg, ivar, Nil).truthy() &&
    eq(
      d_asksign(sub_star(funcall(q_d_hipow, [scarg, ivar]), Fix(1L))),
      q_d_pos,
    ) {
    return q_d_yes
  } else if !freeof(ivar, sdiff(scarg, ivar)).truthy() {
    return q_d_no
  }
  let mut trigpow = funcall(q_d_hipow, [defint__exp(), mk(q_p_sin, [scarg])])
  if trigpow.truthy() &&
    eq(ask_integer(trigpow, q_d_odd), q_d_yes) &&
    equal(
      get_limit(div_star(defint__exp(), mk(q_p_sin, [scarg])), ivar, limit),
      Fix(0L),
    ) {
    return q_d_yes
  }
  trigpow = funcall(q_d_hipow, [defint__exp(), mk(q_p_cos, [scarg])])
  if trigpow.truthy() &&
    eq(ask_integer(trigpow, q_d_odd), q_d_yes) &&
    equal(
      get_limit(div_star(defint__exp(), mk(q_p_cos, [scarg])), ivar, limit),
      Fix(0L),
    ) {
    return q_d_yes
  }
  q_d_no
}

///|
fn is_a_pole(exp_ : Value, soltn : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  get_limit(
    d_radcan(
      mul2_star(
        maxima_substitute(add2_star(q_epsilon, soltn), ivar, defint__exp()),
        q_epsilon,
      ),
    ),
    q_epsilon,
    Fix(0L),
    dir=q_d_plus,
  )
}

///|
fn in_interval(place : Value, ll : Value, ul : Value) -> Value raise {
  // real values for ll and ul; place can be imaginary.
  let mut ll = ll
  let mut ul = ul
  let order = ask_greateq(ul, ll)
  if eq(order, q_d_yes) {
    ()
  } else if eq(order, q_d_no) {
    let temp = ul
    ul = ll
    ll = temp
  } else {
    merr("defint: failed to order limits of integration:~%~M", [
      list3(list2(q_mlist, q_simp), ll, ul),
    ])
    |> ignore
  }
  if !equal(d_imagpart(place), Fix(0L)) {
    q_d_no
  } else {
    let lesseq_ul = ask_greateq(ul, place)
    let greateq_ll = ask_greateq(place, ll)
    if eq(lesseq_ul, q_d_yes) && eq(greateq_ll, q_d_yes) {
      q_d_yes
    } else {
      q_d_no
    }
  }
}

///|
/// returns true or nil
fn strictly_in_interval(place : Value, ll : Value, ul : Value) -> Value raise {
  // real values for ll and ul; place can be imaginary.
  lbool(
    equal(d_imagpart(place), Fix(0L)) &&
    (eq(ul, q_d_inf) || eq(d_asksign(add2_star(ul, defint__mneg(place))), q_d_pos)) &&
    (eq(ll, q_d_minf) || eq(d_asksign(add2_star(place, defint__mneg(ll))), q_d_pos)),
  )
}

///|
/// If :MULTI is NIL, solves EXP = 0 for IVAR and returns a list
/// consisting of (SOLUTION . MULTIPLICITY) pairs, or $NO if no solutions
/// were found.  If :MULTI is non-NIL, EXP is expected to be a Lisp list
/// of expressions, and and each will be solved. All solutions are
/// returned as a single list, without multiplicities, with duplicate
/// solutions removed.
fn real_roots(exp_ : Value, ivar : Value, multi? : Value = Nil) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  if multi.truthy() {
    let parts = mapcar(
      e => {
        let ans = real_roots(e, ivar)
        if eq(ans, q_d_no) {
          Nil
        } else {
          mapcar(x => car(x), ans)
        }
      },
      defint__exp(),
    )
    let all = nconc_n(list_to_array(parts))
    let v = remove_duplicates(all, pred2=(a, b) => alike1(a, b).truthy())
    return if v.truthy() { v } else { q_d_no }
  }
  // Normal mode of operation: EXP is a single expression.
  let bs = bind_all([
    (
      q_d_solvetrigwarn,
      if symval(q_ear_defintdebug).truthy() {
        t
      } else {
        Nil
      },
    ), // Rest of the code for TRIGS in denom needed.
    (
      q_d_solveradcan,
      if among(q_d__pcti, defint__exp()).truthy() ||
        among(q_d__pcte, defint__exp()).truthy() {
        t
      } else {
        Nil
      },
    ),
    (q_n_starroots, Nil),
    (q_n_starfailures, Nil), // special vars for solve.
  ])
  defer unbind_all(bs)
  if !among(ivar, defint__exp()).truthy() {
    return q_d_no
  }
  solve(defint__exp(), ivar, Fix(1L)) |> ignore
  // If *failures is set, we may have missed some roots.  We still return
  // the roots that we have found.
  let mut rootlist : Value = Nil
  let mut dummy = symval(q_n_starroots)
  while dummy.truthy() {
    if equal(d_imagpart(caddr(car(dummy))), Fix(0L)) {
      rootlist = cons(cons(d_rectform(caddr(car(dummy))), cadr(dummy)), rootlist)
    }
    dummy = cddr(dummy)
  }
  if rootlist.truthy() {
    rootlist
  } else {
    q_d_no
  }
}

///|
/// Is x > y. X or Y can be $MINF or $INF, zeroA or zeroB.
fn ask_greateq(x : Value, y : Value) -> Value raise {
  let fix = fn(x : Value) -> Value raise {
    if among(q_zeroa, x).truthy() {
      subst(Fix(0L), q_zeroa, x)
    } else if among(q_zerob, x).truthy() {
      subst(Fix(0L), q_zerob, x)
    } else if among(q_epsilon, x).truthy() {
      subst(Fix(0L), q_epsilon, x)
    } else if among(q_d_inf, x).truthy() || among(q_d_minf, x).truthy() {
      d_limit(list1(x))
    } else {
      x
    }
  }
  let x = fix(x)
  let y = fix(y)
  if eq(x, q_d_inf) {
    q_d_yes
  } else if eq(x, q_d_minf) {
    q_d_no
  } else if eq(y, q_d_inf) {
    q_d_no
  } else if eq(y, q_d_minf) {
    q_d_yes
  } else {
    let ans = d_asksign(add2_star(x, defint__mneg(y)))
    if defint__memq(ans, [q_d_zero, q_d_pos]) {
      q_d_yes
    } else if eq(ans, q_d_neg) {
      q_d_no
    } else {
      q_d_unknown
    }
  }
}

///|
fn sort_poles(pole_list : Value) -> Value raise {
  sort_list(pole_list, (x, y) => if eq(ask_greateq(car(x), car(y)), q_d_yes) {
    false
  } else {
    true
  })
}

// Integrate Definite Integrals involving log and exp functions. The
// algorithm are taken from the paper "Evaluation of CLasses of Definite
// Integrals ..." by K.O.Geddes et. al.
//
// 1. CASE: Integrals generated by the Gamma function.
//
//   integrate(t^w*log(t)^m*exp(-t^s),t,0,inf)
//     = s^(-m-1)*signum(s)*diff(gamma(z),z,m) at z = (w+1)/s
//
// The integral converges for: s # 0, m = 0, 1, 2, ... and
// realpart((w+1)/s) > 0.
//
// 2. CASE: Integrals generated by the Incomplete Gamma function.
//
//   integrate(t^w*log(t)^m*exp(-t^s),t,x,inf)
//     = diff(gamma_incomplete(a,x^s),a,m) at a = (w+1)/s
//       * s^(-m-1)*signum(s)
//
// The integral converges for: s # 0, m = 0, 1, 2, ... and
// realpart((w+1)/s) > 0.  The shown solution is valid for s>0. For s<0
// gamma_incomplete has to be replaced by gamma(a) -
// gamma_incomplete(a,x^s).
//
// 3. CASE: Integrals generated by the beta function.
//
//   integrate(log(1-t)^m*(1-t)^s*t^r*log(t)^n,t,0,1)
//     = diff(diff(beta(z,w),w,m) at w = s+1, z, n) at z = r+1
//
// The integral converges for: n, m = 0, 1, 2, ..., s > -1 and r > -1.

///|
/// Placeholder for the integration variable in the M2 patterns below.
let defint__q_pat_ivar : Value = sym("defint-pattern-ivar")

///|
let defint__lit_log_exp_1 : Value = try! lread(
  "((mtimes) (c freevar2 defint-pattern-ivar) ((mexpt) (z varp2 defint-pattern-ivar) (w freevar2 defint-pattern-ivar)) ((mexpt) $%e ((mtimes) -1 ((mexpt) (z varp2 defint-pattern-ivar) (s freevar02 defint-pattern-ivar)))) ((mexpt) ((%log) (z varp2 defint-pattern-ivar)) (m freevar2 defint-pattern-ivar)))",
)

///|
let defint__lit_log_exp_2 : Value = try! lread(
  "((mtimes) (c freevar2 defint-pattern-ivar) ((mexpt) (z varp2 defint-pattern-ivar) (r freevar2 defint-pattern-ivar)) ((mexpt) ((%log) (z varp2 defint-pattern-ivar)) (n freevar2 defint-pattern-ivar)) ((mexpt) ((mplus) 1 ((mtimes) -1 (z varp2 defint-pattern-ivar))) (s freevar2 defint-pattern-ivar)) ((mexpt) ((%log) ((mplus) 1 ((mtimes) -1 (z varp2 defint-pattern-ivar)))) (m freevar2 defint-pattern-ivar)))",
)

///|
/// Recognize c*z^w*log(z)^m*exp(-t^s)
fn m2_log_exp_1(expr : Value, ivar : Value) -> Value raise {
  if symval(q_ear_debug_defint_log).truthy() {
    format(t, "~&M2-LOG-EXP-1 with ~A~%", [expr]) |> ignore
  }
  m2(expr, subst(ivar, defint__q_pat_ivar, defint__lit_log_exp_1))
}

///|
/// Recognize c*z^r*log(z)^n*(1-z)^s*log(1-z)^m
fn m2_log_exp_2(expr : Value, ivar : Value) -> Value raise {
  if symval(q_ear_debug_defint_log).truthy() {
    format(t, "~&M2-LOG-EXP-2 with ~A~%", [expr]) |> ignore
  }
  m2(expr, subst(ivar, defint__q_pat_ivar, defint__lit_log_exp_2))
}

///|
fn defint_log_exp(expr : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let mut x : Value = Nil
  let mut result : Value = Nil
  let var1 = gensym()
  // var1 is used as a parameter for differentiation. Add var1>0 to the
  // database, to get the desired simplification of the differentiation
  // of the gamma_incomplete function.
  set(
    q_ear_global_defint_assumptions,
    cons(
      assume(mk(q_mgreaterp, [var1, Fix(0L)])),
      symval(q_ear_global_defint_assumptions),
    ),
  )
  |> ignore
  let debug = symval(q_ear_debug_defint_log).truthy()
  if eq(ul, q_d_inf) &&
    {
      x = m2_log_exp_1(expr, ivar)
      x.truthy()
    } {
    // The integrand matches the cases 1 and 2.
    let c = cdras(q_c, x)
    let w = cdras(q_w, x)
    let m = cdras(q_m, x)
    let s = cdras(q_s, x)
    with_special(q_d_gamma_expand, Nil, fn() {
      // No expansion of Gamma functions.
      if debug {
        format(t, "~&DEFINT-LOG-EXP-1:~%", []) |> ignore
        format(t, "~&   : c = ~A~%", [c]) |> ignore
        format(t, "~&   : w = ~A~%", [w]) |> ignore
        format(t, "~&   : m = ~A~%", [m]) |> ignore
        format(t, "~&   : s = ~A~%", [s]) |> ignore
      }
      if zerop1(ll).truthy() &&
        integerp(m) &&
        num_ge(m, Fix(0L)) &&
        !eq(d_sign(s), q_d_zero) &&
        eq(d_sign(div(add2(w, Fix(1L)), s)), q_d_pos) {
        // Case 1: Generated by the Gamma function.
        result = muln_([
          c,
          simplify(list2(list1(q_p_signum), s)),
          power(s, mul2(Fix(-1L), add2(m, Fix(1L)))),
          d_at(
            d_diff(list3(list2(list1(q_p_gamma), var1), var1, m)),
            list3(list1(q_mequal), var1, div(add2(w, Fix(1L)), s)),
          ),
        ])
      } else if defint__memq(d_sign(ll), [q_d_pos, q_d_pz]) &&
        integerp(m) &&
        // Exclude m>1, because Maxima can not derivate the involved
        // hypergeometric functions.
        (num_eq(m, Fix(0L)) || num_eq(m, Fix(1L))) &&
        (
          (
            eq(d_sign(s), q_d_neg) &&
            eq(d_sign(div(add2(Fix(1L), w), s)), q_d_pos)
          ) ||
          (
            eq(d_sign(s), q_d_pos) &&
            eq(d_sign(div(add2(Fix(1L), w), s)), q_d_pos)
          )
        ) {
        // Case 2: Generated by the Incomplete Gamma function.
        let f = if eq(d_sign(s), q_d_pos) {
          list3(list1(q_p_gamma_incomplete), var1, power(ll, s))
        } else {
          sub(
            list2(list1(q_p_gamma), var1),
            list3(list1(q_p_gamma_incomplete), var1, power(ll, s)),
          )
        }
        result = muln_([
          c,
          simplify(list2(list1(q_p_signum), s)),
          power(s, mul2(Fix(-1L), add2(m, Fix(1L)))),
          d_at(
            d_diff(list3(f, var1, m)),
            list3(list1(q_mequal), var1, div(add2(Fix(1L), w), s)),
          ),
        ])
      } else {
        result = Nil
      }
    })
  } else if zerop1(ll).truthy() &&
    onep1(ul).truthy() &&
    {
      x = m2_log_exp_2(expr, ivar)
      x.truthy()
    } {
    // Case 3: Generated by the Beta function.
    let c = cdras(q_c, x)
    let r = cdras(q_r, x)
    let n = cdras(q_n, x)
    let s = cdras(q_s, x)
    let m = cdras(q_m, x)
    let var1 = gensym()
    let var2 = gensym()
    if debug {
      format(t, "~&DEFINT-LOG-EXP-2:~%", []) |> ignore
      format(t, "~&   : c = ~A~%", [c]) |> ignore
      format(t, "~&   : r = ~A~%", [r]) |> ignore
      format(t, "~&   : n = ~A~%", [n]) |> ignore
      format(t, "~&   : s = ~A~%", [s]) |> ignore
      format(t, "~&   : m = ~A~%", [m]) |> ignore
    }
    if integerp(m) &&
      num_ge(m, Fix(0L)) &&
      integerp(n) &&
      num_ge(n, Fix(0L)) &&
      eq(d_sign(add2(Fix(1L), r)), q_d_pos) &&
      eq(d_sign(add2(Fix(1L), s)), q_d_pos) {
      result = mul2(
        c,
        d_at(
          d_diff(
            list3(
              d_at(
                d_diff(list3(list3(list1(q_p_beta), var1, var2), var2, m)),
                list3(list1(q_mequal), var2, add2(Fix(1L), s)),
              ),
              var1,
              n,
            ),
          ),
          list3(list1(q_mequal), var1, add2(Fix(1L), r)),
        ),
      )
    } else {
      result = Nil
    }
  } else {
    result = Nil
  }
  // Simplify result and set $gamma_expand to global value
  with_special(q_d_gamma_expand, symval(q_d_gamma_expand), fn() {
    sratsimp(result)
  })
}
