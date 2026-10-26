// Port of src/residu.lisp: residues of rational functions, used by the
// definite integration package (defint.lisp).

///|
/// `(andmapcar f l)`: like mapcar, but nil as soon as one result is nil.
fn residu__andmapcar(f : (Value) -> Value raise, l : Value) -> Value raise {
  let c = Collector::new()
  for x in l.iter() {
    let d = f(x)
    if d is Nil {
      return Nil
    }
    c.add(d)
  }
  c.result()
}

///|
/// Compute the poles (roots) of the polynomial D and return them.
/// Divide these roots into several parts: Those in REGION, REGION1,
/// and everywhere else.  These are returned in a list.
///
/// The regions are determined by functions REGION and REGION1, which
/// should return non-NIL if the root is in the given region.
///
/// The first part of the list of the form ((r1 (x - r1)^d1) (r2 (x -
/// r2)^d2) ...) where r1, r2 are the roots, d1, d2 are the
/// multiplicity of each root, and x is the variable.
///
/// The second part is a list of the repeated roots in REGION.  Each
/// element of the list is of the form (r d) where r is the root and d
/// is the multiplicity.
///
/// The third part is a list of the simple roots in REGION.
///
/// Finally, the fourth part is NIL, unless *semirat* is T.
fn polelist(d : Value, region : Value, region1 : Value) -> Value raise {
  residu__polelist(symval(q_var), d, region, region1, fn(e) {
    solvecase(e)
  })
}

///|
/// Shared body of POLELIST and POLELIST-VAR.
fn residu__polelist(
  var1 : Value,
  d0 : Value,
  region : Value,
  region1 : Value,
  solver : (Value) -> Value raise,
) -> Value raise {
  let bs = bind_all([(q_d_breakup, Nil), (q_wflag, Nil)])
  defer unbind_all(bs)
  let mut d = d0
  let mut r : Value = Nil
  let mut rr : Value = Nil
  let mut ss : Value = Nil
  let mut r1 : Value = Nil
  let mut s : Value = Nil
  let mut cf : Value = Nil
  set(q_wflag, t) |> ignore
  set(q_ear_leadcoef, polyinx(d, var1, q_leadcoef)) |> ignore
  let mut roots = solver(d)
  if eq(roots, q_failure) {
    return Nil
  }
  // Loop over all the roots.  SOLVECASE returns the roots in the form
  // ((x = r1) mult1
  //  (x = r2) mult2
  //  ...)
  while true {
    if roots is Nil {
      if symval(q_ear_semirat).truthy() &&
        length(s) + length(r) > length(ss) + length(rr) {
        // Return CF, repeated roots (*semirat*), simple
        // roots (*semirat*), roots in region 1.
        return list([cf, rr, ss, r1])
      } else {
        // Return CF, repeated roots, simple roots, roots in region 1.
        return list([cf, r, s, r1])
      }
    }
    // Set POLE to the actual root and set D to the multiplicity of
    // the root.
    let pole = caddr(car(roots))
    d = cadr(roots)
    if symval(q_ear_leadcoef).truthy() {
      // Push (pole (x - pole)^d) onto the list CF.
      cf = cons(
        pole,
        cons(
          power_star(add2_star(var1, mul2_star(Fix(-1L), pole)), d),
          cf,
        ),
      )
    }
    // Don't change the order of clauses here.  We want to call REGION
    // and then REGION1.
    if funcall(region, [pole]).truthy() {
      // The pole is in REGION
      if equal(d, Fix(1L)) {
        // A simple pole, so just push the pole onto the list S.
        s = cons(pole, s)
      } else {
        // A multiple pole, so push (pole d) onto the list R.
        r = cons(list2(pole, d), r)
      }
    } else if funcall(region1, [pole]).truthy() {
      // The pole is in REGION1
      if !symval(q_d_noprincipal).truthy() {
        r1 = cons(pole, r1)
      } else {
        return Nil
      }
    } else if symval(q_ear_semirat).truthy() {
      // The pole is not in REGION or REGION1, so push the pole onto
      // SS or RR depending if the pole is repeated or not.
      if equal(d, Fix(1L)) {
        ss = cons(pole, ss)
      } else {
        rr = cons(list2(pole, d), rr)
      }
    }
    // Pop this root and multiplicity and move on.
    roots = cddr(roots)
  }
  Nil
}

///|
/// Like POLELIST, but dependency on VAR is explicit.  Use this instead
/// when possible.
fn polelist_var(
  var1 : Value,
  d : Value,
  region : Value,
  region1 : Value,
) -> Value raise {
  residu__polelist(var1, d, region, region1, fn(e) { solvecase_var(e, var1) })
}

///|
fn solvecase(e : Value) -> Value raise {
  solvecase_var(e, symval(q_var))
}

///|
fn solvecase_var(e : Value, var1 : Value) -> Value raise {
  if !among(var1, e).truthy() {
    Nil
  } else {
    with_specials([(q_n_starfailures, Nil), (q_n_starroots, Nil)], fn() {
      solve(e, var1, Fix(1L)) |> ignore
      if symval(q_n_starfailures).truthy() {
        q_failure
      } else if symval(q_n_starroots) is Nil {
        Nil
      } else {
        symval(q_n_starroots)
      }
    })
  }
}

///|
/// Compute the sum of the residues of n/d.
fn res(n : Value, d : Value, region : Value, region1 : Value) -> Value raise {
  let mut pl = polelist(d, region, region1)
  let b0 = bind(q_ear_leadcoef, Nil)
  defer unbind(b0)
  if pl is Nil {
    return Nil
  }
  let var1 = symval(q_var)
  let factors = car(pl)
  let mut dp : Value = Nil
  pl = cdr(pl)
  // PL now contains the list of the roots in region, roots in
  // region1, and everything else.
  if cadr(pl).truthy() || caddr(pl).truthy() {
    dp = sdiff(d, var1)
  }
  let a = if car(pl).truthy() {
    // Compute the sum of the residues of n/d for the multiple roots in
    // REGION.
    addn(
      residue(
        n,
        if symval(q_ear_leadcoef).truthy() {
          factors
        } else {
          d
        },
        car(pl),
      ),
      Nil,
    )
  } else {
    Fix(0L)
  }
  let b = if cadr(pl).truthy() {
    // Compute the sum of the residues of n/d for the simple roots in
    // REGION1.  Since the roots are simple, we can use RES1 to compute
    // the residues instead of the more complicated $RESIDUE.  (This
    // works around a bug described in bug 1073338.)
    addn(res1(n, dp, cadr(pl)), Nil)
  } else {
    Fix(0L)
  }
  let c = if caddr(pl).truthy() {
    // Compute the sum of the residues of n/d for the roots not in
    // REGION nor REGION1.
    addn(
      mapcar(
        pole => d_residue(div_star(n, d), symval(q_var), pole),
        caddr(pl),
      ),
      Nil,
    )
  } else {
    Nil
  }
  // Return the sum of the residues in the two regions and the sum of
  // the residues outside the two regions.
  list2(add2_star(a, b), c)
}

///|
fn res_var(
  var1 : Value,
  n : Value,
  d : Value,
  region : Value,
  region1 : Value,
) -> Value raise {
  let mut pl = polelist_var(var1, d, region, region1)
  let b0 = bind(q_ear_leadcoef, Nil)
  defer unbind(b0)
  if pl is Nil {
    return Nil
  }
  let factors = car(pl)
  let mut dp : Value = Nil
  pl = cdr(pl)
  if cadr(pl).truthy() || caddr(pl).truthy() {
    dp = sdiff(d, var1)
  }
  let a = if car(pl).truthy() {
    // Compute the sum of the residues of n/d for the multiple roots in
    // REGION.  Binding VAR is very important for defint.  It prevents
    // the plog simplifier from simplifying plog until the pole has been
    // substituted in when computing the residue.
    addn(
      with_special(q_var, var1, fn() {
        residue_var(
          var1,
          n,
          if symval(q_ear_leadcoef).truthy() {
            factors
          } else {
            d
          },
          car(pl),
        )
      }),
      Nil,
    )
  } else {
    Fix(0L)
  }
  let b = if cadr(pl).truthy() {
    addn(res1_var(var1, n, dp, cadr(pl)), Nil)
  } else {
    Fix(0L)
  }
  let c = if caddr(pl).truthy() {
    addn(
      mapcar(pole => d_residue(div_star(n, d), var1, pole), caddr(pl)),
      Nil,
    )
  } else {
    Nil
  }
  list2(add2_star(a, b), c)
}

///|
fn residue(zn : Value, factors : Value, pl : Value) -> Value raise {
  let b0 = bind(q_zn, zn)
  defer unbind(b0)
  if symval(q_ear_leadcoef).truthy() {
    mapcar(
      j => {
        let f = remfactor(factors, car(j), symval(q_zn))
        resm0(car(f), cadr(f), car(j), cadr(j))
      },
      pl,
    )
  } else {
    mapcar(j => resm1(div_star(symval(q_zn), factors), car(j)), pl)
  }
}

///|
fn residue_var(
  var1 : Value,
  zn : Value,
  factors : Value,
  pl : Value,
) -> Value raise {
  let b0 = bind(q_zn, zn)
  defer unbind(b0)
  if symval(q_ear_leadcoef).truthy() {
    mapcar(
      j => {
        let f = remfactor(factors, car(j), symval(q_zn))
        resm0_var(var1, car(f), cadr(f), car(j), cadr(j))
      },
      pl,
    )
  } else {
    mapcar(
      j => resm1_var(var1, div_star(symval(q_zn), factors), car(j)),
      pl,
    )
  }
}

///|
/// Compute the residues of zn/d for the simple poles in the list PL1.
/// The poles must be simple because ZD must be the derivative of
/// denominator.  For simple poles the residue can be computed as
/// limit(n(z)/d(z)*(z-a),z,a).  Since the pole is simple we have the
/// indeterminate form (z-a)/d(z).  Use L'Hospital's rule to get
/// 1/d'(z).  Hence, the residue is easily computed as n(a)/d'(a).
fn res1(zn : Value, zd : Value, pl1 : Value) -> Value raise {
  let b0 = bind(q_zn, zn)
  defer unbind(b0)
  let zd = div_star(symval(q_zn), zd)
  // In case the pole is messy, call $RECTFORM.  This works around some
  // issues with gcd bugs in certain cases.  (See bug 1073338.)
  mapcar(j => d_rectform(d_expand(subin(d_rectform(j), zd))), pl1)
}

///|
fn res1_var(var1 : Value, zn : Value, zd : Value, pl1 : Value) -> Value raise {
  let b0 = bind(q_zn, zn)
  defer unbind(b0)
  let zd = div_star(symval(q_zn), zd)
  mapcar(j => d_rectform(d_expand(subin_var(d_rectform(j), zd, var1))), pl1)
}

///|
fn resprog0(f : Value, g : Value, n : Value, n2 : Value) -> Value raise {
  residu__resprog0(resprog(f, g), f, g, n, n2)
}

///|
/// Shared tail of RESPROG0 and RESPROG0-VAR; A is the RESPROG result.
fn residu__resprog0(
  a0 : Value,
  f : Value,
  g : Value,
  n : Value,
  n2 : Value,
) -> Value raise {
  let mut a = a0
  let mut b = cadr(a)
  let c = ptimes(cddr(a), n2)
  a = caar(a)
  a = ptimes(n, a)
  b = ptimes(n, b)
  let mut r = pdivide(a, g)
  a = cadr(r)
  r = car(r)
  b = cons(pplus(ptimes(car(r), f), ptimes(cdr(r), b)), cdr(r))
  cons(cons(car(a), ptimes(cdr(a), c)), cons(car(b), ptimes(cdr(b), c)))
}

///|
fn resprog0_var(
  var1 : Value,
  f : Value,
  g : Value,
  n : Value,
  n2 : Value,
) -> Value raise {
  residu__resprog0(resprog_var(var1, f, g), f, g, n, n2)
}

///|
fn resm0(e : Value, n : Value, pole : Value, m : Value) -> Value raise {
  let mut e = div_star(n, e)
  e = d_diff(list3(e, symval(q_var), num_sub(m, Fix(1L))))
  e = d_rectform(d_expand(subin(pole, e)))
  div_star(e, simplify(mk(q_mfactorial, [num_sub(m, Fix(1L))])))
}

///|
fn resm0_var(
  var1 : Value,
  e : Value,
  n : Value,
  pole : Value,
  m : Value,
) -> Value raise {
  let mut e = div_star(n, e)
  e = d_diff(list3(e, var1, num_sub(m, Fix(1L))))
  e = d_rectform(d_expand(subin_var(pole, e, var1)))
  div_star(e, simplify(mk(q_mfactorial, [num_sub(m, Fix(1L))])))
}

///|
fn remfactor(l : Value, p : Value, n : Value) -> Value raise {
  let mut l = l
  let mut g : Value = Nil
  while true {
    if l is Nil {
      return list2(muln(cons(symval(q_ear_leadcoef), g), Nil), n)
    } else if equal(p, car(l)) {
      ()
    } else {
      g = cons(cadr(l), g)
    }
    l = cddr(l)
  }
  Nil
}

///|
fn resprog(p1b : Value, p2b : Value) -> Value raise {
  resprog_var(symval(q_var), p1b, p2b)
}

///|
fn resprog_var(var1 : Value, p1b : Value, p2b : Value) -> Value raise {
  let mut p1b = p1b
  let mut p2b = p2b
  let mut coef1s : Value = Fix(0L)
  let mut coef2r : Value = coef1s
  let mut coef1r : Value = Fix(1L)
  let mut coef2s : Value = coef1r
  while true {
    // b1
    if num_lt(pdegree(p1b, var1), pdegree(p2b, var1)) {
      let mut temp = p2b
      p2b = p1b
      p1b = temp
      temp = coef2r
      coef2r = coef1r
      coef1r = temp
      temp = coef2s
      coef2s = coef1s
      coef1s = temp
    }
    // b2
    if zerop(pdegree(p2b, var1)) {
      return cons(cons(coef2r, p2b), cons(coef2s, p2b))
    }
    let zeropolb = psimp(
      var1,
      list2(num_sub(pdegree(p1b, var1), pdegree(p2b, var1)), Fix(1L)),
    )
    let fac = pgcd(caddr(p1b), caddr(p2b))
    let f1 = pquotient(caddr(p1b), fac)
    let f2 = pquotient(caddr(p2b), fac)
    p1b = pdifference(
      ptimes(f2, psimp(car(p1b), cdddr(p1b))),
      ptimes(f1, ptimes(zeropolb, psimp(car(p2b), cdddr(p2b)))),
    )
    coef1r = pdifference(ptimes(f2, coef1r), ptimes(ptimes(f1, coef2r), zeropolb))
    coef1s = pdifference(ptimes(f2, coef1s), ptimes(ptimes(f1, coef2s), zeropolb))
  }
  Nil
}

///|
/// Looks for polynomials. puts polys^(pos-num) in sn* polys^(neg-num) in sd*.
fn snumden(e : Value) -> Value raise {
  let var1 = symval(q_var)
  if atom(e) || mnump(e).truthy() {
    set(q_sn_star, cons(e, symval(q_sn_star)))
  } else if mexptp(e).truthy() && integerp(caddr(e)) {
    if polyinx(cadr(e), var1, Nil).truthy() {
      if minusp(caddr(e)) {
        set(
          q_sd_star,
          cons(
            if equal(caddr(e), Fix(-1L)) {
              cadr(e)
            } else {
              power_star(cadr(e), num_neg(caddr(e)))
            },
            symval(q_sd_star),
          ),
        )
      } else {
        set(q_sn_star, cons(e, symval(q_sn_star)))
      }
    } else {
      Nil
    }
  } else if polyinx(e, var1, Nil).truthy() {
    set(q_sn_star, cons(e, symval(q_sn_star)))
  } else {
    Nil
  }
}

///|
/// Like SNUMDEN, but dependency on VAR is explicit.  Use this instead
/// when possible.
fn snumden_var(
  e : Value,
  var1 : Value,
  sn : Value,
  sd : Value,
) -> (Value, Value, Value) raise {
  if atom(e) || mnump(e).truthy() {
    (t, cons(e, sn), sd)
  } else if mexptp(e).truthy() && integerp(caddr(e)) {
    if polyinx(cadr(e), var1, Nil).truthy() {
      if minusp(caddr(e)) {
        let sd = cons(
          if equal(caddr(e), Fix(-1L)) {
            cadr(e)
          } else {
            power_star(cadr(e), num_neg(caddr(e)))
          },
          sd,
        )
        (t, sn, sd)
      } else {
        (t, cons(e, sn), sd)
      }
    } else {
      (Nil, Nil, Nil)
    }
  } else if polyinx(e, var1, Nil).truthy() {
    (t, cons(e, sn), sd)
  } else {
    (Nil, Nil, Nil)
  }
}

///|
fn d_residue(e : Value, var_ : Value, p : Value) -> Value raise {
  let b0 = bind(q_var, var_)
  defer unbind(b0)
  if d_unknown(e).truthy() {
    d_nounify(q_d_residue) |> ignore
    list([list1(q_p_residue), e, symval(q_var), p])
  } else {
    with_specials([(q_sn_star, Nil), (q_sd_star, Nil)], fn() {
      if mtimesp(e).truthy() &&
        residu__andmapcar(x => snumden(x), cdr(e)).truthy() {
        set(q_nn_star, muln(symval(q_sn_star), Nil)) |> ignore
        set(q_dn_star, muln(symval(q_sd_star), Nil)) |> ignore
      } else {
        numden(e) |> ignore
      }
    })
    resm1(div_star(symval(q_nn_star), symval(q_dn_star)), p)
  }
}

///|
fn resm1(e : Value, pole : Value) -> Value raise {
  resm1_var(symval(q_var), e, pole)
}

///|
fn resm1_var(var1 : Value, e : Value, pole : Value) -> Value raise {
  // Call taylor with silent-taylor-flag t and catch an error.
  let e = catch_tag(q_taylor_catch, fn() {
    with_special(q_silent_taylor_flag, t, fn() {
      // Things like residue(s/(s^2-a^2),s,a) fails if use -1.
      d_taylor(e, list3(var1, pole, Fix(1L)))
    })
  })
  if e.truthy() {
    coeff(
      ratdisrep(e),
      power_star(add2_star(mul2_star(Fix(-1L), pole), var1), Fix(-1L)),
      Fix(1L),
    )
  } else {
    merr("residue: taylor failed.", [])
  }
}

///|
fn init_residu() -> Unit raise {
  set(q_sn_star, Nil) |> ignore
  set(q_sd_star, Nil) |> ignore
}
