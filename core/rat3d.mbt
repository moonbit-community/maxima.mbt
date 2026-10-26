// Port of src/rat3d.lisp: the new Rational Function Package, part 4.
// The polynomial factoring routines.

///|
fn listovars(q : Value) -> Value raise {
  if atom(q) {
    Nil
  } else {
    with_special(q_ans, Nil, () => listovars0(q))
  }
}

///|
fn listovars0(q : Value) -> Value raise {
  if atom(q) {
    symval(q_ans)
  } else if memq(car(q), symval(q_ans)).truthy() {
    listovars1(cdr(q))
  } else {
    set(q_ans, cons(car(q), symval(q_ans))) |> ignore
    listovars1(cdr(q))
  }
}

///|
fn listovars1(ql : Value) -> Value raise {
  let mut ql = ql
  while !(ql is Nil) {
    listovars0(cadr(ql)) |> ignore
    ql = cddr(ql)
  }
  symval(q_ans)
}

///|
fn dontfactor(y : Value) -> Value raise {
  let df = symval(q_d_dontfactor)
  if df is Nil || equal(df, list1(list1(q_mlist))) {
    Nil
  } else if memalike(pdis(make_poly(y)), df).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn removealg(l : Value) -> Value raise {
  remove_if(v => ratmac__algv(v).truthy(), l)
}

///|
fn degvecdisrep(degl : Value) -> Value raise {
  let mut l = degl
  let mut gv = symval(q_genvar)
  let mut ans : Value = Fix(1L)
  while !(l is Nil) {
    if ratmac__gt(car(l), Fix(0L)) {
      ans = list3(car(gv), car(l), ans)
    }
    l = cdr(l)
    gv = cdr(gv)
  }
  ans
}

///|
fn ptermcont(p : Value) -> Value raise {
  let tcont = degvecdisrep(pmindegvec(p))
  with_special(q_d_algebraic, Nil, () => list2(tcont, pquotient(p, tcont)))
}

///|
fn pmindegvec(p : Value) -> Value raise {
  let odr = putodr(reverse(symval(q_genvar)))
  let nn = int(length(symval(q_genvar)) + 1)
  rat3d__minlist_in_place(
    with_specials([(q_ear_odr, odr), (q_nn_star, nn), (q_ear_min, t)], () => degvector(
      Nil,
      Fix(1L),
      p,
    )),
  )
}

///|
fn pdegreevector(p : Value) -> Value raise {
  let odr = putodr(reverse(symval(q_genvar)))
  let nn = int(length(symval(q_genvar)) + 1)
  rat3d__maxlist_in_place(
    with_specials([(q_ear_odr, odr), (q_nn_star, nn), (q_ear_mx, t)], () => degvector(
      Nil,
      Fix(1L),
      p,
    )),
  )
}

///|
/// For L, a list of lists of reals of the same length N, returns the list of
/// componentwise maxima (DO-MAX) or minima; IN-PLACE modifies the first
/// sublist to hold the result. (The macrolet-defined MAXLIST, MAXLIST-IN-PLACE,
/// MINLIST, MINLIST-IN-PLACE of rat3d.lisp.)
fn rat3d__maxminl(l : Value, do_max : Bool, in_place : Bool) -> Value raise {
  let l1 = if in_place { car(l) } else { copy_list(car(l)) }
  let mut ll = cdr(l)
  while !(ll is Nil) {
    let mut v1 = l1
    let mut v2 = car(ll)
    while !(v1 is Nil) {
      let better = if do_max {
        ratmac__gt(car(v2), car(v1))
      } else {
        ratmac__lt(car(v2), car(v1))
      }
      if better {
        rplaca(v1, car(v2)) |> ignore
      }
      v1 = cdr(v1)
      v2 = cdr(v2)
    }
    ll = cdr(ll)
  }
  l1
}

///|
fn rat3d__maxlist(l : Value) -> Value raise {
  rat3d__maxminl(l, true, false)
}

///|
fn rat3d__maxlist_in_place(l : Value) -> Value raise {
  rat3d__maxminl(l, true, true)
}

///|
fn rat3d__minlist(l : Value) -> Value raise {
  rat3d__maxminl(l, false, false)
}

///|
fn rat3d__minlist_in_place(l : Value) -> Value raise {
  rat3d__maxminl(l, false, true)
}

///|
fn quick_sqfr_check(p : Value, var2 : Value) -> Value raise {
  let mut gv = remove_equal(var2, listovars(p))
  let m = {
    let m = symval(q_modulus)
    if m.truthy() {
      m
    } else {
      symval(q_n_staralpha)
    }
  }
  with_special(q_modulus, m, () => {
    if symval(q_d_algebraic).truthy() {
      gv = removealg(gv)
    }
    if gv is Nil {
      return Nil
    }
    let l = rand(int(length(gv)), symval(q_modulus))
    if ratmac__pz(pcsubsty(l, gv, pmod(caddr(p)))) {
      return Nil
    }
    let p0 = pcsubsty(l, gv, pmod(p))
    if atom(p0) {
      return Nil
    }
    if !atom(pgcd(p0, pderivative(p0, car(p0)))) {
      return Nil
    }
    list3(l, gv, p0)
  })
}

///|
fn monom__gtfacl(p : Value) -> Value raise {
  if atom(p) {
    if equal(p, Fix(1L)) {
      Nil
    } else {
      list2(p, Fix(1L))
    }
  } else {
    cons(pget(car(p)), cons(cadr(p), monom__gtfacl(caddr(p))))
  }
}

///|
/// PSQFR: square-free factorization; returns (f1 m1 f2 m2 ...).
fn psqfr(p : Value) -> Value raise {
  let mut p = p
  let mut r : Value = Nil
  let mut varl : Value = Nil
  let mut var2 : Value = Nil
  let mut mult : Value = Fix(0L)
  let mut factors : Value = Nil
  if atom(p) {
    return cfactor(p)
  } else if rat3a__pminusp(p) {
    return cons(Fix(-1L), cons(Fix(1L), psqfr(pminus(p))))
  }
  let tc = ptermcont(p)
  factors = car(tc)
  p = cadr(tc)
  factors = monom__gtfacl(factors)
  // labels: 0=setvar 1=a 2=nextvar 3=end
  let mut lbl = 0
  if atom(p) {
    lbl = 3
  } else {
    varl = sort_list(listovars(p), (a, b) => ratmac__pgp(a, b))
  }
  while lbl != 4 {
    match lbl {
      0 => {
        var2 = car(varl)
        varl = cdr(varl)
        mult = Fix(0L)
        if ratmac__pgp(var2, car(p)) {
          lbl = 2
          continue
        } else if dontfactor(var2).truthy() {
          factors = cons(p, cons(Fix(1L), factors))
          p = Fix(1L)
          lbl = 3
          continue
        }
        if quick_sqfr_check(p, var2).truthy() {
          // QUICK SQFR CHECK BY SUBST.
          r = oldcontent(p)
          p = car(r)
          factors = cons(cadr(r), cons(Fix(1L), factors))
          lbl = 2
          continue
        }
        r = pderivative(p, var2)
        if ratmac__pz(r) {
          lbl = 2
          continue
        }
        if symval(q_modulus).truthy() && !atom(r) {
          pmonicize(cdr(r)) |> ignore
        }
        p = pgcdcofacts(p, r)
        if symval(q_algfac_star).truthy() && cadddr(p).truthy() {
          set(q_adn_star, ptimes(symval(q_adn_star), cadddr(p))) |> ignore
        }
        r = cadr(p) // PRODUCT OF P[I]
        p = car(p)
        lbl = 1
      }
      1 => {
        r = pgcdcofacts(r, p)
        p = caddr(r)
        mult = num_add(mult, Fix(1L))
        if symval(q_algfac_star).truthy() && cadddr(r).truthy() {
          set(q_adn_star, ptimes(symval(q_adn_star), cadddr(r))) |> ignore
        }
        if !atom(cadr(r)) {
          factors = cons(cadr(r), cons(mult, factors))
        }
        r = car(r)
        if !atom(r) {
          continue
        }
        lbl = 2
      }
      2 => {
        if atom(p) {
          lbl = 3
          continue
        } else if varl.truthy() {
          lbl = 0
          continue
        } else if symval(q_modulus).truthy() {
          factors = append(
            fixmult(psqfr(pmodroot(p)), symval(q_modulus)),
            factors,
          )
          p = Fix(1L)
        }
        lbl = 3
      }
      _ => {
        p = if equal(Fix(1L), p) { Nil } else { cfactor(p) }
        lbl = 4
      }
    }
  }
  append(p, factors)
}

///|
fn fixmult(l : Value, n : Value) -> Value raise {
  let mut x = l
  while !(x is Nil) {
    rplaca(cdr(x), num_mul(n, cadr(x))) |> ignore
    x = cddr(x)
  }
  l
}

///|
fn pmodroot(p : Value) -> Value raise {
  if atom(p) {
    p
  } else if alg(p).truthy() {
    pexpt(
      p,
      expt(symval(q_modulus), num_sub(car(alg(p)), Fix(1L))),
    )
  } else {
    cons(car(p), pmodroot1(cdr(p)))
  }
}

///|
fn pmodroot1(x : Value) -> Value raise {
  if x is Nil {
    x
  } else {
    cons(
      num_truncate(car(x), b=symval(q_modulus)).0,
      cons(pmodroot(cadr(x)), pmodroot1(cddr(x))),
    )
  }
}

///|
fn savefactors(l : Value) -> Value raise {
  if symval(q_d_savefactors).truthy() {
    savefactor1(car(l)) |> ignore
    savefactor1(cdr(l)) |> ignore
  }
  l
}

///|
fn savefactor1(p : Value) -> Value raise {
  if !(atom(p) ||
    cdddr(p) is Nil ||
    member_equal(p, symval(q_ear_checkfactors)).truthy()) {
    set(q_ear_checkfactors, cons(p, symval(q_ear_checkfactors)))
  } else {
    Nil
  }
}

///|
fn heurtrial1(poly : Value, facs : Value) -> Value raise {
  let h = pdegreevector(poly)
  if member_equal(Fix(1L), h).truthy() || member_equal(Fix(2L), h).truthy() {
    return list1(poly)
  }
  if facs is Nil {
    return list1(poly)
  }
  let h = pgcd(poly, car(facs))
  if atom(h) {
    heurtrial1(poly, cdr(facs))
  } else {
    let j = pquotient(poly, h)
    if atom(j) {
      heurtrial1(poly, cdr(facs))
    } else {
      heurtrial(list2(h, j), cdr(facs))
    }
  }
}

///|
fn heurtrial(x : Value, facs : Value) -> Value raise {
  if x is Nil {
    Nil
  } else {
    let a = heurtrial1(car(x), facs)
    nconc(a, heurtrial(cdr(x), facs))
  }
}

///|
fn pfactorquad(p : Value) -> Value raise {
  let bs = bind_all([(q_d_dontfactor, Nil), (q_v, Nil)])
  defer unbind_all(bs)
  if onevarp(p).truthy() || equal(symval(q_modulus), Fix(2L)) {
    return list1(p)
  }
  let mut l = pdegreevector(p)
  if !member_equal(Fix(2L), l).truthy() {
    return list1(p)
  }
  // FIND MOST MAIN VAR
  l = nreverse(l)
  set(q_v, reverse(symval(q_genvar))) |> ignore
  while true {
    if equal(car(l), Fix(2L)) {
      set(q_v, car(symval(q_v))) |> ignore
      break
    } else {
      l = cdr(l)
      set(q_v, cdr(symval(q_v))) |> ignore
    }
  }
  let v = symval(q_v)
  let r = bothprodcoef(list3(v, Fix(2L), Fix(1L)), p)
  let a = car(r)
  let mut c = cdr(r)
  let r = bothprodcoef(list3(v, Fix(1L), Fix(1L)), c)
  let b = car(r)
  c = cdr(r)
  let mut d = pgcd(pgcd(a, b), c)
  if !atom(d) {
    set(q_n_starirreds, nconc(symval(q_n_starirreds), pfactor1(d))) |> ignore
    return pfactorquad(pquotient(p, d))
  }
  d = pplus(pexpt(b, Fix(2L)), ptimes(Fix(-4L), ptimes(a, c)))
  c = pnthrootp(d, Fix(2L))
  if c.truthy() {
    d = ratreduce(pplus(b, c), ptimes(Fix(2L), a))
    d = pabs(pplus(ptimes(make_poly(symval(q_v)), cdr(d)), car(d)))
    set(
      q_n_starirreds,
      nconc(symval(q_n_starirreds), list2(d, pquotient(p, d))),
    )
    |> ignore
    Nil
  } else if symval(q_modulus).truthy() {
    // NEED TO TAKE SQRT(INT. MOD P) LCF.
    list1(p)
  } else {
    set(q_n_starirreds, nconc(symval(q_n_starirreds), list1(p))) |> ignore
    Nil
  }
}

///|
fn d_isqrt(x : Value) -> Value raise {
  d_inrt(x, Fix(2L))
}

///|
fn d_inrt(x : Value, n : Value) -> Value raise {
  let x = mratcheck(x)
  if !integerp(x) {
    if equal(n, Fix(2L)) {
      list2(list1(q_d_isqrt), x)
    } else {
      list3(list1(q_d_inrt), x, n)
    }
  } else if zerop(x) {
    x
  } else {
    let n = mratcheck(n)
    if !integerp(n) {
      list3(list1(q_d_inrt), x, n)
    } else {
      car(iroot(num_abs(x), n))
    }
  }
}

///|
/// Computes a^(1/n); see Fitch, SIGSAM Bull Nov 74.
fn iroot(a : Value, n : Value) -> Value raise {
  if ratmac__lt(int(integer_length(a)), n) {
    list2(Fix(1L), num_sub(a, Fix(1L)))
  } else {
    // assumes integer a>0 n>=2
    let mut x = expt(
      Fix(2L),
      num_add(Fix(1L), num_truncate(int(integer_length(a)), b=n).0),
    )
    let n1 = num_sub(n, Fix(1L))
    while true {
      let xn = expt(x, n1)
      let bk = num_sub(x, num_truncate(a, b=xn).0)
      if !plusp(bk) {
        return list2(x, num_sub(a, num_mul(x, xn)))
      }
      x = num_sub(x, num_truncate(num_add(n1, bk), b=n).0)
    }
    Nil
  }
}

///|
fn d_nthroot(p : Value, n : Value) -> Value raise {
  if integerp(n) && plusp(n) {
    let r = d_rat(p, Nil)
    if eql(cddr(r), Fix(1L)) {
      let k = pnthrootp(cadr(r), n)
      if k.truthy() {
        pdis(k)
      } else {
        merr("nthroot: ~M is not a ~M power", [p, format(Nil, "~:r", [n])])
      }
    } else {
      merr("nthroot: ~M is not a polynomial", [p])
    }
  } else {
    merr("nthroot: ~M is not a positive integer", [n])
  }
}

///|
fn pnthrootp(p : Value, n : Value) -> Value raise {
  ratmac__ignore_rat_err(() => pnthroot(p, n))
}

///|
fn pnthroot(poly : Value, n : Value) -> Value raise {
  if equal(n, Fix(1L)) {
    poly
  } else if atom(poly) {
    cnthroot(poly, n)
  } else {
    let var2 = car(poly)
    let mut ans = list3(var2, cquotient(cadr(poly), n), pnthroot(caddr(poly), n))
    let ae = cdr(pquotient(pctimes(n, leadterm(poly)), ans))
    let mut p = psimp(var2, cdddr(poly))
    while !ratmac__pz(p) {
      if atom(p) || !eq(car(p), var2) || ratmac__gt(car(ae), cadr(p)) {
        ratmac__rat_error("pnthroot error (should have been caught)") |> ignore
      }
      ans = nconc(ans, ptptquotient(cdr(leadterm(p)), ae))
      p = pdifference(poly, pexpt(ans, n))
    }
    ans
  }
}

///|
fn cnthroot(c : Value, n : Value) -> Value raise {
  if minusp(c) {
    if oddp(n) {
      num_neg(cnthroot(num_neg(c), n))
    } else {
      ratmac__rat_error("cnthroot error (should have been caught)")
    }
  } else if zerop(c) {
    c
  } else {
    let c = iroot(c, n)
    if zerop(cadr(c)) {
      car(c)
    } else {
      ratmac__rat_error("cnthroot error2 (should have been caught)")
    }
  }
}

///|
fn pabs(x : Value) -> Value raise {
  if rat3a__pminusp(x) {
    pminus(x)
  } else {
    x
  }
}

///|
fn pfactorlin(p : Value, l : Value) -> Value raise {
  let b = bind(q_v, symval(q_genvar))
  defer unbind(b)
  let mut degl = l
  while !(degl is Nil) {
    let v = symval(q_v)
    if ratmac__eqn(car(degl), Fix(1L)) && !ratmac__algv(car(v)).truthy() {
      let r = bothprodcoef(make_poly(car(v)), p)
      let a = pgcd(car(r), cdr(r))
      return cons(
        pquotientchk(p, a),
        if equal(a, Fix(1L)) {
          Nil
        } else {
          pfactor1(a)
        },
      )
    }
    degl = cdr(degl)
    set(q_v, cdr(v)) |> ignore
  }
  Nil
}

///|
fn ffactor(l : Value, fn_ : Value) -> Value raise {
  let b = bind(q_ear_alpha, symval(q_ear_alpha))
  defer unbind(b)
  let gauss = symval(q_gauss).truthy()
  if !symval(q_d_factorflag).truthy() && mnump(l).truthy() {
    return l
  } else if atom(l) ||
    symval(q_algfac_star).truthy() ||
    symval(q_modulus).truthy() {
    ()
  } else if !gauss && memq(q_irreducible, cdar(l)).truthy() {
    return l
  } else if gauss && memq(q_irreducibleg, cdar(l)).truthy() {
    return l
  } else if !gauss && memq(q_factored, cdar(l)).truthy() {
    return l
  } else if gauss && memq(q_gfactored, cdar(l)).truthy() {
    return l
  }
  newvar(l) |> ignore
  if symval(q_algfac_star).truthy() {
    set(
      q_varlist,
      cons(
        symval(q_ear_alpha),
        remove_equal(symval(q_ear_alpha), symval(q_varlist)),
      ),
    )
    |> ignore
  }
  let q = ratrep_star(l)
  if symval(q_algfac_star).truthy() {
    set(q_ear_alpha, cadr(ratrep_star(symval(q_ear_alpha)))) |> ignore
    let mp = symval(q_minpoly_star)
    set(q_minpoly_star, subst(car(last(symval(q_genvar))), car(mp), mp))
    |> ignore
  }
  let mut gl = symval(q_genvar)
  let mut vl = symval(q_varlist)
  while gl is Cons(_) && vl is Cons(_) {
    putprop(car(gl), car(vl), q_disrep) |> ignore
    gl = cdr(gl)
    vl = cdr(vl)
  }
  retfactor(cdr(q), fn_, l)
}

///|
fn factorout1(l : Value, p : Value) -> Value raise {
  let mut p = p
  let mut gv = symval(q_genvar)
  let mut dl = l
  let mut ans : Value = Nil
  while !(dl is Nil) {
    if !zerop(car(dl)) {
      ans = cons(pget(car(gv)), cons(car(dl), ans))
      p = pquotient(p, list3(car(gv), car(dl), Fix(1L)))
    }
    gv = cdr(gv)
    dl = cdr(dl)
  }
  list2(ans, p)
}

///|
fn factorout(p : Value) -> Value raise {
  if atom(ptterm(cdr(p), Fix(0L))) && !zerop(ptterm(cdr(p), Fix(0L))) {
    list2(Nil, p)
  } else {
    factorout1(pmindegvec(p), p)
  }
}

///|
fn pfactor(p : Value) -> Value raise {
  let b = bind(q_d_algebraic, symval(q_algfac_star))
  defer unbind(b)
  if atom(p) {
    return cfactor(p)
  }
  if symval(q_d_ratfac).truthy() {
    return pfacprod(p)
  }
  let p = factorout(p)
  if equal(cadr(p), Fix(1L)) {
    car(p)
  } else if numberp(cadr(p)) {
    append(cfactor(cadr(p)), car(p))
  } else {
    let algfac = symval(q_algfac_star).truthy()
    let cont = if symval(q_modulus).truthy() {
      list2(leadalgcoef(cadr(p)), monize(cadr(p)))
    } else if algfac {
      algcontent(cadr(p))
    } else {
      pcontent(cadr(p))
    }
    let first : Value = if equal(car(cont), Fix(1L)) {
      Nil
    } else if algfac {
      if symval(q_modulus).truthy() {
        list2(car(cont), Fix(1L))
      } else if equal(car(cont), cons(Fix(1L), Fix(1L))) {
        Nil
      } else {
        let mut num = caar(cont)
        let den = cdar(cont)
        let minus = rat3a__pminusp(num)
        if minus {
          num = pminus(num)
        }
        append_n([
          if minus {
            list2(Fix(-1L), Fix(1L))
          } else {
            Nil
          },
          if !equal(num, Fix(1L)) {
            list2(num, Fix(1L))
          } else {
            Nil
          },
          if !equal(den, Fix(1L)) {
            list2(den, Fix(-1L))
          } else {
            Nil
          },
        ])
      }
    } else {
      cfactor(car(cont))
    }
    let second = pfactor11(psqfr(cadr(cont)))
    nconc_n([first, second, car(p)])
  }
}

///|
fn pfactor11(p : Value) -> Value raise {
  if p is Nil {
    Nil
  } else if numberp(car(p)) {
    cons(car(p), cons(cadr(p), pfactor11(cddr(p))))
  } else {
    with_special(q_adn_star, Fix(1L), () => {
      let f = pfactor1(car(p))
      let first : Value = if equal(symval(q_adn_star), Fix(1L)) {
        Nil
      } else {
        list2(symval(q_adn_star), num_neg(cadr(p)))
      }
      let mut l = f
      let mut ans : Value = Nil
      while !(l is Nil) {
        ans = cons(car(l), cons(cadr(p), ans))
        l = cdr(l)
      }
      let rest = pfactor11(cddr(p))
      nconc_n([first, ans, rest])
    })
  }
}

///|
/// PFACTOR1: factor P, which is assumed square-free.
fn pfactor1(p : Value) -> Value raise {
  let bs = bind_all([(q_n_starirreds, Nil), (q_n_starcheckagain, Nil)])
  defer unbind_all(bs)
  let mut factors : Value = Nil
  let mut goto_out = false
  if dontfactor(car(p)).truthy() {
    return list1(p)
  }
  let fmd = symval(q_d_factor_max_degree)
  if !zerop(fmd) &&
    ratmac__gt(reduce((a, b) => num_max(a, b), pdegreevector(p)), fmd) {
    if symval(q_d_factor_max_degree_print_warning).truthy() {
      mtell(
        list([
          Str(
            "Refusing to factor polynomial ~M because its degree exceeds factor_max_degree (~M)~%",
          ),
          pdis(p),
          fmd,
        ]),
      )
      |> ignore
    }
    return list1(p)
  }
  if onevarp(p).truthy() {
    factors = factxn_plus_1(p)
    if factors.truthy() {
      if !symval(q_modulus).truthy() &&
        (symval(q_gauss).truthy() || !symval(q_algfac_star).truthy()) {
        set(q_n_starirreds, factors) |> ignore
        factors = Nil
      }
      goto_out = true
    } else if !symval(q_algfac_star).truthy() &&
      !symval(q_modulus).truthy() &&
      !equal(cadr(p), Fix(2L)) &&
      estcheck(cdr(p)).truthy() {
      return list1(p)
    }
  }
  if !goto_out {
    factors = pfactorlin(p, pdegreevector(p))
    if factors.truthy() {
      return factors
    }
    // SQRT(NUM. CONT OF DISC)
    factors = if symval(q_algfac_star).truthy() || symval(q_modulus).truthy() {
      list1(p)
    } else {
      pfactorquad(p)
    }
    if !(factors is Nil) {
      if symval(q_ear_checkfactors).truthy() {
        factors = heurtrial(factors, symval(q_ear_checkfactors))
        set(q_n_starcheckagain, cdr(factors)) |> ignore
      }
    }
  }
  let irreds = symval(q_n_starirreds)
  nconc(irreds, mapcan(x => pfactorany(x), factors))
}

///|
fn pfactorany(p : Value) -> Value raise {
  if symval(q_n_starcheckagain).truthy() {
    with_special(q_ear_checkfactors, Nil, () => pfactor1(p))
  } else if symval(q_d_homog_hack).truthy() &&
    !symval(q_algfac_star).truthy() &&
    !onevarp(p).truthy() {
    with_specials(
      [(q_d_homog_hack, Nil), (q_n_starhvar, Nil), (q_n_starhmat, Nil)],
      () => mapcar(x => hexpand(x), pfactor(hreduce(p))),
    )
  } else if symval(q_d_berlefact).truthy() {
    factor1972(p)
  } else {
    pkroneck(p)
  }
}

///|
fn retfactor(x : Value, fn_ : Value, l : Value) -> Value raise {
  let mut a = ratfact(x, fn_)
  while true {
    if cddr(a) is Nil {
      a = retfactor1(car(a), cadr(a))
      return if symval(q_scanmapp).truthy() &&
        !atom(a) &&
        !atom(l) &&
        eq(caar(a), caar(l)) {
        tagirr(l)
      } else {
        a
      }
    } else if equal(car(a), Fix(1L)) {
      a = cddr(a)
    } else {
      a = map2c(q_retfactor1, a)
      if member(Fix(0L), a).truthy() {
        return Fix(0L)
      }
      a = with_specials(
        [(q_d_expop, Fix(0L)), (q_d_expon, Fix(0L)), (q_d_negdistrib, Nil)],
        () => muln(sortgreat(a), t),
      )
      return if !mtimesp(a).truthy() {
        a
      } else {
        cons(list3(q_mtimes, q_simp, q_factored), cdr(a))
      }
    }
  }
  Nil
}

///|
/// FOR LISTS OF ARBITRARY EXPRESSIONS
fn retfactor1(p : Value, e : Value) -> Value raise {
  power(tagirr(simplify(pdisrep(p))), e)
}

///|
fn tagirr(x : Value) -> Value raise {
  if atom(x) || memq(q_irreducible, cdar(x)).truthy() {
    x
  } else {
    cons(append(car(x), list1(q_irreducible)), cdr(x))
  }
}

///|
fn revsign(x : Value) -> Value raise {
  if x is Nil {
    Nil
  } else {
    cons(car(x), cons(num_neg(cadr(x)), revsign(cddr(x))))
  }
}
