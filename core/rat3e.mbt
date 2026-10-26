// Port of src/rat3e.lisp: the rational function package, part 5.
// The conversion and top-level routines (rat, ratsimp, ratdisrep, factor,
// gcd, divide, ...) used by the rest of the functions.

///|
fn mrateval(x : Value) -> Value raise {
  with_special(q_varlist, caddar(x), () => {
    let varlist = symval(q_varlist)
    if symval(q_evp).truthy() && symval(q_d_infeval).truthy() {
      meval(d_ratdisrep(x))
    } else if symval(q_evp).truthy() ||
      (symval(q_d_float).truthy() && symval(q_d_keepfloat).truthy()) ||
      !alike(varlist, mapcar(v => meval(v), varlist)).truthy() {
      ratf(meval(d_ratdisrep(x)))
    } else {
      x
    }
  })
}

///|
fn d_ratnumer(x : Value) -> Value raise {
  if mbagp(x).truthy() {
    cons(car(x), mapcar(e => d_ratnumer(e), cdr(x)))
  } else {
    let x = taychk2rat(x)
    cons(car(x), cons(cadr(x), Fix(1L)))
  }
}

///|
fn d_ratdenom(x : Value) -> Value raise {
  if mbagp(x).truthy() {
    cons(car(x), mapcar(e => d_ratdenom(e), cdr(x)))
  } else {
    let x = taychk2rat(x)
    cons(car(x), cons(cddr(x), Fix(1L)))
  }
}

///|
fn taychk2rat(x : Value) -> Value raise {
  if d_ratp(x).truthy() && memq(q_trunc, cdar(x)).truthy() {
    d_taytorat(x)
  } else {
    d_rat(x, Nil)
  }
}

///|
fn tellratdisp(x : Value) -> Value raise {
  pdisrep_plus(trdisp1(cdr(x), car(x)))
}

///|
fn trdisp1(p : Value, var_ : Value) -> Value raise {
  if p is Nil {
    Nil
  } else {
    cons(
      pdisrep_star(
        // prevents clobbering p
        if mtimesp(cadr(p)).truthy() {
          copy_list(cadr(p))
        } else {
          cadr(p)
        },
        pdisrep_bang(car(p), var_),
      ),
      trdisp1(cddr(p), var_),
    )
  }
}

///|
fn d_untellrat(args : Value) -> Value raise {
  for x in args.iter() {
    let x = assol(x, symval(q_tellratlist))
    if x.truthy() {
      set(q_tellratlist, remove_equal(x, symval(q_tellratlist))) |> ignore
    }
  }
  cons(list1(q_mlist), mapcar(x => tellratdisp(x), symval(q_tellratlist)))
}

///|
fn d_tellrat(args : Value) -> Value raise {
  // Through the function cell: share/affine/new-rat.lisp redefines TELLRAT1.
  mapc(x => funcall(q_tellrat1, [x]) |> ignore, args) |> ignore
  if !(args is Nil) {
    add2lnc(q_tellratlist, symval(q_d_myoptions)) |> ignore
  }
  cons(list1(q_mlist), mapcar(x => tellratdisp(x), symval(q_tellratlist)))
}

///|
fn tellrat1(x : Value) -> Value raise {
  let bs = bind_all([
    (q_varlist, Nil),
    (q_genvar, Nil),
    (q_d_algebraic, Nil),
    (q_d_ratfac, Nil),
  ])
  defer unbind_all(bs)
  let mut x = d_totaldisrep(x)
  if !atom(x) && eq(caar(x), q_mequal) {
    newvar(cadr(x)) |> ignore
  }
  x = meqhk(x)
  newvar(x) |> ignore
  if symval(q_varlist) is Nil {
    merr("tellrat: argument must be a polynomial; found: ~M", [x]) |> ignore
  }
  let mut algvar = car(last(symval(q_varlist)))
  x = cdr(primpart(cadr(ratrep_star(x))))
  if !equal(cadr(x), Fix(1L)) {
    merr("tellrat: minimal polynomial must be monic.", []) |> ignore
  }
  let mut p = cddr(x)
  while !(p is Nil) {
    rplaca(cdr(p), pdis(cadr(p))) |> ignore
    p = cddr(p)
  }
  algvar = cons(algvar, x)
  x = assol(car(algvar), symval(q_tellratlist))
  if x.truthy() {
    set(q_tellratlist, remove_equal(x, symval(q_tellratlist))) |> ignore
  }
  set(q_tellratlist, cons(algvar, symval(q_tellratlist)))
}

///|
fn d_printvarlist() -> Value raise {
  cons(list1(q_mlist), copy_tree(symval(q_varlist)))
}

///|
fn d_showratvars(e : Value) -> Value raise {
  cons(
    list2(q_mlist, q_simp),
    if d_ratp(e).truthy() {
      let e = if memq(q_trunc, cdar(e)).truthy() { d_taytorat(e) } else { e }
      caddar(minimize_varlist(e))
    } else {
      with_special(q_varlist, Nil, () => {
        lnewvar(e) |> ignore
        symval(q_varlist)
      })
    },
  )
}

///|
fn d_ratvars(args : Value) -> Value raise {
  add2lnc(q_d_ratvars, symval(q_d_myoptions)) |> ignore
  let vl = mapfr1(args, symval(q_varlist))
  set(q_varlist, vl) |> ignore
  set(q_d_ratvars, cons(list2(q_mlist, q_simp), vl))
}

///|
fn mapfr1(l : Value, varlist : Value) -> Value raise {
  with_special(q_varlist, varlist, () => mapcar(
    z => fr1(z, symval(q_varlist)),
    l,
  ))
}

///|
fn d_fullratsimp(exp_ : Value, argl : Value) -> Value raise {
  let mut exp_ = exp_
  while true {
    let exp1 = simplify(d_ratsimp(exp_, argl))
    if alike1(exp_, exp1).truthy() {
      return exp_
    }
    exp_ = exp1
  }
  Nil
}

///|
fn fullratsimp(l : Value) -> Value raise {
  with_specials(
    [
      (q_d_expop, Fix(0L)),
      (q_d_expon, Fix(0L)),
      (q_inratsimp, t),
      (q_d_ratsimpexpons, Nil),
    ],
    () => {
      let mut l = l
      if !d_ratp(l).truthy() {
        // Not a mrat expression. Remove the special representation.
        l = specrepcheck(l)
      }
      l = d_totaldisrep(l)
      fr1(l, symval(q_varlist))
    },
  )
}

///|
fn d_totaldisrep(l : Value) -> Value raise {
  if atom(l) {
    l
  } else if !among(q_mrat, l).truthy() {
    l
  } else if eq(caar(l), q_mrat) {
    ratdisrep(l)
  } else {
    cons(delete(q_ratsimp, car(l)), mapcar(x => d_totaldisrep(x), cdr(l)))
  }
}

// VARLIST HAS MAIN VARIABLE AT END

///|
fn joinvarlist(cdrl : Value) -> Value raise {
  mapc(
    z => if !memalike(z, symval(q_varlist)).truthy() {
      set(q_varlist, cons(z, symval(q_varlist))) |> ignore
    },
    reverse(mapfr1(cdrl, Nil)),
  )
}

///|
fn d_rat(e : Value, vars : Value) -> Value raise {
  if !(vars is Nil) {
    with_special(q_varlist, Nil, () => {
      joinvarlist(vars) |> ignore
      lnewvar(e) |> ignore
      rat0(e)
    })
  } else {
    lnewvar(e) |> ignore
    rat0(e)
  }
}

///|
fn rat0(exp_ : Value) -> Value raise {
  if mbagp(exp_).truthy() {
    cons(car(exp_), mapcar(x => rat0(x), cdr(exp_)))
  } else {
    ratf(exp_)
  }
}

///|
fn d_ratsimp(e : Value, vars : Value) -> Value raise {
  if !(vars is Nil) {
    with_special(q_varlist, Nil, () => {
      joinvarlist(vars) |> ignore
      fullratsimp(e)
    })
  } else {
    fullratsimp(e)
  }
}

///|
/// PSQFR HAS NOT BEEN CHANGED TO MAKE USE OF THE SQFR FLAGS YET
fn d_sqfr(x : Value) -> Value raise {
  with_specials(
    [
      (q_varlist, cdr(symval(q_d_ratvars))),
      (q_genvar, Nil),
      (q_d_keepfloat, Nil),
      (q_d_ratfac, Nil),
    ],
    () => sublis(
      list2(cons(q_factored, q_sqfred), cons(q_irreducible, q_sqfr)),
      ffactor(x, q_psqfr),
    ),
  )
}

///|
fn whichfn(p : Value) -> Value raise {
  if mexptp(p).truthy() && integerp(caddr(p)) {
    list3(list1(q_mexpt), whichfn(cadr(p)), caddr(p))
  } else if mtimesp(p).truthy() {
    cons(list1(q_mtimes), mapcar(x => whichfn(x), cdr(p)))
  } else if symval(q_fn).truthy() {
    ffactor(p, q_pfactor)
  } else {
    factoralg(p)
  }
}

///|
fn factoralg(p : Value) -> Value raise {
  let bs = bind_all([
    (q_alc, Nil),
    (q_ans, Nil),
    (q_adn_star, Nil),
    (q_d_gcd, Nil),
  ])
  defer unbind_all(bs)
  set(q_d_gcd, q_d_algebraic) |> ignore
  if atom(p) || numberp(p) {
    return p
  }
  set(q_adn_star, Fix(1L)) |> ignore
  if !symval(q_d_nalgfac).truthy() && !symval(q_intbs_star).truthy() {
    set(q_intbs_star, findibase(symval(q_minpoly_star))) |> ignore
  }
  set(q_algfac_star, t) |> ignore
  set(q_ans, ffactor(p, q_pfactor)) |> ignore
  if eq(caar(symval(q_ans)), q_mplus) {
    return p
  } else if symval(q_mplc_star).truthy() {
    set(q_ans, albk(symval(q_ans))) |> ignore
  }
  if !symval(q_alc).truthy() && equal(Fix(1L), symval(q_adn_star)) {
    return symval(q_ans)
  }
  set(q_ans, partition(symval(q_ans), car(last(symval(q_varlist))), Fix(1L)))
  |> ignore
  let ans = symval(q_ans)
  let f = with_special(q_dosimp, t, () => muln_([
    mk(q_rat, [Fix(1L), symval(q_adn_star)]),
    car(ans),
    if symval(q_alc).truthy() {
      pdis(symval(q_alc))
    } else {
      Fix(1L)
    },
  ]))
  muln_([f, cdr(ans)])
}

///|
/// To undo the monicizing substitution.
fn albk(p : Value) -> Value raise {
  let alpha = pdis(symval(q_ear_alpha))
  // don't multiply them back out
  with_specials([(q_ear_alpha, alpha), (q_d_ratfac, t)], () => maxima_substitute(
    list3(list2(q_mtimes, q_simp), symval(q_mplc_star), symval(q_ear_alpha)),
    symval(q_ear_alpha),
    p,
  ))
}

///|
fn d_gfactor(p : Value) -> Value raise {
  with_special(q_gauss, t, () => {
    let mut p = p
    if d_ratp(p).truthy() {
      p = d_ratdisrep(p)
    }
    p = d_factor(
      subst(q_p_i, q_d__pcti, p),
      mp=mk(q_mplus, [Fix(1L), mk(q_mexpt, [q_p_i, Fix(2L)])]),
    )
    p = sublis(
      list2(cons(q_factored, q_gfactored), cons(q_irreducible, q_irreducibleg)),
      p,
    )
    with_specials(
      [(q_d_expop, Fix(0L)), (q_d_expon, Fix(0L)), (q_d_negdistrib, Nil)],
      () => maxima_substitute(q_d__pcti, q_p_i, p),
    )
  })
}

///|
fn d_factor(e : Value, mp? : Value) -> Value raise {
  with_specials(
    [
      (q_d_intfaclim, Nil),
      (q_varlist, cdr(symval(q_d_ratvars))),
      (q_genvar, Nil),
      (q_ans, Nil),
    ],
    () => {
      set(q_ans, factor(e, mp?)) |> ignore
      let ans = symval(q_ans)
      if symval(q_factorresimp).truthy() &&
        symval(q_d_negdistrib).truthy() &&
        mtimesp(ans).truthy() &&
        cdddr(ans) is Nil &&
        equal(cadr(ans), Fix(-1L)) &&
        mplusp(caddr(ans)).truthy() {
        with_specials([(q_d_expop, Fix(0L)), (q_d_expon, Fix(0L))], () => d_multthru(
          ans,
        ))
      } else {
        ans
      }
    },
  )
}

///|
fn factor(e : Value, mp? : Value) -> Value raise {
  let bs1 = bind_all([
    (q_tellratlist, Nil),
    (q_varlist, symval(q_varlist)),
    (q_genvar, Nil),
    (q_d_gcd, symval(q_d_gcd)),
    (q_d_negdistrib, symval(q_d_negdistrib)),
  ])
  defer unbind_all(bs1)
  let bs2 = bind_all([
    (q_fn, Nil),
    (q_var, Nil),
    (q_mm_star, Nil),
    (q_mplc_star, Nil),
    (q_intbs_star, Nil),
    (q_alflag, Nil),
    (q_minpoly_star, Nil),
    (q_ear_alpha, Nil),
    (q_algfac_star, Nil),
    (q_d_keepfloat, Nil),
    (q_d_algebraic, Nil),
    (q_cargs, Nil),
  ])
  defer unbind_all(bs2)
  if memq(symval(q_d_gcd), symval(q_ear_gcdl)) is Nil {
    set(q_d_gcd, car(symval(q_ear_gcdl))) |> ignore
  }
  let mut p : Value = Nil
  {
    let b = bind(q_d_ratfac, Nil)
    defer unbind(b)
    p = e
    set(q_mm_star, Fix(1L)) |> ignore
    set(
      q_cargs,
      match mp {
        Some(m) => list1(m)
        None => Nil
      },
    )
    |> ignore
    if symbolp(p) {
      return p
    }
    if d_numberp(p).truthy() {
      return with_special(
        q_d_factorflag,
        lbool(!symval(q_scanmapp).truthy()),
        () => factornumber(p),
      )
    }
    if mbagp(p).truthy() {
      let p0 = p
      return cons(
        car(p0),
        mapcar(
          x => {
            let cargs = symval(q_cargs)
            if cargs is Nil {
              factor(x)
            } else {
              factor(x, mp=car(cargs))
            }
          },
          cdr(p0),
        ),
      )
    }
    match mp {
      Some(mpv) => {
        set(q_ear_alpha, meqhk(mpv)) |> ignore
        newvar(symval(q_ear_alpha)) |> ignore
        set(q_minpoly_star, cadr(ratrep_star(symval(q_ear_alpha)))) |> ignore
        let minpoly = symval(q_minpoly_star)
        let bad = atom(minpoly) ||
          !univar(cdr(minpoly)).truthy() ||
          ratmac__lt(cadr(minpoly), Fix(2L)) || {
            // Detect a reducible polynomial: factor MINPOLY* with GAUSS = NIL,
            // skip over the content and see if there is more than one factor
            // or the single factor has a multiplicity > 1.
            let pfac = with_special(q_gauss, Nil, () => pfactor(minpoly))
            let facs = if atom(car(pfac)) { cddr(pfac) } else { pfac }
            cddr(facs).truthy() || ratmac__gt(cadr(facs), Fix(1L))
          }
        if bad {
          merr(
            "factor: second argument must be an irreducible, nonlinear, univariate polynomial; found: ~M",
            [symval(q_ear_alpha)],
          )
          |> ignore
        }
        let minpoly = symval(q_minpoly_star)
        set(q_ear_alpha, pdis(list3(car(minpoly), Fix(1L), Fix(1L)))) |> ignore
        set(q_mm_star, cadr(minpoly)) |> ignore
        if !equal(caddr(minpoly), Fix(1L)) {
          set(q_mplc_star, caddr(minpoly)) |> ignore
          set(q_minpoly_star, pmonz(minpoly)) |> ignore
          p = maxima_substitute(
            div(symval(q_ear_alpha), symval(q_mplc_star)),
            symval(q_ear_alpha),
            p,
          )
        }
        set(q_d_algebraic, t) |> ignore
        d_tellrat(list1(pdis(symval(q_minpoly_star)))) |> ignore
        set(q_algfac_star, t) |> ignore
      }
      None => set(q_fn, t) |> ignore
    }
    if !symval(q_scanmapp).truthy() {
      let p0 = p
      p = with_special(q_d_ratfac, t, () => sratsimp(p0))
    }
    newvar(p) |> ignore
    if symbolp(p) {
      return p
    }
    if numberp(p) {
      let p0 = p
      return with_special(
        q_d_factorflag,
        lbool(!symval(q_scanmapp).truthy()),
        () => factornumber(p0),
      )
    }
    set(q_d_negdistrib, Nil) |> ignore
    let p0 = p
    p = with_specials(
      [(q_d_factorflag, Nil), (q_d_ratexpand, symval(q_d_facexpand))],
      () => whichfn(p0),
    )
  }
  let p0 = p
  p = with_specials([(q_d_expop, Fix(0L)), (q_d_expon, Fix(0L))], () => simplify(
    p0,
  ))
  if mnump(p).truthy() {
    return factornumber(p)
  } else if atom(p) {
    return p
  }
  if symval(q_d_ratfac).truthy() &&
    !symval(q_d_factorflag).truthy() &&
    d_ratp(e).truthy() {
    return d_rat(p, Nil)
  }
  if symval(q_d_factorflag).truthy() &&
    mtimesp(p).truthy() &&
    mnump(cadr(p)).truthy() {
    set(q_ear_alpha, factornumber(cadr(p))) |> ignore
    let alpha = symval(q_ear_alpha)
    if alpha.truthy() {
      if alike1(alpha, cadr(p)).truthy() {
        ()
      } else if mtimesp(alpha).truthy() {
        p = cons(car(p), append(cdr(alpha), cddr(p)))
      } else {
        p = cons(car(p), cons(alpha, cddr(p)))
      }
    }
  }
  if memq(q_factored, car(p)) is Nil {
    p = cons(append(car(p), list1(q_factored)), cdr(p))
  }
  p
}

///|
fn factornumber(n : Value) -> Value raise {
  let n = nretfactor1(nratfact(cdr(d_rat(n, Nil))))
  if cdr(n).truthy() {
    cons(
      list3(q_mtimes, q_simp, q_factored),
      if equal(car(n), Fix(-1L)) {
        cons(car(n), nreverse(cdr(n)))
      } else {
        nreverse(n)
      },
    )
  } else if atom(car(n)) {
    car(n)
  } else {
    cons(cons(caaar(n), list2(q_simp, q_factored)), cdar(n))
  }
}

///|
fn nratfact(x : Value) -> Value raise {
  if equal(cdr(x), Fix(1L)) {
    cfactor(car(x))
  } else if equal(car(x), Fix(1L)) {
    revsign(cfactor(cdr(x)))
  } else {
    let a = cfactor(car(x))
    nconc(a, revsign(cfactor(cdr(x))))
  }
}

///|
/// FOR LISTS OF JUST NUMBERS
fn nretfactor1(l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else if equal(cadr(l), Fix(1L)) {
    cons(car(l), nretfactor1(cddr(l)))
  } else {
    cons(
      if equal(cadr(l), Fix(-1L)) {
        list3(list2(q_rat, q_simp), Fix(1L), car(l))
      } else {
        list3(list2(q_mexpt, q_simp), car(l), cadr(l))
      },
      nretfactor1(cddr(l)),
    )
  }
}

///|
fn d_polymod(p : Value, m? : Value) -> Value raise {
  with_special(q_modulus, symval(q_modulus), () => {
    match m {
      Some(m) => {
        set(q_modulus, m) |> ignore
        let md = symval(q_modulus)
        if !integerp(md) || zerop(md) {
          merr("polymod: modulus must be a nonzero integer; found: ~M", [md])
          |> ignore
        }
      }
      None => ()
    }
    if minusp(symval(q_modulus)) {
      set(q_modulus, num_abs(symval(q_modulus))) |> ignore
    }
    mod1(p)
  })
}

///|
fn mod1(e : Value) -> Value raise {
  if mbagp(e).truthy() {
    cons(car(e), mapcar(x => mod1(x), cdr(e)))
  } else {
    newvar(e) |> ignore
    let formflag = d_ratp(e).truthy()
    let e = ratrep_star(e)
    let e = cons(car(e), ratreduce(pmod(cadr(e)), pmod(cddr(e))))
    if formflag {
      e
    } else {
      ratdisrep(e)
    }
  }
}

///|
fn d_divide(x : Value, y : Value, vars : Value) -> Value raise {
  let bs = bind_all([(q_varlist, Nil), (q_d_ratfac, Nil)])
  defer unbind_all(bs)
  let mut x = x
  let mut y = y
  let mut formflag = false
  if d_ratp(x).truthy() {
    formflag = true
    if integerp(cadr(x)) && equal(cddr(x), Fix(1L)) {
      x = cadr(x)
    }
  }
  if d_ratp(y).truthy() {
    formflag = true
    if integerp(cadr(y)) && equal(cddr(y), Fix(1L)) {
      y = cadr(y)
    }
  }
  if integerp(x) && integerp(y) {
    if zerop(y) {
      merr("divide: Quotient by zero", []) |> ignore
    }
    let (q, r) = num_truncate(x, b=y)
    return list3(list1(q_mlist), q, r)
  }
  set(q_varlist, vars) |> ignore
  mapc(v => newvar(v) |> ignore, reverse(cdr(symval(q_d_ratvars)))) |> ignore
  newvar(y) |> ignore
  newvar(x) |> ignore
  x = ratrep_star(x)
  let mut h = car(x)
  x = cdr(x)
  y = cdr(ratrep_star(y))
  let tt = cdr(x)
  if equal(tt, Fix(1L)) && equal(cdr(y), Fix(1L)) {
    x = pdivide(car(x), car(y))
  } else {
    let ty = cdr(y)
    x = ptimes(car(x), cdr(y))
    x = pdivide(x, car(y))
    x = list2(ratqu(car(x), tt), ratqu(cadr(x), ptimes(tt, ty)))
  }
  h = list3(list1(q_mlist), cons(h, car(x)), cons(h, cadr(x)))
  if formflag {
    h
  } else {
    d_totaldisrep(h)
  }
}

///|
fn d_quotient(args : Value) -> Value raise {
  cadr(apply(q_d_divide, args))
}

///|
fn d_remainder(args : Value) -> Value raise {
  caddr(apply(q_d_divide, args))
}

///|
fn d_gcd(x : Value, y : Value, vars : Value) -> Value raise {
  let bs = bind_all([(q_varlist, Nil), (q_genvar, Nil), (q_d_keepfloat, Nil)])
  defer unbind_all(bs)
  let mut x = x
  let mut y = y
  let mut h : Value = Nil
  let mut formflag = d_ratp(x).truthy()
  if d_ratp(y).truthy() {
    formflag = true
  }
  set(q_varlist, vars) |> ignore
  for v in symval(q_varlist).iter() {
    if numberp(v) {
      improper_arg_err(v, q_d_gcd) |> ignore
    }
  }
  newvar(x) |> ignore
  newvar(y) |> ignore
  if d_ratp(x).truthy() && d_ratp(y).truthy() && equal(car(x), car(y)) {
    set(q_genvar, car(last(car(x)))) |> ignore
    h = car(x)
    x = cdr(x)
    y = cdr(y)
  } else {
    x = ratrep_star(x)
    h = car(x)
    x = cdr(x)
    y = cdr(ratrep_star(y))
  }
  x = cons(pgcd(car(x), car(y)), plcm(cdr(x), cdr(y)))
  h = cons(h, x)
  if formflag {
    h
  } else {
    ratdisrep(h)
  }
}

///|
fn d_content(x : Value, vars : Value) -> Value raise {
  let b = bind(q_varlist, Nil)
  defer unbind(b)
  let formflag = d_ratp(x).truthy()
  set(q_varlist, vars) |> ignore
  newvar(x) |> ignore
  let r = ratrep_star(x)
  let mut h = car(r)
  let mut x = cadr(r)
  let mut y = cddr(r)
  if !atom(x) {
    // (CAR X) => gensym corresponding to apparent main var.
    // MAIN-GENVAR => gensym corresponding to the genuine main var.
    let main_genvar = nth(length(symval(q_varlist)) - 1, symval(q_genvar))
    if !eq(car(x), main_genvar) {
      x = list3(main_genvar, Fix(0L), x)
    }
  }
  x = rcontent(x)
  y = cons(Fix(1L), y)
  h = list3(
    list1(q_mlist),
    cons(h, rattimes(car(x), y, Nil)),
    cons(h, cadr(x)),
  )
  if formflag {
    h
  } else {
    d_totaldisrep(h)
  }
}

///|
fn pget(gen : Value) -> Value raise {
  cons(gen, list2(Fix(1L), Fix(1L)))
}

///|
fn m_dolexp_q(x : Value) -> Value raise {
  lbool(mexptp(x).truthy() && eq(cadr(x), q_d__pcte))
}

///|
fn algp(d_x : Value) -> Value raise {
  with_special(q_d_x, d_x, () => algpchk(symval(q_d_x), Nil))
}

///|
fn algpget(d_x : Value) -> Value raise {
  with_special(q_d_x, d_x, () => algpchk(symval(q_d_x), t))
}

///|
fn algpchk(d_x : Value, mpflag : Value) -> Value raise {
  let b = bind(q_d_x, d_x)
  defer unbind(b)
  let x = d_x
  if eq(x, q_d__pcti) {
    list2(Fix(2L), Fix(-1L))
  } else if eq(x, q_d__pctphi) {
    list([Fix(2L), Fix(1L), Fix(1L), Fix(-1L), Fix(0L), Fix(-1L)])
  } else if radfunp(x, Nil).truthy() {
    if !mpflag.truthy() {
      t
    } else {
      let r = prep1(cadr(x))
      if onep1(cdr(r)).truthy() {
        // INTEGRAL ALG. QUANT.?
        list2(caddr(caddr(x)), car(r))
      } else if symval(q_ear_ratsimp).truthy() {
        set(q_radlist, cons(x, symval(q_radlist))) |> ignore
        Nil
      } else {
        Nil
      }
    }
  } else if !symval(q_d_algebraic).truthy() {
    Nil
  } else if m_dolexp_q(x).truthy() &&
    mtimesp(caddr(x)).truthy() &&
    equal(cddr(caddr(x)), list2(q_d__pcti, q_d__pctpi)) &&
    ratnump(cadr(caddr(x))).truthy() {
    let temp = cadr(caddr(x))
    if mpflag.truthy() {
      primcyclo(num_mul(Fix(2L), caddr(temp)))
    } else {
      t
    }
  } else if !mpflag.truthy() {
    assolike(x, symval(q_tellratlist))
  } else {
    let mut temp = copy_list(assolike(x, symval(q_tellratlist)))
    if temp is Nil {
      return Nil
    }
    let mut p = temp
    while !(p is Nil) {
      rplaca(cdr(p), car(prep1(cadr(p)))) |> ignore
      p = cddr(p)
    }
    temp = if cddr(temp) is Nil {
      list2(car(temp), Fix(0L))
    } else if zerop(car(cddr(temp))) {
      list2(car(temp), pminus(cadr(cddr(temp))))
    } else {
      temp
    }
    if ratmac__eqn(car(temp), Fix(1L)) {
      set(q_d_x, assol(x, symval(q_genpairs))) |> ignore
      let gx = symval(q_d_x)
      if gx.truthy() {
        rplacd(gx, cons(cadr(temp), Fix(1L))) |> ignore
      }
    }
    temp
  }
}

///|
/// FUNCFLAG -> TEST FOR ALG FUNCTION NOT NUMBER
fn radfunp(x : Value, funcflag : Value) -> Value raise {
  if atom(x) {
    Nil
  } else if !eq(caar(x), q_mexpt) {
    Nil
  } else if !ratnump(caddr(x)).truthy() {
    Nil
  } else if funcflag.truthy() {
    lbool(!numberp(cadr(x)))
  } else {
    t
  }
}

///|
fn ratsetup(vl : Value, gl : Value) -> Value raise {
  ratsetup1(vl, gl) |> ignore
  ratsetup2(vl, gl)
}

///|
fn ratsetup1(vl : Value, gl : Value) -> Value raise {
  if symval(q_d_ratwtlvl).truthy() {
    let mut v = vl
    let mut g = gl
    while v is Cons(_) && g is Cons(_) {
      let w = assolike(car(v), symval(q_n_starratweights))
      if w.truthy() {
        putprop(car(g), w, q_d_ratweight) |> ignore
      } else {
        remprop(car(g), q_d_ratweight) |> ignore
      }
      v = cdr(v)
      g = cdr(g)
    }
    vl
  } else {
    Nil
  }
}

///|
fn ratsetup2(vl : Value, gl : Value) -> Value raise {
  if symval(q_d_algebraic).truthy() {
    mapc(g => remprop(g, q_algord) |> ignore, gl) |> ignore
    let mut v = vl
    let mut lg = gl
    while v is Cons(_) && lg is Cons(_) {
      let a = algpget(car(v))
      if a.truthy() {
        algordset(a, lg) |> ignore
        putprop(car(lg), a, q_tellrat) |> ignore
      } else {
        remprop(car(lg), q_tellrat) |> ignore
      }
      v = cdr(v)
      lg = cdr(lg)
    }
  }
  if symval(q_d_ratfac).truthy() {
    with_special(q_d_ratfac, Nil, () => {
      let mut v = vl
      let mut g = gl
      while v is Cons(_) && g is Cons(_) {
        if mplusp(car(v)).truthy() {
          putprop(car(g), car(prep1(car(v))), q_unhacked) |> ignore
        } else {
          remprop(car(g), q_unhacked) |> ignore
        }
        v = cdr(v)
        g = cdr(g)
      }
      vl
    })
  } else {
    Nil
  }
}

///|
fn porder(p : Value) -> Value raise {
  if atom(p) {
    Fix(0L)
  } else {
    valget(car(p))
  }
}

///|
fn algordset(x : Value, gl : Value) -> Value raise {
  let mut p = x
  let mut mv : Value = Fix(0L)
  while !(p is Nil) {
    mv = num_max(mv, porder(cadr(p)))
    p = cddr(p)
  }
  let mut l = gl
  while !(l is Nil || ratmac__gt(valget(car(l)), mv)) {
    putprop(car(l), t, q_algord) |> ignore
    l = cdr(l)
  }
  Nil
}

///|
/// GENSYM-READABLE: a gensym, named after SYMNAME only in debug mode. The
/// port assumes Maxima's debugger hook is installed (*DEBUGGER-HOOK* non-nil),
/// so readable names are used only when *MDEBUG* is set or
/// *USE-READABLE-GENSYMS* is T.
fn gensym_readable(symname : Value) -> Value raise {
  let urg = symval(q_ear_use_readable_gensyms)
  let debugger_hook = true
  if (eq(urg, q_kw_debug) && !symval(q_ear_mdebug).truthy() && debugger_hook) ||
    !urg.truthy() {
    gensym()
  } else if symbolp(symname) {
    gensym(prefix=string_trim("$", symbol_name(symname)))
  } else {
    let s = aformat(Nil, Str("~:M"), list1(symname))
    match s {
      Str(name) => gensym(prefix=name)
      _ => gensym()
    }
  }
}

///|
fn orderpointer(l : Value) -> Value raise {
  let n = length(l) - length(symval(q_genvar))
  let tem = Collector::new()
  let mut v = l
  let mut i = 0
  while v is Cons(_) && i < n {
    tem.add(gensym_readable(car(v)))
    v = cdr(v)
    i += 1
  }
  set(q_genvar, nconc(tem.result(), symval(q_genvar))) |> ignore
  prenumber(symval(q_genvar), Fix(1L))
}

///|
fn creatsym(n : Value) -> Value raise {
  let cnt = to_int(n)
  for _i in 0..<cnt {
    set(q_genvar, cons(gensym(), symval(q_genvar))) |> ignore
  }
  Nil
}

///|
fn prenumber(v : Value, n : Value) -> Value raise {
  let mut vl = v
  let mut i = n
  while !(vl is Nil) {
    set(car(vl), i) |> ignore
    vl = cdr(vl)
    i = num_add(i, Fix(1L))
  }
  Nil
}

///|
fn rget(genv : Value) -> Value raise {
  let lvl = symval(q_d_ratwtlvl)
  let zero = lvl.truthy() &&
    (fixnump(lvl) ||
    merr("rat: 'ratwtlvl' must be an integer; found: ~M", [lvl]).truthy()) && {
      let w = get(genv, q_d_ratweight)
      ratmac__gt(if w.truthy() { w } else { Fix(-1L) }, lvl)
    }
  cons(if zero { Fix(0L) } else { pget(genv) }, Fix(1L))
}

///|
fn ratrep(x : Value, varl : Value) -> Value raise {
  set(q_varlist, varl) |> ignore
  ratrep_star(x)
}

///|
fn ratrep_star(x : Value) -> Value raise {
  with_special(q_genpairs, Nil, () => {
    orderpointer(symval(q_varlist)) |> ignore
    ratsetup1(symval(q_varlist), symval(q_genvar)) |> ignore
    let mut vl = symval(q_varlist)
    let mut gl = symval(q_genvar)
    while vl is Cons(_) && gl is Cons(_) {
      set(q_genpairs, cons(cons(car(vl), rget(car(gl))), symval(q_genpairs)))
      |> ignore
      vl = cdr(vl)
      gl = cdr(gl)
    }
    ratsetup2(symval(q_varlist), symval(q_genvar)) |> ignore
    // PREP1 changes VARLIST when $RATFAC is T.
    let a = prep1(x)
    let b = list_star([
      q_mrat,
      q_simp,
      symval(q_varlist),
      symval(q_genvar),
      if !atom(x) && memq(q_irreducible, cdar(x)).truthy() {
        list1(q_irreducible)
      } else {
        Nil
      },
    ])
    cons(b, a)
  })
}

///|
fn ratf(l : Value) -> Value raise {
  with_special(q_ear_withinratf, Nil, () => {
    set(q_ear_withinratf, t) |> ignore
    if eq(q_p_op_pct, catch_tag(q_ratf, () => newvar(l))) {
      set(q_ear_withinratf, Nil) |> ignore
      return srf(l)
    }
    // for truncation routines
    let u = catch_tag(q_ratf, () => ratrep_star(l))
    if u.truthy() {
      u
    } else {
      set(q_ear_withinratf, Nil) |> ignore
      srf(l)
    }
  })
}

///|
fn prep1(x : Value) -> Value raise {
  if floatp(x) {
    if symval(q_d_keepfloat).truthy() {
      cons(x, Flo(1.0))
    } else {
      prepfloat(x)
    }
  } else if integerp(x) {
    cons(cmod(x), Fix(1L))
  } else if ratiop(x) {
    if symval(q_modulus) is Nil {
      cons(numerator(x), denominator(x))
    } else {
      cquotient(numerator(x), denominator(x))
    }
  } else if atom(x) {
    let v = assolike(x, symval(q_genpairs))
    if v.truthy() {
      v
    } else {
      newsym(x)
    }
  } else if symval(q_d_ratfac).truthy() &&
    assolike(x, symval(q_genpairs)).truthy() {
    assolike(x, symval(q_genpairs))
  } else if eq(caar(x), q_mplus) {
    if symval(q_d_ratfac).truthy() {
      let x = mapcar(y => prep1(y), cdr(x))
      if every(y => frpoly_q(y).truthy(), x) {
        let mut l = x
        while l is Cons(_) {
          rplaca(l, caar(l)) |> ignore
          l = cdr(l)
        }
        cons(mfacpplus(x), Fix(1L))
      } else {
        let mut a = car(x)
        let mut l = cdr(x)
        while !(l is Nil) {
          a = facrplus(a, car(l))
          l = cdr(l)
        }
        a
      }
    } else {
      let mut a = prep1(cadr(x))
      let mut l = cddr(x)
      while !(l is Nil) {
        a = ratplus(a, prep1(car(l)))
        l = cdr(l)
      }
      a
    }
  } else if eq(caar(x), q_mtimes) {
    let sw = lbool(
      !(symval(q_d_norepeat).truthy() && memq(q_ratsimp, cdar(x)).truthy()),
    )
    let mut a = savefactors(prep1(cadr(x)))
    let mut l = cddr(x)
    while !(l is Nil) {
      a = rattimes(a, savefactors(prep1(car(l))), sw)
      l = cdr(l)
    }
    a
  } else if eq(caar(x), q_mexpt) {
    newvarmexpt(x, caddr(x), t)
  } else if eq(caar(x), q_mquotient) {
    let a = savefactors(prep1(cadr(x)))
    ratquotient(a, savefactors(prep1(caddr(x))))
  } else if eq(caar(x), q_mminus) {
    ratminus(prep1(cadr(x)))
  } else if eq(caar(x), q_rat) {
    if symval(q_modulus).truthy() {
      cons(cquotient(cmod(cadr(x)), cmod(caddr(x))), Fix(1L))
    } else {
      cons(cadr(x), caddr(x))
    }
  } else if eq(caar(x), q_bigfloat) {
    bigfloat2rat(x)
  } else if eq(caar(x), q_mrat) {
    if symval(q_ear_withinratf).truthy() && memq(q_trunc, car(x)).truthy() {
      throw_tag(q_ratf, Nil)
    } else {
      let mut temp : Value = Nil
      let ok = catch_tag(q_compatvl, () => {
        temp = compatvarl(
          caddar(x),
          symval(q_varlist),
          cadddr(car(x)),
          symval(q_genvar),
        )
        t
      })
      if ok.truthy() {
        if memq(q_trunc, car(x)).truthy() {
          cdr(d_taytorat(x))
        } else if !symval(q_d_keepfloat).truthy() &&
          (pfloatp(cadr(x)).truthy() || pfloatp(cddr(x)).truthy()) {
          cdr(ratrep_star(d_ratdisrep(x)))
        } else {
          sublis(temp, cdr(x))
        }
      } else {
        cdr(ratrep_star(d_ratdisrep(x)))
      }
    }
  } else {
    let v = assolike(x, symval(q_genpairs))
    if v.truthy() {
      v
    } else {
      let x = littlefr1(x)
      let v = assolike(x, symval(q_genpairs))
      if v.truthy() {
        v
      } else {
        newsym(x)
      }
    }
  }
}

///|
fn putonvlist(x : Value) -> Value raise {
  set(q_vlist, cons(x, symval(q_vlist))) |> ignore
  if symval(q_d_algebraic).truthy() {
    let x = assolike(x, symval(q_tellratlist))
    if x.truthy() {
      return mapc(y => newvar1(y) |> ignore, x)
    }
  }
  Nil
}

///|
/// NEWVARMEXPT: when FLAG is T, the call returns a ratform.
fn newvarmexpt(x : Value, e : Value, flag : Value) -> Value raise {
  let mut x = x
  let mut e = e
  let flag_ = flag.truthy()
  if integerp(e) && !flag_ {
    return newvar1(cadr(x))
  }
  let mut topexp : Value = Fix(1L)
  let mut again = true
  while again {
    again = false
    if integerp(e) {
      // X=B^N FOR N A NUMBER
      topexp = num_mul(topexp, e)
      x = cadr(x)
    } else if atom(e) {
      ()
    } else if eq(caar(e), q_rat) {
      // X=B^(P/Q) FOR P AND Q INTEGERS
      if minusp(cadr(e)) || ratmac__gt(cadr(e), Fix(1L)) {
        topexp = num_mul(topexp, cadr(e))
        x = list3(list1(q_mexpt), cadr(x), list3(list1(q_rat), Fix(1L), caddr(e)))
      }
      if flag_ || numberp(cadr(x)) {
        ()
      } else if symval(q_ear_ratsimp).truthy() {
        if memalike(x, symval(q_radlist)).truthy() {
          return Nil
        } else {
          set(q_radlist, cons(x, symval(q_radlist))) |> ignore
          return newvar1(cadr(x))
        }
      } else if symval(q_d_algebraic).truthy() {
        newvar1(cadr(x)) |> ignore
      }
    } else if eq(caar(e), q_mtimes) {
      // X=B^(A*C)
      let mut hit = false
      // X=B^(N *C)
      if atom(cadr(e)) && integerp(cadr(e)) {
        topexp = num_mul(topexp, cadr(e))
        e = cddr(e)
        hit = e.truthy()
      }
      // X=B^(P/Q *C)
      if !hit &&
        !atom(cadr(e)) &&
        eq(caaadr(e), q_rat) &&
        !equal(Fix(1L), cadadr(e)) {
        topexp = num_mul(topexp, cadadr(e))
        e = cons(list3(list1(q_rat), Fix(1L), caddr(cadr(e))), cddr(e))
        hit = true
      }
      if hit {
        e = simplify(cons(list1(q_mtimes), e))
        x = list3(list1(q_mexpt), cadr(x), e)
        again = true
      }
    } else if eq(caar(e), q_mplus) && symval(q_expsumsplit).truthy() {
      // X=B^(A+C): SWITCH CONTROLS SPLITTING EXPONENT SUMS
      let base = cadr(x)
      let te = topexp
      x = cons(
        list1(q_mtimes),
        mapcar(
          ll => list3(
            list1(q_mexpt),
            base,
            simplify(list3(list1(q_mtimes), te, ll)),
          ),
          cdr(e),
        ),
      )
      if flag_ {
        return prep1(x)
      } else {
        return newvar1(x)
      }
    }
  }
  if flag_ {
    ()
  } else if equal(Fix(1L), topexp) {
    if atom(x) || !eq(caar(x), q_mexpt) {
      newvar1(x) |> ignore
    } else if memalike(x, symval(q_varlist)).truthy() ||
      memalike(x, symval(q_vlist)).truthy() {
      ()
    } else if atom(x) || !symval(q_n_starfnewvarsw).truthy() {
      putonvlist(x) |> ignore
    } else {
      x = littlefr1(x)
      mapc(y => newvar1(y) |> ignore, cdr(x)) |> ignore
      if !(memalike(x, symval(q_vlist)).truthy() ||
        memalike(x, symval(q_varlist)).truthy()) {
        putonvlist(x) |> ignore
      }
    }
  } else {
    newvar1(x) |> ignore
  }
  if !flag_ {
    Nil
  } else if equal(Fix(1L), topexp) {
    if !atom(x) && eq(caar(x), q_mexpt) {
      let v = assolike(x, symval(q_genpairs))
      if v.truthy() {
        v
      } else {
        // *** SHOULD ONLY GET HERE IF CALLED FROM FR1. *FNEWVARSW=NIL
        let x = littlefr1(x)
        let v = assolike(x, symval(q_genpairs))
        if v.truthy() {
          v
        } else {
          newsym(x)
        }
      }
    } else {
      prep1(x)
    }
  } else {
    ratexpt(prep1(x), topexp)
  }
}

///|
fn newvar1(x : Value) -> Value raise {
  if numberp(x) {
    Nil
  } else if memalike(x, symval(q_varlist)).truthy() {
    Nil
  } else if memalike(x, symval(q_vlist)).truthy() {
    Nil
  } else if atom(x) {
    putonvlist(x)
  } else if memq(
      caar(x),
      list([
        q_mplus, q_mtimes, q_rat, q_mdifference, q_mquotient, q_mminus, q_bigfloat,
      ]),
    ).truthy() {
    mapc(y => newvar1(y) |> ignore, cdr(x))
  } else if eq(caar(x), q_mexpt) {
    newvarmexpt(x, caddr(x), Nil)
  } else if eq(caar(x), q_mrat) {
    if symval(q_ear_withinratf).truthy() && memq(q_trunc, cdr(cddar(x))).truthy() {
      throw_tag(q_ratf, q_p_op_pct) |> ignore
    }
    if symval(q_d_ratfac).truthy() {
      mapc(y => newvar3(y) |> ignore, caddar(x))
    } else {
      mapc(y => newvar1(y) |> ignore, reverse(caddar(x)))
    }
  } else if symval(q_n_starfnewvarsw).truthy() {
    let x = littlefr1(x)
    mapc(y => newvar1(y) |> ignore, cdr(x)) |> ignore
    let v = memalike(x, symval(q_vlist))
    if v.truthy() {
      return v
    }
    let v = memalike(x, symval(q_varlist))
    if v.truthy() {
      return v
    }
    putonvlist(x)
  } else {
    putonvlist(x)
  }
}

///|
fn newvar3(x : Value) -> Value raise {
  let v = memalike(x, symval(q_vlist))
  if v.truthy() {
    return v
  }
  let v = memalike(x, symval(q_varlist))
  if v.truthy() {
    return v
  }
  putonvlist(x)
}

///|
/// Radicals b^(1/m) and b^(1/n) of one base whose indices have a common
/// factor are powers of b^(1/k), k = lcm(m,n). Replace each class of such
/// radicals in the kernel list L by b^(1/k), and return L and PAIRS with
/// (RADICAL B^(1/K) . K/M) added for each radical that it replaces.
fn unify_radicals(l : Value, pairs : Value) -> (Value, Value) raise {
  let mut l = l
  let mut pairs = pairs
  // (base . classes), a class (lcm . radicals)
  let mut groups : Value = Nil
  for v in l.iter() {
    if radfunp(v, Nil).truthy() && eql(cadr(caddr(v)), Fix(1L)) {
      let n = caddr(caddr(v))
      let mut c = list2(n, v)
      let mut rest : Value = Nil
      let g = {
        let g0 = assol(cadr(v), groups)
        if g0.truthy() {
          g0
        } else {
          groups = cons(list1(cadr(v)), groups)
          car(groups)
        }
      }
      for d in cdr(g).iter() {
        if ratmac__gt(num_gcd(car(d), n), Fix(1L)) {
          c = cons(num_lcm(car(c), car(d)), append(cdr(d), cdr(c)))
        } else {
          rest = cons(d, rest)
        }
      }
      setf_cdr(g, cons(c, rest)) |> ignore
    }
  }
  for g in groups.iter() {
    for c in cdr(g).iter() {
      // With domain:real, x^(1/3) = (x^(1/6))^2 fails for x < 0, so if b may
      // be negative, n must be odd or a power of 2, which makes the powers of
      // b^(1/n) all odd or all even roots. Odd roots of -1 simplify to -1.
      let b = car(g)
      let n = car(c)
      if cddr(c).truthy() &&
        (
          (numberp(b) && (plusp(b) || eql(b, Fix(-1L)))) ||
          !eq(symval(q_d_domain), q_d_real) ||
          oddp(n) ||
          logcount(n) == 1
        ) {
        let k = simplify(
          list3(list1(q_mexpt), b, list3(list1(q_rat), Fix(1L), n)),
        )
        if mexptp(k).truthy() &&
          alike1(cadr(k), b).truthy() &&
          equal(caddr(k), list3(list2(q_rat, q_simp), Fix(1L), n)) {
          for m in cdr(c).iter() {
            l = remove(m, l)
            if !alike1(m, k).truthy() {
              pairs = cons(
                cons(m, cons(k, num_div(n, caddr(caddr(m))))),
                pairs,
              )
            }
          }
          if !(memalike(k, l).truthy() ||
            memalike(k, symval(q_varlist)).truthy()) {
            l = cons(k, l)
          }
        }
      }
    }
  }
  (l, pairs)
}

///|
/// Put radicands on initial varlist?
fn fr1(x : Value, varlist : Value) -> Value raise {
  if (symbolp(x) &&
    !symval(q_d_algebraic).truthy() &&
    !symval(q_d_ratwtlvl).truthy()) ||
    (integerp(x) && !symval(q_modulus).truthy()) {
    // early exit for symbols and integers
    return x
  }
  let b0 = bind(q_varlist, varlist)
  defer unbind(b0)
  let bs = bind_all([
    (q_genvar, Nil),
    (q_d_norepeat, Nil),
    (q_ear_ratsimp, Nil),
    (q_radlist, Nil),
    (q_vlist, Nil),
    (q_ovarlist, Nil),
    (q_genpairs, Nil),
  ])
  defer unbind_all(bs)
  let mut x = x
  newvar1(x) |> ignore
  let mut nvarlist = mapcar(v => fr_args(v), symval(q_vlist))
  if !symval(q_ear_ratsimp).truthy() {
    // *ratsimp* not set for initial varlist
    set(
      q_varlist,
      nconc(sortgreat(symval(q_vlist)), symval(q_varlist)),
    )
    |> ignore
    return rdis(cdr(ratrep_star(x)))
  }
  set(q_ovarlist, nconc(symval(q_vlist), symval(q_varlist))) |> ignore
  set(q_vlist, Nil) |> ignore
  // *RATSIMP*=T PUTS RADICANDS ON VLIST
  mapc(v => newvar1(v) |> ignore, nvarlist) |> ignore
  // and those of radicals on initial varlist
  for v in symval(q_varlist).iter() {
    if radfunp(v, Nil).truthy() {
      newvar1(cadr(v)) |> ignore
    }
  }
  let (vl, pairs) = unify_radicals(symval(q_vlist), Nil)
  set(q_vlist, vl) |> ignore
  let (rl, pairs) = unify_radicals(symval(q_radlist), pairs)
  set(q_radlist, rl) |> ignore
  // RADICALS ON RADLIST
  nvarlist = nconc(nvarlist, symval(q_varlist))
  set(
    q_varlist,
    nconc_n([
      sortgreat(symval(q_vlist)),
      radsort(symval(q_radlist)),
      symval(q_varlist),
    ]),
  )
  |> ignore
  orderpointer(symval(q_varlist)) |> ignore
  set(
    q_genpairs,
    mapcar2((x, y) => cons(x, rget(y)), symval(q_varlist), symval(q_genvar)),
  )
  |> ignore
  for p in pairs.iter() {
    set(
      q_genpairs,
      cons(
        cons(car(p), ratexpt(assolike(cadr(p), symval(q_genpairs)), cddr(p))),
        symval(q_genpairs),
      ),
    )
    |> ignore
  }
  let nvl = nvarlist
  x = with_specials(
    [
      (q_d_algebraic, symval(q_d_algebraic)),
      (q_d_ratalgdenom, symval(q_d_ratalgdenom)),
      (q_radlist, Nil),
    ],
    () => {
      if !symval(q_d_algebraic).truthy() &&
        some(v => algpget(v).truthy(), symval(q_varlist)) {
        // NEEDS *RATSIMP*=T
        set(q_d_algebraic, t) |> ignore
        set(q_d_ratalgdenom, Nil) |> ignore
      }
      ratsetup(symval(q_varlist), symval(q_genvar)) |> ignore
      set(
        q_genpairs,
        mapcar2((a, b) => cons(a, prep1(b)), symval(q_ovarlist), nvl),
      )
      |> ignore
      let mut r = rdis(prep1(x))
      if symval(q_radlist).truthy() {
        // rational radicands
        set(q_ear_ratsimp, Nil) |> ignore
        r = ratsimp(simplify(r), Nil, Nil)
      }
      r
    },
  )
  x
}

///|
fn ratsimp(x : Value, varlist : Value, genvar : Value) -> Value raise {
  with_specials([(q_varlist, varlist), (q_genvar, genvar)], () => d_ratdisrep(
    ratf(x),
  ))
}

///|
fn littlefr1(x : Value) -> Value raise {
  cons(remove(q_simp, car(x)), mapfr1(cdr(x), Nil))
}

///|
/// SIMP (A/B)^N TO A^N/B^N ?
fn fr_args(x : Value) -> Value raise {
  if atom(x) {
    if eq(x, q_d__pcti) {
      // indicates algebraic present
      set(q_ear_ratsimp, t) |> ignore
    }
    x
  } else {
    // FLAG TO CHANGED ELMT.
    set(q_ear_ratsimp, t) |> ignore
    let args = if radfunp(x, Nil).truthy() || eq(caar(x), q_p_log) {
      cons(
        if symval(q_fr_factor).truthy() {
          factor(cadr(x))
        } else {
          fr1(cadr(x), symval(q_varlist))
        },
        cddr(x),
      )
    } else {
      with_special(q_modulus, Nil, () => mapfr1(cdr(x), symval(q_varlist)))
    }
    simplify(zp(cons(remove(q_simp, car(x)), args)))
  }
}

///|
/// SIMPLIFY MEXPT'S & RATEXPAND EXPONENT
fn zp(x : Value) -> Value raise {
  if mexptp(x).truthy() && !atom(caddr(x)) {
    list3(
      car(x),
      cadr(x),
      with_specials(
        [(q_varlist, symval(q_varlist)), (q_ear_ratsimp, Nil)],
        () => d_ratexpand(caddr(x)),
      ),
    )
  } else {
    x
  }
}

///|
fn newsym(e : Value) -> Value raise {
  let g = assolike(e, symval(q_genpairs))
  if g.truthy() {
    return g
  }
  let g = gensym_readable(e)
  putprop(g, e, q_disrep) |> ignore
  set(q_varlist, cons(e, symval(q_varlist))) |> ignore
  set(q_genpairs, cons(cons(e, rget(g)), symval(q_genpairs))) |> ignore
  let gv = symval(q_genvar)
  valput(
    g,
    if gv.truthy() {
      num_sub(valget(car(gv)), Fix(1L))
    } else {
      Fix(1L)
    },
  )
  |> ignore
  set(q_genvar, cons(g, symval(q_genvar))) |> ignore
  let p = if symval(q_d_algebraic).truthy() { algpget(e) } else { Nil }
  if p.truthy() {
    algordset(p, symval(q_genvar)) |> ignore
    putprop(g, p, q_tellrat) |> ignore
  }
  rget(g)
}

// This control of conversion from float to rational appears to be explained
// nowhere. - RJF

///|
fn maxima_rationalize(x : Value) -> Value raise {
  match x {
    Flo(d) =>
      // Handle denormalized floats -- see maxima-discuss 2021-04-27 and bug 3777
      if d != 0.0 && d.abs() < least_positive_normalized_double_float {
        let r = d_rationalize(x)
        cons(cadr(r), caddr(r))
      } else if d < 0.0 {
        let r = ration1(Flo(-1.0 * d))
        rplaca(r, num_mul(Fix(-1L), car(r)))
      } else {
        ration1(x)
      }
    _ => x
  }
}

///|
fn ration1(x : Value) -> Value raise {
  let re = symval(q_d_ratepsilon)
  let rateps = if !floatp(re) { d_float(re) } else { re }
  if zerop(x) {
    return cons(Fix(0L), Fix(1L))
  }
  // Computes a continued fraction expansion of the given float.
  let xd = to_double(x)
  let mut xx = xd
  let mut a = floor1(x)
  let mut num = a
  let mut den : Value = Fix(1L)
  let mut onum : Value = Fix(1L)
  let mut oden : Value = Fix(0L)
  while true {
    if xx - to_double(a) == 0.0 ||
      (!zerop(den) &&
      !num_gt(
        Flo(((xd - to_double(num) / to_double(den)) / xd).abs()),
        rateps,
      )) {
      return cons(num, den)
    }
    let y = 1.0 / (xx - to_double(a))
    let nxx = y
    a = floor1(Flo(y))
    let nnum = num_add(num_mul(a, num), onum)
    let nden = num_add(num_mul(a, den), oden)
    onum = num
    oden = den
    xx = nxx
    num = nnum
    den = nden
  }
  Nil
}

///|
fn prepfloat(f : Value) -> Value raise {
  if symval(q_modulus).truthy() {
    merr("rat: can't rationalize ~M when modulus = ~M", [f, symval(q_modulus)])
    |> ignore
  } else if symval(q_d_ratprint).truthy() {
    mtell(list2(Str("~&rat: replaced ~A by"), f)) |> ignore
  }
  let f = maxima_rationalize(f)
  if symval(q_d_ratprint).truthy() {
    mtell(
      list4(Str(" ~A/~A = ~A~%"), car(f), cdr(f), fpcofrat1(car(f), cdr(f))),
    )
    |> ignore
  }
  f
}

///|
fn pdisrep(p : Value) -> Value raise {
  if atom(p) {
    p
  } else {
    pdisrep_plus(pdisrep2(cdr(p), get(car(p), q_disrep)))
  }
}

///|
fn pdisrep_bang(n : Value, var2 : Value) -> Value raise {
  if zerop(n) {
    Fix(1L)
  } else if equal(n, Fix(1L)) {
    if atom(var2) {
      var2
    } else if eq(caar(var2), q_mtimes) || eq(caar(var2), q_mplus) {
      copy_list(var2)
    } else {
      var2
    }
  } else if eql(var2, Fix(1L)) {
    Fix(1L)
  } else {
    list3(list2(q_mexpt, q_ratsimp), var2, n)
  }
}

///|
fn pdisrep_plus(p : Value) -> Value raise {
  if cdr(p) is Nil {
    car(p)
  } else {
    let a = last(p)
    if mplusp(car(a)).truthy() {
      rplacd(a, cddar(a)) |> ignore
      rplaca(a, cadar(a)) |> ignore
    }
    cons(list2(q_mplus, q_ratsimp), p)
  }
}

///|
fn pdisrep_star(a : Value, b : Value) -> Value raise {
  if equal(a, Fix(1L)) {
    b
  } else if equal(b, Fix(1L)) {
    a
  } else {
    cons(
      list2(q_mtimes, q_ratsimp),
      nconc(pdisrep_starchk(a), pdisrep_starchk(b)),
    )
  }
}

///|
fn pdisrep_starchk(a : Value) -> Value raise {
  if mtimesp(a).truthy() {
    cdr(a)
  } else {
    list1(a)
  }
}

///|
fn pdisrep2(p : Value, var2 : Value) -> Value raise {
  if p is Nil {
    Nil
  } else if symval(q_d_ratexpand).truthy() {
    pdisrep2expand(p, var2)
  } else {
    let acc = Collector::new()
    let mut p = p
    while !(p is Nil) {
      acc.add(pdisrep_star(pdisrep(cadr(p)), pdisrep_bang(car(p), var2)))
      p = cddr(p)
    }
    acc.result()
  }
}

///|
fn d_ratexpand(x : Value) -> Value raise {
  if mbagp(x).truthy() {
    cons(car(x), mapcar(y => d_ratexpand(y), cdr(x)))
  } else {
    with_specials([(q_d_ratexpand, t), (q_d_ratfac, Nil)], () => ratdisrep(
      ratf(x),
    ))
  }
}

///|
fn pdisrep_starexpand(a : Value, b : Value) -> Value raise {
  if equal(a, Fix(1L)) {
    list1(b)
  } else if equal(b, Fix(1L)) {
    list1(a)
  } else if atom(a) || !eq(caar(a), q_mplus) {
    list1(
      cons(
        list2(q_mtimes, q_ratsimp),
        nconc(pdisrep_starchk(a), pdisrep_starchk(b)),
      ),
    )
  } else {
    mapcar(
      z => if equal(z, Fix(1L)) {
        b
      } else {
        cons(
          list2(q_mtimes, q_ratsimp),
          nconc(pdisrep_starchk(z), pdisrep_starchk(b)),
        )
      },
      cdr(a),
    )
  }
}

///|
fn pdisrep2expand(p : Value, var2 : Value) -> Value raise {
  if p is Nil {
    Nil
  } else {
    let a = pdisrep_starexpand(pdisrep(cadr(p)), pdisrep_bang(car(p), var2))
    nconc(a, pdisrep2expand(cddr(p), var2))
  }
}

///|
fn d_ratdisrep(x : Value) -> Value raise {
  if mbagp(x).truthy() {
    // Distribute over lists, equations, and matrices.
    // Remove a SIMP flag to allow elements to be simplified.
    cons(delsimp(car(x)), mapcar(y => d_ratdisrep(y), cdr(x)))
  } else if !d_ratp(x).truthy() {
    x
  } else {
    let x = ratdisrepd(x)
    if !atom(x) && memq(q_trunc, cdar(x)).truthy() {
      cons(rat3e__delete_first_eq(q_trunc, copy_list(car(x))), cdr(x))
    } else {
      x
    }
  }
}

///|
/// `(delete item list :count 1 :test #'eq)`
fn rat3e__delete_first_eq(item : Value, l : Value) -> Value {
  if l is Nil {
    return l
  }
  if eq(car(l), item) {
    return cdr(l)
  }
  let mut p = l
  while cdr(p) is Cons(_) {
    if eq(cadr(p), item) {
      rplacd(p, cddr(p)) |> ignore
      return l
    }
    p = cdr(p)
  }
  l
}

///|
/// RATDISREPD is needed by DISPLA. - JPG
fn ratdisrepd(x : Value) -> Value raise {
  let mut gl = cadddr(car(x))
  let mut vl = caddar(x)
  while gl is Cons(_) && vl is Cons(_) {
    putprop(car(gl), car(vl), q_disrep) |> ignore
    gl = cdr(gl)
    vl = cdr(vl)
  }
  with_special(q_varlist, caddar(x), () => if memq(q_trunc, car(x)).truthy() {
    srdisrep(x)
  } else {
    cdisrep(cdr(x))
  })
}

///|
fn cdisrep(x : Value) -> Value raise {
  if ratmac__pz(car(x)) {
    return Fix(0L)
  }
  if equal(Fix(1L), cdr(x)) ||
    (
      match cdr(x) {
        Flo(d) => d == 1.0
        _ => false
      }
    ) {
    return pdisrep(car(x))
  }
  if floatp(cdr(x)) {
    return pdisrep(pctimes(num_div(Fix(1L), cdr(x)), car(x)))
  }
  let mut n : Value = Nil
  let sign : Value = if symval(q_d_ratexpand).truthy() {
    n = pdisrep(car(x))
    Fix(1L)
  } else if rat3a__pminusp(car(x)) {
    n = pdisrep(pminus(car(x)))
    Fix(-1L)
  } else {
    n = pdisrep(car(x))
    Fix(1L)
  }
  let d = pdisrep(cdr(x))
  if numberp(n) && numberp(d) {
    if floatp(n) {
      num_div(num_mul(sign, n), d)
    } else {
      list3(list1(q_rat), num_mul(sign, n), d)
    }
  } else if symval(q_d_ratdenomdivide).truthy() &&
    symval(q_d_ratexpand).truthy() &&
    !atom(n) &&
    eq(caar(n), q_mplus) {
    fancydis(n, d)
  } else if numberp(d) {
    list3(list2(q_mtimes, q_ratsimp), list3(list1(q_rat), sign, d), n)
  } else if equal(sign, Fix(-1L)) {
    cons(
      list2(q_mtimes, q_ratsimp),
      if numberp(n) {
        list2(
          num_mul(n, Fix(-1L)),
          list3(list2(q_mexpt, q_ratsimp), d, Fix(-1L)),
        )
      } else {
        list3(sign, n, list3(list2(q_mexpt, q_ratsimp), d, Fix(-1L)))
      },
    )
  } else if equal(n, Fix(1L)) {
    list3(list2(q_mexpt, q_ratsimp), d, Fix(-1L))
  } else {
    list3(
      list2(q_mtimes, q_ratsimp),
      n,
      list3(list2(q_mexpt, q_ratsimp), d, Fix(-1L)),
    )
  }
}

///|
/// FANCYDIS GOES THROUGH EACH TERM AND DIVIDES IT BY THE DENOMINATOR.
fn fancydis(n : Value, d : Value) -> Value raise {
  let d = simplify(list3(list1(q_mexpt), d, Fix(-1L)))
  simplify(
    cons(
      list1(q_mplus),
      mapcar(z => d_ratdisrep(ratf(list3(list1(q_mtimes), z, d))), cdr(n)),
    ),
  )
}

///|
fn compatvarl(a : Value, b : Value, c : Value, d : Value) -> Value raise {
  if a is Nil {
    Nil
  } else if b is Nil || c is Nil || d is Nil {
    throw_tag(q_compatvl, Nil)
  } else if alike1(car(a), car(b)).truthy() {
    let a = compatvarl(cdr(a), cdr(b), cdr(c), cdr(d))
    if eq(car(c), car(d)) {
      a
    } else {
      cons(cons(car(c), car(d)), a)
    }
  } else {
    compatvarl(a, cdr(b), c, cdr(d))
  }
}

///|
fn newvar(l : Value) -> Value raise {
  with_special(q_vlist, Nil, () => {
    newvar1(l) |> ignore
    set(q_varlist, nconc(sortgreat(symval(q_vlist)), symval(q_varlist)))
  })
}

///|
/// FIXME consider a total order function with #'sort
fn sortgreat(l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else {
    nreverse(sort_list(l, (a, b) => great(a, b).truthy()))
  }
}

///|
fn fnewvar(l : Value) -> Value raise {
  with_special(q_n_starfnewvarsw, t, () => newvar(l))
}

///|
fn nestlev(exp_ : Value) -> Value raise {
  if atom(exp_) {
    Fix(0L)
  } else {
    let mut m = nestlev(cadr(exp_))
    let mut l = cddr(exp_)
    while !(l is Nil) {
      m = num_max(m, nestlev(car(l)))
      l = cdr(l)
    }
    num_add(m, Fix(1L))
  }
}

///|
fn radsort(l : Value) -> Value raise {
  sort_list(l, (a, b) => {
    let na = nestlev(a)
    let nb = nestlev(b)
    if ratmac__lt(na, nb) {
      true
    } else if ratmac__gt(na, nb) {
      false
    } else {
      great(b, a).truthy()
    }
  })
}

///|
fn init_rat3e() -> Unit raise {
  putprop(q_mrat, q_mrateval, q_mfexpr_star) |> ignore
  // CONTROLS SPLITTING SUMS IN EXPONS
  set(q_expsumsplit, t) |> ignore
  putprop(q_d_fullratsimp, t, q_evfun) |> ignore
  putprop(q_d_ratsimp, t, q_evfun) |> ignore
  putprop(q_d_factor, t, q_evfun) |> ignore
  putprop(q_d_ratexpand, t, q_evfun) |> ignore
}
