// Port of src/ezgcd.lisp: the EZ (extended Zassenhaus) multivariate
// polynomial GCD algorithm.
//
// Specials of this file: lcprod svals svars oldsvars oldsvals valflag $gcd
// pl0 d0 degd0 var many* tempprime ovarlist valist zl *prime plim nn* ne
// nn*-1 dlp ez1skip svalsl nsvals lc1 oldlc limk.

///|
fn ezgcd2(f : Value, g : Value) -> Value raise {
  let allvars = union_star(listovars(f), listovars(g))
  if 2 > length(allvars) {
    let r = newgcd(f, g, symval(q_modulus))
    if !(cdr(r) is Nil) {
      return r
    }
    let a = car(r)
    return list3(a, pquotient(f, a), pquotient(g, a))
  }
  let allvars = sort_list(allvars, (a, b) => pointergp(a, b).truthy())
  ezgcd(list2(f, g), allvars, symval(q_modulus))
}

///|
fn newgcdcall(p : Value, q : Value) -> Value raise {
  car(newgcd(p, q, symval(q_modulus)))
}

///|
fn gcdl(pl : Value) -> Value raise {
  let mut d = car(pl)
  let mut l = cdr(pl)
  while !(l is Nil || eql(d, Fix(1L))) {
    d = pgcd(d, car(l))
    l = cdr(l)
  }
  d
}

///|
fn newgcdl(pl : Value) -> Value raise {
  with_special(q_d_gcd, q_d_mod, () => gcdl(pl))
}

///|
fn oldgcdl(elt_ : Value, pl : Value) -> Value raise {
  with_special(q_d_gcd, q_d_red, () => gcdl(cons(elt_, pl)))
}

///|
fn oldgcdcall(pfl : Value) -> Value raise {
  let a = oldgcdl(car(pfl), cdr(pfl))
  cons(a, mapcar(h => pquotient(h, a), pfl))
}

///|
fn non0rand(modulus : Value) -> Value raise {
  let b = bind(q_modulus, modulus)
  defer unbind(b)
  while true {
    let r = cmod(mt_random(Fix(1000L)))
    if !zerop(r) {
      return r
    }
  }
  Nil
}

///|
fn getgoodvals(varl : Value, lcp : Value) -> Value raise {
  let mut lcp = lcp
  mapcar(
    v => {
      let mut val : Value = Fix(0L)
      while true {
        let temp = pcsubsty(val, v, lcp)
        if !pzerop(temp).truthy() {
          lcp = temp
          return val
        }
        val = non0rand(symval(q_tempprime))
      }
      val
    },
    varl,
  )
}

///|
fn evmap(vals : Value, pl : Value) -> Value raise {
  let bs = bind_all([(q_pl0, Nil), (q_d0, Nil)])
  defer unbind_all(bs)
  let mut vals = vals
  let nsvars = length(symval(q_svars))
  if equal(symval(q_nsvals), int(length(symval(q_svalsl)))) {
    return Nil
  }
  if !symval(q_valflag).truthy() {
    vals = getgoodvals(symval(q_svars), symval(q_lcprod))
    while member_equal(vals, symval(q_svalsl)).truthy() {
      vals = rand(int(nsvars), symval(q_tempprime))
    }
    set(q_valflag, t) |> ignore
    set(q_svalsl, cons(vals, symval(q_svalsl))) |> ignore
  } else {
    // newvals
    while true {
      set(q_pl0, rand(int(nsvars), symval(q_tempprime))) |> ignore
      if member_equal(symval(q_pl0), symval(q_svalsl)).truthy() {
        continue
      }
      vals = symval(q_pl0)
      set(q_svalsl, cons(vals, symval(q_svalsl))) |> ignore
      if equal(Fix(0L), pcsub(symval(q_lcprod), vals, symval(q_svars))) {
        if equal(symval(q_nsvals), int(length(symval(q_svalsl)))) {
          return Nil
        }
        continue
      }
      break
    }
  }
  // end
  getd0(pl, vals) |> ignore
  list3(vals, symval(q_pl0), symval(q_d0))
}

///|
fn degodr(a : Value, b : Value) -> Value raise {
  if numberp(a) {
    Nil
  } else if numberp(b) {
    t
  } else {
    lbool(num_gt(cadr(a), cadr(b)))
  }
}

///|
fn evtildegless(pl : Value) -> Value raise {
  while true {
    let evout = evmap(symval(q_svals), pl)
    if evout is Nil {
      return Nil
    }
    let npl0 = cadr(evout)
    let nd0 = caddr(evout)
    let ndeg : Value = if numberp(nd0) { Fix(0L) } else { cadr(nd0) }
    let degd0 = symval(q_degd0)
    if num_eq(degd0, ndeg) || num_gt(ndeg, degd0) {
      continue
    }
    set(q_degd0, ndeg) |> ignore
    set(q_pl0, npl0) |> ignore
    set(q_d0, nd0) |> ignore
    return set(q_svals, car(evout))
  }
  Nil
}

///|
fn ptimesmerge(pl1 : Value, pl2 : Value) -> Value raise {
  if pl1.truthy() {
    let x = ptimes(car(pl1), car(pl2))
    cons(x, ptimesmerge(cdr(pl1), cdr(pl2)))
  } else {
    Nil
  }
}

///|
fn ezgcd__maxmultideg(l : Value) -> Value raise {
  let mut m : Value = Fix(0L)
  let mut first_ = true
  for x in l.iter() {
    let d = multideg(x)
    if first_ || num_gt(d, m) {
      m = d
    }
    first_ = false
  }
  m
}

///|
fn ez1call(
  builder : Value,
  factrs : Value,
  lc1 : Value,
  valist : Value,
  ovarlist : Value,
) -> Value raise {
  let bs = bind_all([
    (q_lc1, lc1),
    (q_valist, valist),
    (q_ovarlist, ovarlist),
    (q_n_starprime, Nil),
    (q_plim, Nil),
    (q_nn_star, Nil),
    (q_ne, Nil),
    (q_nn_star_1, Nil),
    (q_zl, Nil),
    (q_oldlc, Nil),
    (q_dlp, Nil),
    (q_limk, Nil),
    (q_genvar, Nil),
    (q_subval, Nil),
    (q_subvar, Nil),
  ])
  defer unbind_all(bs)
  let mut builder = builder
  let mut factrs = factrs
  set(q_oldlc, caddr(builder)) |> ignore
  if !equal(Fix(1L), lc1) {
    builder = ptimes(builder, lc1)
  }
  set(q_genvar, append(ovarlist, list1(car(builder)))) |> ignore
  let alpha = symval(q_n_staralpha)
  if symval(q_modulus).truthy() {
    set(q_n_starprime, symval(q_modulus)) |> ignore
    set(q_plim, symval(q_modulus)) |> ignore
    set(q_limk, Fix(-1L)) |> ignore
  } else {
    set(
      q_n_starprime,
      num_max(
        num_max(norm(builder), maxcoefficient(car(factrs))),
        maxcoefficient(cadr(factrs)),
      ),
    )
    |> ignore
    if num_gt(symval(q_n_starprime), alpha) {
      let mut newmodulus = num_mul(alpha, alpha)
      set(q_limk, Fix(0L)) |> ignore
      while true {
        if num_gt(newmodulus, symval(q_n_starprime)) {
          set(q_n_starprime, alpha) |> ignore
          set(q_plim, newmodulus) |> ignore
          break
        }
        set(q_limk, one_plus(symval(q_limk))) |> ignore
        newmodulus = num_mul(newmodulus, newmodulus)
      }
    } else {
      set(q_limk, Fix(-1L)) |> ignore
      set(q_n_starprime, alpha) |> ignore
      set(q_plim, alpha) |> ignore
    }
  }
  // mod
  set(q_nn_star_1, int(length(ovarlist))) |> ignore
  set(q_ne, symval(q_nn_star_1)) |> ignore
  set(q_nn_star, one_plus(symval(q_ne))) |> ignore
  set(q_zl, completevector(Nil, Fix(1L), symval(q_nn_star), Fix(0L))) |> ignore
  fixvl(valist, ovarlist) |> ignore
  if equal(Fix(1L), lc1) {
    set(q_modulus, symval(q_plim)) |> ignore
    builder = newrep(builder)
    set(q_dlp, ezgcd__maxmultideg(cdr(oddelm(builder)))) |> ignore
    let zfactr = z1(builder, car(factrs), cadr(factrs))
    let zfactr = restorelc(zfactr, caddr(builder))
    return oldrep(cadr(zfactr))
  }
  set(q_modulus, symval(q_plim)) |> ignore
  let lcd0 = caddar(factrs)
  let mult = ctimes(
    pcsub(lc1, symval(q_svals), symval(q_svars)),
    crecip(lcd0),
  )
  factrs = list2(ptimes(mult, car(factrs)), ptimes(lcd0, cadr(factrs)))
  builder = newrep(builder)
  set(q_dlp, ezgcd__maxmultideg(cdr(oddelm(builder)))) |> ignore
  let zfactr = z1(builder, car(factrs), cadr(factrs))
  let zfactr = pmod(oldrep(car(zfactr)))
  cadr(with_special(q_modulus, Nil, () => fastcont(zfactr)))
}

///|
fn getd0(tpl : Value, tvals : Value) -> Value raise {
  let svars = symval(q_svars)
  let mut tpl = tpl
  set(q_d0, pcsub(car(tpl), tvals, svars)) |> ignore
  set(q_pl0, list1(symval(q_d0))) |> ignore
  tpl = cdr(tpl)
  while true {
    if tpl is Nil {
      return symval(q_d0)
    }
    let c = pcsub(car(tpl), tvals, svars)
    set(q_d0, newgcdcall(symval(q_d0), c)) |> ignore
    if numberp(symval(q_d0)) {
      return set(q_d0, Fix(1L))
    }
    set(q_pl0, append(symval(q_pl0), list1(c))) |> ignore
    tpl = cdr(tpl)
  }
  Nil
}

///|
fn numberinlistp(l : Value) -> Value raise {
  for x in l.iter() {
    if numberp(x) {
      return x
    }
  }
  Nil
}

///|
fn ezgcd(pfl : Value, vl : Value, modulus : Value) -> Value raise {
  let bs = bind_all([
    (q_modulus, modulus),
    (q_svars, Nil),
    (q_svals, Nil),
    (q_valflag, Nil),
    (q_tempprime, Nil),
    (q_nsvals, Nil),
    (q_svalsl, Nil),
    (q_lcprod, Nil),
    (q_pl0, Nil),
    (q_d0, Nil),
    (q_degd0, Nil),
    (q_var, Nil),
    (q_d_algebraic, Nil),
  ])
  defer unbind_all(bs)
  let mut pfl = pfl
  let mut temp = numberinlistp(pfl)
  if temp.truthy() {
    if member(Fix(1L), pfl).truthy() || member(Fix(-1L), pfl).truthy() {
      return cons(Fix(1L), pfl)
    }
    let temp = oldgcdl(temp, remove_equal(temp, pfl))
    let pl = mapcar(h => pquotient(h, temp), pfl)
    return cons(temp, pl)
  }
  set(q_svars, cdr(vl)) |> ignore
  set(q_var, car(vl)) |> ignore
  if symval(q_svars).truthy() {
    set(q_many_star, t) |> ignore
  } else {
    let d = newgcdl(pfl)
    return cons(d, mapcar(h => pquotient(h, d), pfl))
  }
  set(
    q_tempprime,
    if symval(q_modulus).truthy() {
      symval(q_modulus)
    } else {
      Fix(13L)
    },
  )
  |> ignore
  let mut tcontl = mapcar(x => ptermcont(x), pfl)
  pfl = mapcar(x => cadr(x), tcontl)
  tcontl = mapcar(x => car(x), tcontl)
  let mut termcont = oldgcdcall(tcontl)
  tcontl = cdr(termcont)
  termcont = car(termcont)
  let mut d : Value = Nil
  let mut pcofactl : Value = Nil
  let mut contgcd : Value = Nil
  let mut contcofactl : Value = Nil
  let mut pl : Value = Nil
  let mut evmapout : Value = Nil
  let mut degd0n : Value = Nil
  let mut d0n : Value = Nil
  let mut pl0n : Value = Nil
  let mut tryagain = false
  let mut cofact0 : Value = Nil
  let mut ith_ = 1
  let mut builder : Value = Nil
  // states
  let s_testd0 = 1
  let s_anothersvals = 2
  let s_testcofact = 3
  let s_loop = 4
  let s_testgcd = 5
  let s_next = 6
  let s_callez1 = 7
  let s_end = 8
  let s_loop1 = 9
  let s_out = 10
  let mut state = 0
  temp = numberinlistp(pfl)
  if temp.truthy() {
    let tmp = temp
    d = oldgcdl(tmp, remove_equal(tmp, pfl))
    let dd = d
    pcofactl = mapcar(h => pquotient(h, dd), pfl)
    contgcd = termcont
    contcofactl = tcontl
    state = s_out
  }
  if state == 0 {
    let var_ = symval(q_var)
    let mut pfcontl = mapcar(
      h => if eq(var_, car(h)) { fastcont(h) } else { list2(h, Fix(1L)) },
      pfl,
    )
    pfl = mapcar(x => cadr(x), pfcontl)
    pfcontl = mapcar(x => car(x), pfcontl)
    contgcd = ezgcd(pfcontl, symval(q_svars), symval(q_modulus))
    contcofactl = ptimesmerge(tcontl, cdr(contgcd))
    contgcd = ptimes(termcont, car(contgcd))
    if numberinlistp(pfl).truthy() {
      d = Fix(1L)
      pcofactl = pfl
      state = s_out
    }
  }
  if state == 0 {
    temp = listovarsl(pfl)
    temp = intersection(symval(q_svars), temp, pred2=(a, b) => equal(a, b))
    if !temp.truthy() {
      d = newgcdl(pfl)
      state = s_end
    }
  }
  if state == 0 {
    pl = bbsort(pfl, q_degodr)
    let nsvars = length(symval(q_svars))
    for _ in 0..<nsvars {
      set(q_svals, cons(Fix(0L), symval(q_svals))) |> ignore
    }
    set(q_lcprod, Fix(1L)) |> ignore
    set(q_svalsl, list1(symval(q_svals))) |> ignore
    set(
      q_nsvals,
      expt(symval(q_tempprime), int(length(symval(q_svars)))),
    )
    |> ignore
    for lc in mapcar(x => caddr(x), pl).iter() {
      set(q_lcprod, ptimes(symval(q_lcprod), lc)) |> ignore
    }
    if equal(
        Fix(0L),
        pcsub(symval(q_lcprod), symval(q_svals), symval(q_svars)),
      ) {
      evmapout = evmap(symval(q_svals), pl)
      if evmapout.truthy() {
        set(q_svals, car(evmapout)) |> ignore
        set(q_pl0, cadr(evmapout)) |> ignore
        set(q_d0, caddr(evmapout)) |> ignore
      } else {
        let r = oldgcdcall(pfl)
        d = car(r)
        pcofactl = cdr(r)
        state = s_out
      }
    } else {
      set(q_valflag, t) |> ignore
      getd0(pl, symval(q_svals)) |> ignore
    }
  }
  if state == 0 {
    let d0 = symval(q_d0)
    set(q_degd0, if numberp(d0) { Fix(0L) } else { cadr(d0) }) |> ignore
    state = s_testd0
  }
  while state != s_out {
    if state == s_testd0 {
      if equal(Fix(1L), symval(q_d0)) {
        d = Fix(1L)
        pcofactl = pfl
        state = s_out
      } else if degd0n.truthy() {
        state = s_testcofact
      } else {
        state = s_anothersvals
      }
    } else if state == s_anothersvals {
      evmapout = evmap(symval(q_svals), pl)
      if evmapout.truthy() {
        pl0n = cadr(evmapout)
        d0n = caddr(evmapout)
        evmapout = car(evmapout)
      } else {
        let r = oldgcdcall(pfl)
        d = car(r)
        pcofactl = cdr(r)
        state = s_out
        continue
      }
      degd0n = if numberp(d0n) { Fix(0L) } else { cadr(d0n) }
      if num_gt(symval(q_degd0), degd0n) {
        set(q_degd0, degd0n) |> ignore
        set(q_pl0, pl0n) |> ignore
        set(q_d0, d0n) |> ignore
        set(q_svals, evmapout) |> ignore
        state = s_anothersvals
      } else if equal(symval(q_degd0), degd0n) {
        state = s_testd0
      } else {
        state = s_anothersvals
      }
    } else if state == s_testcofact {
      if !equal(symval(q_degd0), cadar(symval(q_pl0))) {
        state = s_testgcd
      } else {
        d = car(pl)
        temp = pfl
        pcofactl = Nil
        state = s_loop
      }
    } else if state == s_loop {
      if temp.truthy() {
        d0n = eztestdivide(car(temp), d)
      } else {
        set(q_ez1skip, t) |> ignore
        state = s_out
        continue
      }
      if d0n.truthy() {
        pcofactl = append(pcofactl, list1(d0n))
        temp = cdr(temp)
      } else if evtildegless(pl).truthy() {
        degd0n = Nil
        state = s_testd0
      } else {
        let r = oldgcdcall(pfl)
        d = car(r)
        pcofactl = cdr(r)
        state = s_out
      }
    } else if state == s_testgcd {
      ith_ = 1
      temp = symval(q_pl0)
      state = s_next
    } else if state == s_next {
      if !temp.truthy() {
        if tryagain {
          d = nonsqfrcase(pfl, vl)
          pcofactl = cdr(d)
          d = car(d)
          state = s_out
        } else {
          set(q_degd0, degd0n) |> ignore
          set(q_pl0, pl0n) |> ignore
          set(q_d0, d0n) |> ignore
          degd0n = Nil
          pl0n = Nil
          d0n = Nil
          set(q_svals, evmapout) |> ignore
          tryagain = true
          state = s_testgcd
        }
        continue
      }
      cofact0 = pquotient(car(temp), symval(q_d0))
      if numberp(newgcdcall(symval(q_d0), cofact0)) {
        builder = ith(pl, int(ith_))
        if intersection(listovars(builder), symval(q_svars), pred2=(a, b) => equal(a, b)).truthy() {
          state = s_callez1
          continue
        }
      }
      temp = cdr(temp)
      ith_ += 1
    } else if state == s_callez1 {
      let lcpl = mapcar(x => caddr(x), pl)
      let gcdlcs = car(ezgcd(lcpl, symval(q_svars), symval(q_modulus)))
      d = ez1call(
        builder,
        list2(symval(q_d0), cofact0),
        gcdlcs,
        reverse(symval(q_svals)),
        reverse(symval(q_svars)),
      )
      set(q_modulus, Nil) |> ignore
      state = s_end
    } else if state == s_end {
      pcofactl = Nil
      temp = pfl
      if pminusp(d).truthy() {
        d = pminus(d)
      }
      state = s_loop1
    } else if state == s_loop1 {
      if temp.truthy() {
        cofact0 = eztestdivide(car(temp), d)
      } else {
        set(q_ez1skip, Nil) |> ignore
        state = s_out
        continue
      }
      if cofact0.truthy() {
        pcofactl = append(pcofactl, list1(cofact0))
        temp = cdr(temp)
      } else if evtildegless(pl).truthy() {
        degd0n = Nil
        state = s_testd0
      } else {
        let r = oldgcdcall(pfl)
        d = car(r)
        pcofactl = cdr(r)
        state = s_out
      }
    }
  }
  // out
  set(q_oldsvars, symval(q_svars)) |> ignore
  set(q_oldsvals, symval(q_svals)) |> ignore
  cons(ptimes(contgcd, d), ptimesmerge(contcofactl, pcofactl))
}

///|
fn listovarsl(plist : Value) -> Value raise {
  let allvarsl = mapcar(x => listovars(x), plist)
  let mut allvars = car(allvarsl)
  for l in cdr(allvarsl).iter() {
    allvars = union_star(allvars, l)
  }
  allvars
}

///|
fn d_ezgcd(args : Value) -> Value raise {
  let bg = bind(q_genvar, Nil) // need if genvar doesn't shrink
  defer unbind(bg)
  if args is Nil {
    wna_err(q_d_ezgcd) |> ignore
  }
  let flag = some(x => d_ratp(x).truthy(), args)
  let mut pfl = mapcar(h => cdr(ratf(h)), args)
  let mut pfl2 = list1(Fix(1L))
  let mut lcm = cdar(pfl)
  let mut l = cdr(pfl)
  while !(l is Nil) {
    let r = plcmcofacts(lcm, cdar(l))
    lcm = car(r)
    let cof1 = cadr(r)
    let cof2 = caddr(r)
    if !equal(cof1, Fix(1L)) {
      let p2 = pfl2
      mapcar(x => ptimes(x, cof1), p2) |> ignore
    }
    pfl2 = cons(cof2, pfl2)
    l = cdr(l)
  }
  let denom = lcm
  pfl = mapcar(x => car(x), pfl)
  let allvars = sort_list(listovarsl(pfl), (a, b) => pointergp(a, b).truthy())
  let mut presult = if symval(q_d_ratfac).truthy() {
    let p = pfl
    with_special(q_d_gcd, q_d_ez, () => facmgcd(p))
  } else {
    ezgcd(pfl, allvars, symval(q_modulus))
  }
  presult = cons(
    cons(car(presult), denom),
    if equal(denom, Fix(1L)) {
      cdr(presult)
    } else {
      mapcar2((a, b) => ptimes(a, b), cdr(presult), pfl2)
    },
  )
  presult = cons(
    list1(q_mlist),
    cons(rdis_star(car(presult)), mapcar(x => pdis_star(x), cdr(presult))),
  )
  if flag {
    presult
  } else {
    d_totaldisrep(presult)
  }
}

///|
fn insrt(nth_ : Value, elt_ : Value, l : Value) -> Value raise {
  if eql(nth_, Fix(1L)) {
    cons(elt_, l)
  } else {
    cons(car(l), insrt(one_minus(nth_), elt_, cdr(l)))
  }
}

///|
fn nonsqfrcase(pl : Value, vl : Value) -> Value raise {
  let modulus = symval(q_modulus)
  let mut dl = pl
  let mut pt = 1
  while !intersection(cdr(vl), listovars(car(dl)), pred2=(a, b) => equal(a, b)).truthy() {
    dl = cdr(dl)
    pt += 1
  }
  let f = car(dl)
  let ptr = pt
  let mut d = ezgcd(list2(f, pderivative(f, car(f))), vl, modulus)
  let mut pl = ezgcd(cons(cadr(d), remove_equal(f, pl)), vl, modulus)
  pl = cons(car(pl), cons(car(d), cddr(pl)))
  d = car(pl)
  while true {
    pl = ezgcd(pl, vl, symval(q_modulus))
    if equal(Fix(1L), car(pl)) {
      return cons(d, insrt(int(ptr), pquotient(f, d), cdddr(pl)))
    }
    d = ptimes(car(pl), d)
    pl = cons(car(pl), cddr(pl))
  }
  Nil
}

///|
fn eztestdivide(x : Value, y : Value) -> Value raise {
  if pcoefp(x).truthy() ||
    pcoefp(y).truthy() ||
    factor__ignore_rat_err(() => pquotient(car(last(x)), car(last(y)))).truthy() {
    factor__ignore_rat_err(() => pquotient(x, y))
  } else {
    Nil
  }
}

///|
fn noterms(p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    Fix(1L)
  } else {
    let mut nt = noterms(caddr(p))
    let mut p = cdddr(p)
    while !(p is Nil) {
      nt = num_add(nt, noterms(cadr(p)))
      p = cddr(p)
    }
    nt
  }
}

///|
fn fastcont(p : Value) -> Value raise {
  let bv = bind(q_var, Nil)
  defer unbind(bv)
  if univar(cdr(p)).truthy() {
    return oldcontent(p)
  }
  let mut p = p
  let oldgenvar = symval(q_genvar)
  set(q_var, car(p)) |> ignore
  // intersect must maintain order of genvar list
  set(
    q_genvar,
    remove_equal(symval(q_var), intersect(cdr(symval(q_genvar)), listovars(p))),
  )
  |> ignore
  let mut minus_q = false
  if pminusp(p).truthy() {
    p = pminus(p)
    minus_q = true
  }
  let mut tppl = oddelm(cddr(p))
  let mut tcont : Value = Nil
  let mut ans : Value = Nil
  let mut done = false
  if cdr(tppl) is Nil {
    tcont = Fix(1L)
    ans = car(tppl)
    done = true
  }
  if !done {
    let tcontl = mapcar(x => pmindegvec(x), tppl)
    tppl = mapcar2((x, y) => pquotient(x, degvecdisrep(y)), tppl, tcontl)
    tcont = car(tcontl)
    for l in cdr(tcontl).iter() {
      tcont = mapcar2((x, y) => num_min(x, y), tcont, l)
    }
    tcont = degvecdisrep(tcont)
    set(q_genvar, oldgenvar) |> ignore
    let temp = numberinlistp(tppl)
    if temp.truthy() {
      if member(Fix(1L), tppl).truthy() || member(Fix(-1L), tppl).truthy() {
        ans = Fix(1L)
      } else {
        ans = oldgcdl(temp, remove_equal(temp, tppl))
      }
      done = true
    }
  }
  if !done {
    if 4 > length(tppl) {
      tppl = bbsort(
        tppl,
        lfunc("fastcont-lenodr", args => lbool(
          length(arg(args, 0)) > length(arg(args, 1)),
        )),
      )
    } else {
      let mut coefvarl = mapcar(x => listovars(x), tppl)
      let mut temp = car(coefvarl)
      coefvarl = cdr(coefvarl)
      while !(coefvarl is Nil) {
        temp = intersection(temp, car(coefvarl), pred2=(a, b) => equal(a, b))
        if temp is Nil {
          ans = Fix(1L)
          done = true
          break
        }
        coefvarl = cdr(coefvarl)
      }
      if !done {
        let nts = mapcar(x => noterms(x), tppl)
        tppl = mapcar2((x, y) => list2(x, y), nts, tppl)
        tppl = bbsort(
          tppl,
          lfunc("fastcont-ntodr", args => lbool(
            num_gt(car(arg(args, 0)), car(arg(args, 1))),
          )),
        )
        tppl = mapcar(x => cadr(x), tppl)
      }
    }
  }
  if !done {
    // skip
    let small1 = car(tppl)
    let small2 = cadr(tppl)
    ans = pgcd(small1, small2)
    if eql(Fix(1L), ans) {
      ()
    } else if eql(Fix(-1L), ans) {
      ans = Fix(1L)
    } else if !(cddr(tppl) is Nil) {
      ans = cons(ans, cddr(tppl))
      let temp = sort_list(listovarsl(ans), (a, b) => pointergp(a, b).truthy())
      ans = car(ezgcd(ans, temp, symval(q_modulus)))
    }
  }
  // out
  tcont = ptimes(tcont, ans)
  p = pquotient(p, tcont)
  if minus_q {
    tcont = pminus(tcont)
  }
  list2(tcont, p)
}
