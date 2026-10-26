// Port of src/factor.lisp (part 2): multivariate factoring driver, true
// factor recovery, Hensel lifting and the Berlekamp null space.
//
// Note: *P* used to be P.  Here, functions that take *P* as a parameter
// treat it lexically (nothing they call reads it); MULTFACT and POLYSUBST
// use the special, since they transport state through it.

///|
fn fixvl0(l1 : Value, l2 : Value, ov : Value) -> Value raise {
  let mut a : Value = Nil
  let mut b : Value = Nil
  let mut c : Value = Nil
  let mut ov = ov
  while true {
    if ov is Nil {
      set(q_subvar, a) |> ignore
      set(q_subval, b) |> ignore
      set(q_valist, c) |> ignore
      return Nil
    } else if memq(car(ov), l1).truthy() {
      a = cons(car(ov), a)
      b = cons(assso(car(ov), l1, l2), b)
      c = cons(car(b), c)
    } else {
      c = cons(Fix(0L), c)
    }
    ov = cdr(ov)
  }
  Nil
}

///|
fn assso(a : Value, l1 : Value, l2 : Value) -> Value raise {
  let mut l1 = l1
  let mut l2 = l2
  while !(l1 is Nil) {
    if eq(car(l1), a) {
      return car(l2)
    }
    l1 = cdr(l1)
    l2 = cdr(l2)
  }
  Nil
}

///|
fn factor__count0(l : Value) -> Int raise {
  count_if(x => eql(x, Fix(0L)), l)
}

///|
fn zerohk(l : Value) -> Value raise {
  if l is Nil {
    return Nil
  }
  let mut l = l
  let mut ans = car(l)
  let mut i = factor__count0(ans)
  while true {
    l = cdr(l)
    if l is Nil {
      return ans
    } else if factor__count0(car(l)) > i {
      ans = car(l)
      i = factor__count0(ans)
    }
  }
  Nil
}

///|
fn multfact(poly : Value) -> Value raise {
  let bs = bind_all([
    (q_n_starinl3, Nil),
    (q_ear_i, Nil),
    (q_ear_min, Nil),
    (q_ear_mx, Nil),
    (q_nn_star, Nil),
    (q_ear_odr, Nil),
    (q_elm, Nil),
    (q_listelm, Nil),
    (q_plim, Nil),
    (q_ne, Nil),
    (q_var, Nil),
    (q_valist, Nil),
    (q_ovarlist, Nil),
    (q_ear_p, Nil),
    (q_subvar, Nil),
    (q_subvar1, Nil),
    (q_subval1, Nil),
    (q_subval, Nil),
    (q_dlp, Nil),
  ])
  defer unbind_all(bs)
  let mut poly = poly
  set(q_var, car(poly)) |> ignore
  set(q_elm, listovars(poly)) |> ignore
  let origenvar = symval(q_genvar)
  let elm = symval(q_elm)
  set(
    q_genvar,
    intersect(
      symval(q_genvar),
      if symval(q_algfac_star).truthy() {
        remove_equal(car(symval(q_ear_alpha)), elm)
      } else {
        elm
      },
    ),
  )
  |> ignore
  set(q_ovarlist, butlast(symval(q_genvar))) |> ignore // depends on the order of the above intersection!
  set(q_nn_star, int(1 + length(symval(q_ovarlist)))) |> ignore
  set(q_listelm, Fix(0L)) |> ignore
  let lc = caddr(poly)
  set(q_elm, Fix(1L)) |> ignore
  set(q_ear_i, Fix(1L)) |> ignore
  set(q_ne, Fix(1L)) |> ignore
  set(q_subval, reverse(poly)) |> ignore
  set(q_ear_odr, putodr(reverse(symval(q_ovarlist)))) |> ignore
  let subval = symval(q_subval)
  let dv = degvector(Nil, Fix(1L), lc)
  let val1 = zerohk(
    nconc(
      dv,
      if num_gt(cadr(subval), Fix(0L)) || num_gt(cadddr(subval), Fix(1L)) {
        degvector(Nil, Fix(1L), car(subval))
      } else {
        Nil
      },
    ),
  )
  set(q_subval, Nil) |> ignore
  set(q_ear_p, poly) |> ignore
  if val1 is Nil {
    set(q_subvar1, symval(q_ovarlist)) |> ignore
    let zeros = mapcar(_ => Fix(0L), symval(q_subvar1))
    set(q_subval1, polysubst(zeros, symval(q_subvar1))) |> ignore
  } else {
    fixvl(val1, symval(q_ovarlist)) |> ignore
    fixvl1(val1, symval(q_ovarlist)) |> ignore
    if symval(q_subval1).truthy() {
      set(q_subval1, polysubst(symval(q_subval1), symval(q_subvar1))) |> ignore
    }
    set(
      q_subval,
      polysubst(
        completevector(Nil, Fix(0L), int(length(symval(q_subval))), Fix(1L)),
        symval(q_subvar),
      ),
    )
    |> ignore
  }
  // tag
  fixvl(symval(q_subval1), symval(q_subvar1)) |> ignore
  set(q_subval1, Nil) |> ignore
  set(q_subvar1, Nil) |> ignore
  fixvl0(symval(q_subvar), symval(q_subval), reverse(symval(q_ovarlist)))
  |> ignore
  if symval(q_algfac_star).truthy() {
    set(q_genvar, cons(car(symval(q_ear_alpha)), symval(q_genvar))) |> ignore
  }
  poly = cpber3(poly, symval(q_ear_p))
  set(q_genvar, origenvar) |> ignore
  poly
}

///|
fn polysubst(a : Value, b : Value) -> Value raise {
  let bs = bind_all([(q_n_starinl3, Nil), (q_modulus, Nil)])
  defer unbind_all(bs)
  let mut a = a
  if symval(q_modulu_star).truthy() {
    set(q_modulus, symval(q_modulu_star)) |> ignore
  }
  set(q_n_starinl3, t) |> ignore
  let lc = caddr(symval(q_ear_p))
  let n = int(length(a))
  while true {
    let d = pcsubsty(a, b, lc)
    if !equal(Fix(0L), d) {
      let aa = a
      let d = with_special(q_modulus, Nil, () => pcsubsty(
        aa,
        b,
        symval(q_ear_p),
      ))
      if sqfrp(pmod(d), car(d)).truthy() {
        set(q_ear_p, d) |> ignore
        return a
      }
    }
    // inl
    a = increaselist(a, n)
  }
  Nil
}

///|
fn fixvl1(l : Value, r : Value) -> Value raise {
  let mut l = l
  let mut r = r
  while !(l is Nil) {
    if zerop(car(l)) {
      set(q_subval1, cons(car(l), symval(q_subval1))) |> ignore
      set(q_subvar1, cons(car(r), symval(q_subvar1))) |> ignore
    }
    l = cdr(l)
    r = cdr(r)
  }
  set(q_subval1, nreverse(symval(q_subval1))) |> ignore
  set(q_subvar1, nreverse(symval(q_subvar1))) |> ignore
  Nil
}

///|
fn fixvl(l : Value, r : Value) -> Value raise {
  let mut l = l
  let mut r = r
  while !(l is Nil) {
    if !zerop(car(l)) {
      set(q_subval, cons(car(l), symval(q_subval))) |> ignore
      set(q_subvar, cons(car(r), symval(q_subvar))) |> ignore
    }
    l = cdr(l)
    r = cdr(r)
  }
  set(q_subval, nreverse(symval(q_subval))) |> ignore
  set(q_subvar, nreverse(symval(q_subvar))) |> ignore
  Nil
}

///|
fn maxcoef(ear_p : Value) -> Value raise {
  maxcoefficient(ear_p)
}

///|
fn incrlimk(ear_p : Value) -> Value raise {
  if symval(q_modulu_star).truthy() {
    set(q_plim, symval(q_modulu_star)) |> ignore
    set(q_n_starprime, symval(q_modulu_star)) |> ignore
    set(q_limk, Fix(-1L)) |> ignore
    return Nil
  } else if symval(q_limk) is Nil {
    set(q_plim, symval(q_n_staralpha)) |> ignore
    set(q_n_starprime, symval(q_n_staralpha)) |> ignore
    set(q_limk, Fix(-1L)) |> ignore
    return Nil
  }
  let v = butlast(pdegreevector(ear_p))
  let factors = mapcar2(
    (a, b) => if equal(b, Fix(0L)) {
      Fix(1L)
    } else {
      let h = ash(a, -1)
      num_max(
        num_mul(ftake(q_p_binomial, [a, h]), expt(b, h)),
        expt(b, a),
      )
    },
    v,
    symval(q_valist),
  )
  let mut v : Value = Fix(1L)
  for x in factors.iter() {
    v = num_mul(v, x)
  }
  let min_plim = num_mul(num_max(maxcoef(ear_p), symval(q_plim)), v)
  while !num_lt(min_plim, symval(q_plim)) {
    set(q_limk, one_plus(symval(q_limk))) |> ignore
    set(q_plim, num_mul(symval(q_plim), symval(q_plim))) |> ignore
  }
  Nil
}

///|
fn increaselist(l : Value, n : Value) -> Value raise {
  let mut l = l
  if symval(q_n_starinl3).truthy() {
    l = inlist3(l)
  }
  if symval(q_n_starinl3).truthy() {
    l
  } else if equal(symval(q_elm), Fix(2L)) {
    if symval(q_modulu_star).truthy() {
      merr("factor: not enough choices for substitution.", [])
    } else {
      rand(n, Fix(13L))
    }
  } else if equal(symval(q_ne), n) {
    set(q_elm, one_plus(symval(q_elm))) |> ignore
    set(q_ne, Fix(1L)) |> ignore
    let bl = baselist(symval(q_ne))
    completevector(bl, symval(q_ne), n, symval(q_listelm))
  } else if equal(symval(q_ear_i), n) {
    set(q_ne, one_plus(symval(q_ne))) |> ignore
    let bl = baselist(symval(q_ne))
    completevector(bl, symval(q_ne), n, symval(q_listelm))
  } else {
    set(q_ear_i, one_plus(symval(q_ear_i))) |> ignore
    butlast(cons(symval(q_listelm), l))
  }
}

///|
/// Returns a list of N random numbers.  If MODULUS is set, then the numbers
/// will be modulo MODULUS.  Otherwise, between 0 and 1000.
fn rand(n : Value, modulus : Value) -> Value raise {
  let b = bind(q_modulus, modulus)
  defer unbind(b)
  let mut l : Value = Nil
  let mut i = to_int(n)
  while i != 0 {
    l = cons(mt_random(Fix(1000L)), l)
    i -= 1
  }
  if modulus.truthy() {
    mapcar(x => cmod(x), l)
  } else {
    l
  }
}

///|
fn trufac(
  v : Value,
  lp : Value,
  olfact : Value,
  many_star : Value,
  modulus : Value,
) -> Value raise {
  let bs = bind_all([(q_many_star, many_star), (q_modulus, modulus)])
  defer unbind_all(bs)
  let mut v = v
  let mut lp = lp
  let mut lc : Value = Fix(1L)
  let mut olc : Value = Fix(1L)
  let mut factor : Value = Nil
  set_modulus(modulus) |> ignore
  let olfact = cons(Nil, olfact)
  let mut lfunct = olfact
  while true {
    // test
    if equal(v, Fix(1L)) {
      return factor
    } else if lp is Nil {
      return if length(olfact) < 4 {
        cons(v, factor)
      } else {
        let o = olc
        let first_ = with_special(q_modulus, symval(q_plim), () => ptimes(
          o,
          cadr(olfact),
        ))
        nconc(factor, nprod(lc, v, cons(first_, cddr(olfact))))
      }
    } else if cdr(lp) is Nil && (cdr(olfact) is Nil || cddr(olfact) is Nil) {
      return cons(v, factor)
    }
    let af = car(lp)
    let vv = v
    let qnt = with_special(q_modulus, symval(q_modulu_star), () => testdivide(
      vv,
      af,
    ))
    if qnt.truthy() {
      factor = cons(af, factor)
      lc = ptimes(lc, caddr(af))
      v = qnt
      let o = olc
      let lf = lfunct
      olc = with_special(q_modulus, symval(q_plim), () => ptimes(
        caddr(cadr(lf)),
        o,
      ))
      rplacd(lfunct, cddr(lfunct)) |> ignore
    } else {
      lfunct = cdr(lfunct)
    }
    lp = cdr(lp)
  }
  Nil
}

///|
fn multideg(ear_p : Value) -> Value raise {
  if numberp(ear_p) {
    return Fix(0L)
  } else if onevarp(ear_p).truthy() {
    return cadr(ear_p)
  }
  let mut p = cdr(ear_p)
  let mut m = car(p)
  while !(p is Nil) {
    let d = num_add(car(p), multideg(cadr(p)))
    p = cddr(p)
    m = num_max(d, m)
  }
  m
}

///|
/// Return a list of the first, third etc. elements of list.
fn oddelm(list_ : Value) -> Value raise {
  let c = Collector::new()
  let mut l = list_
  while l is Cons(_) {
    c.add(car(l))
    l = cddr(l)
  }
  c.result()
}

///|
fn cpber3(v : Value, u : Value) -> Value raise {
  let bs = bind_all([
    (q_alcinv, Nil),
    (q_plim, Nil),
    (q_monic_star, Nil),
    (q_sharpcont, Nil),
    (q_limk, Nil),
    (q_var, Nil),
  ])
  defer unbind_all(bs)
  let mut v = v
  let mut u = u
  set(q_var, car(u)) |> ignore
  if symval(q_algfac_star).truthy() && !atom(caddr(u)) {
    set(q_alc, caddr(u)) |> ignore
    set(q_alcinv, rainv(symval(q_alc))) |> ignore
    u = ptimes(u, car(symval(q_alcinv)))
    v = ptimes(v, car(symval(q_alcinv)))
    set(q_adn_star, num_mul(symval(q_adn_star), cdr(symval(q_alcinv))))
    |> ignore
  }
  u = oldcontent(u)
  set(q_sharpcont, car(u)) |> ignore
  u = cadr(u)
  let mut lc = caddr(v)
  if equal(lc, Fix(1L)) {
    set(q_monic_star, t) |> ignore
  }
  let mut factz = fact5(u)
  // this is the barry trick
  if symval(q_ear_stop).truthy() {
    set(q_ear_stop, symval(q_plim)) |> ignore
    return cons(car(symval(q_subval)), factz)
  }
  if cdr(factz) is Nil {
    return list1(v)
  } else if symval(q_algfac_star).truthy() &&
    !equal(symval(q_adn_star), Fix(1L)) {
    v = pctimes(symval(q_adn_star), v)
    lc = pctimes(symval(q_adn_star), lc)
  }
  incrlimk(v) |> ignore
  set(q_modulus, symval(q_plim)) |> ignore
  u = v
  v = newrep(v)
  if numberp(car(factz)) {
    set(q_sharpcont, ptimes(symval(q_sharpcont), car(factz))) |> ignore
    factz = cdr(factz)
  }
  if !equal(symval(q_sharpcont), Fix(1L)) {
    factz = cons(ptimes(symval(q_sharpcont), car(factz)), cdr(factz))
  }
  let mut vfact = zfact(v, factz, symval(q_limk), t)
  factz = if symval(q_monic_star).truthy() {
    reverse(vfact)
  } else {
    restorelc(vfact, newrep(lc))
  }
  if symval(q_algfac_star).truthy() && !equal(symval(q_adn_star), Fix(1L)) {
    v = pctimes(crecip(symval(q_adn_star)), v)
    set(q_adn_star, Fix(1L)) |> ignore
  }
  vfact = trufac(v, factz, nreverse(vfact), t, symval(q_modulu_star))
  if cdr(vfact) is Nil {
    list1(u)
  } else {
    mapcar(x => oldrep(x), vfact)
  }
}

///|
/// A tuple is a sorted list of distinct positive indices - ORDE builds them
/// that way, and the (MEMBER L TUPLE) guard keeps them distinct - so the set
/// of indices is a faithful key for it.
fn nprod_tuple_key(l : Value) -> Value raise {
  let mut k : Value = Fix(0L)
  for i in l.iter() {
    k = logior(k, ash(Fix(1L), to_int(i)))
  }
  k
}

///|
fn nprod_reindex(h : Value, lt : Value) -> Value raise {
  clrhash(h) |> ignore
  for e in lt.iter() {
    if e.truthy() {
      sethash(nprod_tuple_key(e), h, t) |> ignore
    }
  }
  Nil
}

///|
fn nprod(lc : Value, u : Value, lfunct : Value) -> Value raise {
  let bm = bind(q_modulus, Nil)
  defer unbind(bm)
  let mut u = u
  let mut ltemp = cons(Nil, Nil)
  let mut lpr = copy_tree(ltemp)
  // SEEN mirrors the set of tuples in LTEMP, so that "Have we tried this
  // combination?" is a hash lookup; the tails make appending to LTEMP and
  // LPR O(1).  Neither changes what is searched, in what order, or what is
  // returned.
  let seen = make_hash_table(kind=Eql)
  let mut ltemp_tail = ltemp
  let mut lpr_tail = lpr
  let mut lprod = cons(Nil, lfunct)
  let mut d2 = ash(cadr(u), -1)
  remov0(lprod, d2) |> ignore
  let mut lfunct = cdr(lprod)
  let mut r = int(length(lfunct))
  let mut lindex = index_star(r)
  let mut llc : Value = Nil
  let mut lcindex : Value = Nil
  let mut v : Value = Nil
  let mut factor : Value = Nil
  if !symval(q_monic_star).truthy() {
    llc = mapcar(x => caddr(x), lfunct)
    lcindex = copy_list(lindex)
    remov3(llc, lcindex) |> ignore
    v = ptimes(lc, ptimes(caddr(u), u))
  } else {
    v = u
  }
  let mut ltuple = cons(Nil, mapcar(x => list1(x), lindex))
  let mut stage : Value = Fix(1L)
  lindex = cons(Nil, lindex)
  lfunct = copy_list(lprod)
  while true {
    // tloop
    stage = one_plus(stage)
    while true {
      // nextuple
      if num_gt(stage, d2) ||
        num_gt(stage, one_minus(r)) ||
        ltuple is Nil ||
        cdr(ltuple) is Nil {
        return cons(u, factor)
      }
      let mut li = cdr(lindex)
      let mut lf = cdr(lfunct)
      let tuple = cadr(ltuple)
      let funct = cadr(lprod)
      rplacd(ltuple, cddr(ltuple)) |> ignore
      rplacd(lprod, cddr(lprod)) |> ignore
      while true {
        // iloop
        let mut l = car(li)
        let f = car(lf)
        li = cdr(li)
        lf = cdr(lf)
        if member_equal(l, tuple) is Nil &&
          !num_gt(num_add(cadr(f), cadr(funct)), d2) &&
          {
            l = orde(l, tuple)
            !gethash(nprod_tuple_key(l), seen).truthy()
          } {
          set_modulus(symval(q_plim)) |> ignore
          let af0 = ptimes(pmod(f), pmod(funct))
          let mut af = af0
          if llc.truthy() {
            af = ptimes(pmod(lchk(llc, lcindex, l)), af)
          }
          if symval(q_many_star).truthy() {
            af = dropterms(af)
          } else if factor__intbase_case_nprod() {
            af = intbasehk(af)
          }
          set_modulus(Nil) |> ignore
          let qnt = testdivide(v, af)
          if qnt.truthy() {
            if llc.truthy() {
              let afc = oldcontent(af)
              v = ptimes(car(afc), qnt)
              af = cadr(afc)
              let a2 = af
              let uu = u
              u = if symval(q_algfac_star).truthy() {
                car(factor__ignore_rat_err(() => rquotient(uu, a2)))
              } else {
                pquotient(u, af)
              }
            } else {
              u = qnt
              v = qnt
            }
            factor = cons(af, factor)
            if equal(u, Fix(1L)) {
              return factor
            }
            d2 = ash(cadr(u), -1)
            if num_lt(d2, stage) {
              return cons(u, factor)
            }
            remov1(l, ltuple, lprod, d2) |> ignore
            remov1(l, ltemp, lpr, d2) |> ignore
            remov2(l, lindex, lfunct, d2) |> ignore
            nprod_reindex(seen, ltemp) |> ignore
            ltemp_tail = last(ltemp)
            lpr_tail = last(lpr)
            r = num_sub(r, stage)
            li = Nil // exit iloop
          } else {
            if ltemp_tail.truthy() {
              let c = list1(l)
              setf_cdr(ltemp_tail, c) |> ignore
              ltemp_tail = c
            } else {
              ltemp = list1(l)
              ltemp_tail = ltemp
            }
            sethash(nprod_tuple_key(l), seen, t) |> ignore
            if lpr_tail.truthy() {
              let c = list1(af0)
              setf_cdr(lpr_tail, c) |> ignore
              lpr_tail = c
            } else {
              lpr = list1(af0)
              lpr_tail = lpr
            }
          }
        }
        if !li.truthy() {
          break
        }
      }
      if !(cdr(ltuple) is Nil) {
        continue // nextuple
      }
      break
    }
    ltuple = ltemp
    lprod = lpr
    ltemp = Nil
    lpr = Nil
    ltemp_tail = Nil
    lpr_tail = Nil
    clrhash(seen) |> ignore
  }
  Nil
}

///|
fn factor__intbase_case_nprod() -> Bool {
  symval(q_algfac_star).truthy() && !equal(symval(q_intbs_star), Fix(1L))
}

///|
fn remov2(a : Value, b : Value, c : Value, d2 : Value) -> Value raise {
  let mut b = b
  let mut c = c
  while !(cdr(b) is Nil) {
    if member_equal(cadr(b), a).truthy() || num_gt(cadadr(c), d2) {
      rplacd(b, cddr(b)) |> ignore
      rplacd(c, cddr(c)) |> ignore
    } else {
      b = cdr(b)
      c = cdr(c)
    }
  }
  Nil
}

///|
fn remov1(a : Value, lt1 : Value, lp1 : Value, d2 : Value) -> Value raise {
  let mut lt1 = lt1
  let mut lp1 = lp1
  while !(cdr(lt1) is Nil) {
    if !num_gt(cadadr(lp1), d2) &&
      intersection(a, cadr(lt1), pred2=(x, y) => equal(x, y)) is Nil {
      lt1 = cdr(lt1)
      lp1 = cdr(lp1)
    } else {
      rplacd(lt1, cddr(lt1)) |> ignore
      rplacd(lp1, cddr(lp1)) |> ignore
    }
  }
  Nil
}

///|
fn remov0(lf : Value, d2 : Value) -> Value raise {
  let d = lf
  let mut lf = lf
  while !(cdr(lf) is Nil) {
    if num_gt(cadadr(lf), d2) {
      let d2 = caddr(cadr(lf))
      rplacd(lf, cddr(lf)) |> ignore
      if !equal(d2, Fix(1L)) {
        rplacd(d, cons(ptimes(d2, cadr(d)), cddr(d))) |> ignore
      }
      return Nil
    }
    lf = cdr(lf)
  }
  Nil
}

///|
fn remov3(a : Value, b : Value) -> Value raise {
  let mut a = a
  let mut b = b
  while !(cdr(a) is Nil) {
    if equal(cadr(a), Fix(1L)) {
      rplacd(a, cddr(a)) |> ignore
      rplacd(b, cddr(b)) |> ignore
    } else {
      a = cdr(a)
      b = cdr(b)
    }
  }
  Nil
}

///|
fn lchk(a : Value, b : Value, c : Value) -> Value raise {
  let mut ans : Value = Fix(1L)
  let mut a = a
  let mut b = b
  while !(a is Nil) {
    if member_equal(car(b), c) is Nil {
      ans = ptimes(ans, car(a))
    }
    a = cdr(a)
    b = cdr(b)
  }
  ans
}

///|
fn lcprodl(l : Value) -> Value raise {
  let mut d : Value = Fix(1L)
  let mut l = reverse(l)
  let mut ans = list1(Fix(1L))
  while !(cdr(l) is Nil) {
    d = ptimes(d, caddar(l))
    l = cdr(l)
    ans = cons(d, ans)
  }
  ans
}

///|
fn fact5(poly : Value) -> Value raise {
  let bs = bind_all([
    (q_trl_star, Nil),
    (q_uu_star, Nil),
    (q_modulus, Nil),
    (q_monic_star, Nil),
    (q_split_star, Nil),
    (q_var, Nil),
    (q_anotype, Nil),
    (q_fctc, Nil),
    (q_invc, Nil),
    (q_ear_afixn, Nil),
    (q_ear_fctcfixn, Nil),
    (q_ear_invcfixn, Nil),
  ])
  defer unbind_all(bs)
  let mut poly = poly
  let mut ql : Value = Nil
  let mut linfac : Value = Nil
  let mut factp : Value = Nil
  set(q_var, car(poly)) |> ignore
  if cdddr(poly) is Nil {
    return list1(poly)
  }
  let algfac = symval(q_algfac_star).truthy()
  if algfac && !atom(caddr(poly)) {
    set(q_alc, caddr(poly)) |> ignore
    set(q_alcinv, rainv(symval(q_alc))) |> ignore
    poly = rattimes(cons(poly, Fix(1L)), symval(q_alcinv), t)
    set(q_adn_star, num_mul(symval(q_adn_star), cdr(poly))) |> ignore
    poly = car(poly)
  }
  let minpoly = symval(q_minpoly_star)
  let splitcase = algfac &&
    minpoly.truthy() &&
    (symval(q_d_nalgfac).truthy() ||
    equal(cdr(minpoly), list([Fix(4L), Fix(1L), Fix(0L), Fix(1L)])))
  let mut lc : Value = Nil
  if splitcase {
    ql = q_splitcase
  } else {
    set(q_uu_star, poly) |> ignore
    lc = caddr(symval(q_uu_star))
    if equal(lc, Fix(1L)) {
      set(q_monic_star, t) |> ignore
    }
    let deg = to_int(cadr(poly))
    if !algfac {
      set(q_ear_fctcfixn, make_array([deg], initial=Fix(0L))) |> ignore
      set(q_ear_invcfixn, make_array([deg], initial=Fix(0L))) |> ignore
      set(q_ear_afixn, make_array([deg, deg], initial=Fix(0L))) |> ignore
    } else {
      let mm = to_int(symval(q_mm_star))
      set(q_fctc, make_array([deg])) |> ignore
      set(q_invc, make_array([deg])) |> ignore
      set(q_anotype, make_array([deg, deg])) |> ignore
      set(q_ear_fctcfixn, make_array([mm], initial=Fix(0L))) |> ignore
      set(q_ear_invcfixn, make_array([mm], initial=Fix(0L))) |> ignore
      set(q_ear_afixn, make_array([mm, mm], initial=Fix(0L))) |> ignore
    }
    if symval(q_modulu_star).truthy() {
      return fact5mod(poly)
    }
    ql = choozp(symval(q_uu_star))
    if !atom(ql) {
      linfac = car(ql)
      set(q_uu_star, caddr(ql)) |> ignore
      ql = cadr(ql)
    }
    set(q_n_starprime, symval(q_modulus)) |> ignore
  }
  // tag0
  if eq(ql, q_splitcase) {
    poly = nalgfac(
      poly,
      cons(car(symval(q_ear_alpha)), cdr(symval(q_minpoly_star))),
    )
    set(q_plim, symval(q_n_staralpha)) |> ignore
    set(q_n_starprime, symval(q_plim)) |> ignore
    set(q_limk, Fix(-1L)) |> ignore
    return poly
  } else if cdr(append(linfac, ql)) is Nil {
    return list1(poly)
  }
  if equal(symval(q_uu_star), Fix(1L)) {
    factp = Nil
  } else {
    if algfac {
      factp = cpbgzass(ql, symval(q_uu_star), int(length(ql)))
    } else if !equal(symval(q_uu_star), Fix(1L)) {
      factp = cpbg(ql, symval(q_uu_star), int(length(ql)))
    }
    set(q_uu_star, Nil) |> ignore
  }
  // on
  factp = nconc(factp, linfac)
  factp = cons(pctimes(pmod(lc), car(factp)), cdr(factp))
  set(q_limk, klim(poly, symval(q_modulus))) |> ignore
  let factz = zfact(poly, factp, symval(q_limk), Nil)
  let fz = factz
  let rl = with_special(q_modulus, symval(q_plim), () => restorelc(fz, lc))
  poly = trufac(poly, rl, nreverse(factz), Nil, Nil)
  set(q_modulus, Nil) |> ignore
  poly
}

///|
fn fact5mod(u : Value) -> Value raise {
  let mut poly = copy_list(u)
  set_modulus(symval(q_modulu_star)) |> ignore
  poly = pmod(poly)
  let lc = caddr(poly)
  pmonicize(cdr(poly)) |> ignore
  poly = cpberl(poly)
  if cdr(poly) is Nil {
    list1(u)
  } else if num_eq(lc, Fix(1L)) {
    poly
  } else {
    cons(lc, poly)
  }
}

///|
fn cpbg(qlist : Value, v : Value, m : Value) -> Value raise {
  if num_eq(m, Fix(1L)) {
    return list1(v)
  }
  let p1 = ash(symval(q_modulus), -1)
  let mut p2 : Value = Fix(1L)
  let mut qlist = cdr(nreverse(qlist))
  let mut oldfac = list2(Nil, v)
  let mut fnq : Value = Nil
  let mut fnj : Value = Nil
  let mut factors : Value = Nil
  let mut vj : Value = Nil
  let mut j : Value = Nil
  // states: 0 tag3, 1 incrj, 2 tag2, 3 agg, 4 tag1, 5 out
  let mut state = 0
  while state != 5 {
    match state {
      0 => {
        vj = nconc(car(qlist), list2(Fix(0L), Fix(0L)))
        qlist = cdr(qlist)
        j = num_neg(p1)
        oldfac = nconc(oldfac, fnq)
        fnq = Nil
        state = 1
      }
      1 => {
        factors = nconc(oldfac, fnj)
        fnj = Nil
        pcdifconc(vj, j) |> ignore
        state = 2
      }
      2 => {
        let u = cadr(factors)
        let w = pgcdu(vj, u)
        if numberp(w) || num_eq(cadr(w), cadr(u)) {
          state = 3
        } else {
          let y = car(pmodquo(u, w))
          fnq = cons(copy_list(w), fnq)
          fnj = cons(y, fnj)
          p2 = one_plus(p2)
          rplacd(factors, cddr(factors)) |> ignore
          state = if equal(p2, m) { 5 } else { 4 }
        }
      }
      3 => {
        factors = cdr(factors)
        state = 4
      }
      _ =>
        if !(cdr(factors) is Nil) {
          state = 2
        } else if num_lt(j, p1) {
          j = one_plus(j)
          state = 1
        } else if qlist.truthy() {
          state = 0
        } else {
          state = 5
        }
    }
  }
  nconc(fnq, nconc(fnj, cdr(oldfac)))
}

///|
fn fact2z(u : Value, f : Value, g : Value, limk : Value) -> Value raise {
  let bs = bind_all([(q_limk, limk), (q_ear_p, Nil)])
  defer unbind_all(bs)
  let mut f = f
  let mut g = g
  let mut k : Value = Fix(0L)
  set(q_ear_p, symval(q_modulus)) |> ignore
  let r0 = ppprog(f, g)
  let mut a = car(r0)
  let mut b = cadr(r0)
  let ff = f
  let gg = g
  let mut r = with_special(q_modulus, Nil, () => pdifference(ptimes(ff, gg), u))
  let mut pk : Value = Nil
  let mut mpk : Value = Nil
  while true {
    // sharp
    if equal(r, Fix(0L)) || num_gt(k, symval(q_limk)) {
      break
    }
    pk = symval(q_modulus)
    mpk = num_neg(pk)
    set(q_modulus, num_mul(symval(q_modulus), symval(q_modulus))) |> ignore
    let w = pmod(r)
    if !equal(w, Fix(0L)) {
      let c = npquo(w, pk)
      let ql = pmodquo(ptimes(a, c), g)
      let a1 = npctimes(mpk, pplus(ptimes(car(ql), f), ptimes(b, c)))
      let b1 = npctimes(mpk, cdr(ql))
      let (nr, nf, ng) = with_special(q_modulus, symval(q_plim), () => {
        let nr = pplus(pplus(r, ptimes(a1, b1)), pplus(ptimes(a1, g), ptimes(b1, f)))
        let nf = pplus(f, a1)
        let ng = pplus(g, b1)
        (nr, nf, ng)
      })
      r = nr
      f = nf
      g = ng
    }
    // tag1
    k = one_plus(k)
    if equal(r, Fix(0L)) || num_gt(k, symval(q_limk)) {
      break
    }
    let h = npquo(pplus(pplus(ptimes(a, f), ptimes(b, g)), Fix(-1L)), pk)
    let qlp = pmodquo(ptimes(a, h), g)
    let b1 = pplus(ptimes(b, h), ptimes(car(qlp), f))
    a = pplus(a, npctimes(mpk, cdr(qlp)))
    b = pplus(b, npctimes(mpk, b1))
  }
  // on
  set_modulus(symval(q_ear_p)) |> ignore
  list2(f, g)
}

///|
fn npctimes(c : Value, ear_p : Value) -> Value raise {
  let p = npctimes1(c, ear_p)
  if !atom(p) && cdr(p) is Nil {
    Fix(0L)
  } else {
    p
  }
}

///|
fn npquo(ear_p : Value, c : Value) -> Value raise {
  let b = bind(q_modulus, Nil)
  defer unbind(b)
  if equal(c, Fix(1L)) {
    return ear_p
  } else if pcoefp(ear_p).truthy() {
    return quot(ear_p, c)
  }
  let mut u = ear_p
  while !(cdr(u) is Nil) {
    u = cddr(u)
    rplaca(
      u,
      if pcoefp(car(u)).truthy() {
        quot(car(u), c)
      } else {
        npquo(copy_list(car(u)), c)
      },
    )
    |> ignore
  }
  ear_p
}

///|
fn npctimes1(c : Value, ear_p : Value) -> Value raise {
  if equal(c, Fix(1L)) {
    return ear_p
  } else if pcoefp(ear_p).truthy() {
    return ctimes(c, ear_p)
  }
  let mut u = ear_p
  while !(cdr(u) is Nil) {
    let a = if pcoefp(caddr(u)).truthy() {
      ctimes(c, caddr(u))
    } else {
      npctimes(c, copy_list(caddr(u)))
    }
    if equal(a, Fix(0L)) {
      rplacd(u, cdddr(u)) |> ignore
    } else {
      u = cddr(u)
      rplaca(u, a) |> ignore
    }
  }
  ear_p
}

///|
fn x_star_starq1(term : Value, u : Value, m : Value, ear_p : Value) -> Value raise {
  let mut term = term
  let mut i : Value = Fix(1L)
  set(q_trl_star, list1(term)) |> ignore
  while !num_eq(i, m) {
    term = pexptmod(term, ear_p, u)
    set(q_trl_star, cons(term, symval(q_trl_star))) |> ignore
    i = one_plus(i)
  }
  pexptmod(term, ear_p, u)
}

///|
fn cptomf(ear_p : Value, u : Value, n : Value) -> Value raise {
  let bs = bind_all([(q_n_starxn, Nil), (q_ind, Nil)])
  defer unbind_all(bs)
  let p = to_int(ear_p)
  let n = to_int(n)
  let n_1 = n - 1
  let afixn = symval(q_ear_afixn)
  let mut s : Value = Nil
  let mut j = 0
  let mut i = 0
  while true {
    // loop
    j += 1
    if j == n {
      return Nil
    }
    let mut do_st = false
    if symval(q_ind).truthy() {
      i = p // sa
    } else if p * j > n_1 {
      set(
        q_n_starxn,
        mapcar(x => num_neg(x), p2cpol(cddr(u), int(n_1))),
      )
      |> ignore
      s = copy_tree(symval(q_n_starxn))
      set(q_ind, t) |> ignore
      i = p * j - n
    } else {
      s = p2cpol(list3(symval(q_var), int(p * j), Fix(1L)), int(n_1))
      do_st = true
    }
    if !do_st {
      // sa1
      while i != 0 {
        cptimesx(s) |> ignore
        i -= 1
      }
    }
    // st
    if j == 1 &&
      equal(list2(Fix(1L), Fix(0L)), algfac__last2(s)) &&
      num_eq(Fix(1L), num_sum(list_to_array(s))) {
      return set(q_split_star, t)
    }
    let mut l = s
    i = n_1
    while !(l is Nil) {
      aset(afixn, [j, i], car(l)) |> ignore
      l = cdr(l)
      i -= 1
    }
    // on
    aset(afixn, [j, j], one_minus(aref(afixn, [j, j]))) |> ignore
  }
  Nil
}

///|
fn p2cpol(ear_p : Value, n : Value) -> Value raise {
  let mut p = cdr(ear_p)
  let mut n = n
  let mut l : Value = Nil
  while !num_eq(n, Fix(-1L)) {
    if p is Nil || num_gt(n, car(p)) {
      l = cons(Fix(0L), l)
    } else if num_eq(n, car(p)) {
      l = cons(cadr(p), l)
      p = cddr(p)
    }
    n = one_minus(n)
  }
  nreverse(l)
}

///|
fn cptimesx(ear_p : Value) -> Value raise {
  let mut xn = symval(q_n_starxn)
  let mut q = ear_p
  let lc = car(ear_p)
  while true {
    if !(cdr(q) is Nil) {
      rplaca(q, cplus(cadr(q), ctimes(lc, car(xn)))) |> ignore
      q = cdr(q)
      xn = cdr(xn)
    } else {
      rplaca(q, ctimes(lc, car(xn))) |> ignore
      return ear_p
    }
  }
  Nil
}

///|
fn cmnullf(n : Value) -> Value raise {
  let n_1 = to_int(n) - 1
  let mone = cmod(Fix(-1L))
  let afixn = symval(q_ear_afixn)
  let fa = symval(q_ear_fctcfixn)
  let ia = symval(q_ear_invcfixn)
  for i in 0..=n_1 {
    aset1(fa, i, Fix(-1L)) |> ignore
    aset1(ia, i, Fix(-1L)) |> ignore
  }
  let ga = (r : Int, c : Int) => aref(afixn, [r, c])
  let sa = (r : Int, c : Int, v : Value) => aset(afixn, [r, c], v)
  let mut nullsp = list1(Fix(1L))
  let mut k = 1
  while k <= n_1 {
    let mut j = 0
    // n3a
    while j <= n_1 &&
      (num_eq(ga(k, j), Fix(0L)) || num_gt(aref1(fa, j), Fix(-1L))) {
      j += 1
    }
    if j > n_1 {
      // null
      let mut nullv : Value = Nil
      for s in 0..=n_1 {
        if s == k {
          nullv = cons(int(s), cons(Fix(1L), nullv))
        } else if num_gt(aref1(ia, s), Fix(-1L)) {
          let vj = ga(k, to_int(aref1(ia, s)))
          if !num_eq(vj, Fix(0L)) {
            nullv = cons(int(s), cons(vj, nullv))
          }
        }
      }
      if equal(car(nullv), Fix(0L)) {
        nullv = cadr(nullv)
      } else {
        nullv = cons(symval(q_var), nullv)
      }
      nullsp = cons(nullv, nullsp)
    } else {
      aset1(ia, k, int(j)) |> ignore
      aset1(fa, j, int(k)) |> ignore
      let m = crecip(ctimes(mone, ga(k, j)))
      for s in k..=n_1 {
        sa(s, j, ctimes(m, ga(s, j))) |> ignore
      }
      // go through columns
      for s in 0..=n_1 {
        // go through rows in each column
        if s != j {
          let aks = ga(k, s)
          for i in k..=n_1 {
            sa(i, s, cplus(ga(i, s), ctimes(ga(i, j), aks))) |> ignore
          }
        }
      }
    }
    // nextk
    k += 1
  }
  nullsp
}

///|
let factor__gauss_primes : Value = list(
  [3L, 7, 11, 19, 23, 29, 31, 37].map(x => Fix(x)),
)

///|
fn choozp(v : Value) -> Value raise {
  let mut tr : Value = Nil
  let mut ncont = 1
  let mut bmod : Value = Nil
  let mut b : Value = Nil
  let mut mincont = 0
  let mut lmin = 0
  let deg = cadr(v)
  let mut algcont = 0
  let nf = integer_length(deg)
  let mut lchar1 = if symval(q_gauss).truthy() {
    factor__gauss_primes
  } else {
    cdr(symval(q_ear_small_primes))
  }
  let algfac = symval(q_algfac_star).truthy()
  while true {
    // test
    set(q_modulus, car(lchar1)) |> ignore
    let modulus = symval(q_modulus)
    let u = pmod(v)
    let mut skip = zerop(num_rem(symval(q_sharpcont), modulus)) ||
      (!symval(q_monic_star).truthy() &&
      (pcoefp(u).truthy() || num_gt(deg, cadr(u))))
    if !skip &&
      (!sqfrp(u, symval(q_var)).truthy() ||
      (algfac &&
      !symval(q_gauss).truthy() &&
      !iredup(pmod(symval(q_minpoly_star))).truthy())) {
      algcont += 1
      skip = true
    }
    if !skip {
      pmonicize(cdr(u)) |> ignore
      let b1 = catch_tag(q_splt, () => cpber1(u))
      algcont = 0
      ncont += 1
      let n = length(car(b1)) + length(cadr(b1))
      if lmin == 0 || n < lmin {
        lmin = n
        mincont = 1
        bmod = modulus
        b = b1
        if algfac {
          tr = symval(q_trl_star)
        }
      } else if n == lmin {
        mincont += 1
      }
      if ncont > nf || !(n > nf) || mincont == 3 {
        break // out
      }
    }
    // nextp
    lchar1 = cdr(lchar1)
    if lchar1 is Nil {
      if lmin != 0 {
        break // out
      } else {
        merr("factor: ran out of primes.", []) |> ignore
      }
    } else if algfac && symval(q_minpoly_star).truthy() && algcont > 6 {
      if ziredup(symval(q_minpoly_star)).truthy() {
        set(q_trl_star, tr) |> ignore
        set(q_modulus, Nil) |> ignore
        return q_splitcase
      } else {
        merr(
          "factor: the minimal polynomial must be irreducible over the integers.",
          [],
        )
        |> ignore
      }
    }
  }
  // out
  set(q_modulus, bmod) |> ignore
  set(q_trl_star, tr) |> ignore
  b
}

///|
fn cpbq1(a : Value, n : Value) -> Value raise {
  set(q_split_star, Nil) |> ignore
  let modulus = symval(q_modulus)
  if !integerp(modulus) {
    n_stararray(q_a, t, list2(n, n)) |> ignore
  }
  if symval(q_algfac_star).truthy() || !integerp(modulus) {
    cptom(modulus, symval(q_mm_star), a, n) |> ignore
  } else {
    cptomf(modulus, a, n) |> ignore
  }
  if symval(q_split_star).truthy() {
    return powrs(car(a), cadr(a))
  }
  if symval(q_algfac_star).truthy() || !integerp(symval(q_modulus)) {
    cmnull(n)
  } else {
    cmnullf(n)
  }
}

///|
fn cpber1(u : Value) -> Value raise {
  set(q_var, car(u)) |> ignore
  let linfac = linout(u)
  let u = car(linfac)
  let linfac = cadr(linfac)
  if equal(u, Fix(1L)) {
    return list3(linfac, Nil, u)
  }
  list3(linfac, cpbq1(u, cadr(u)), u)
}

///|
fn factor1972(ear_p : Value) -> Value raise {
  let bs = bind_all([
    (q_modulu_star, symval(q_modulus)),
    (q_many_star, Nil),
    (q_ear_stop, Nil),
    (q_modulus, Nil),
    (q_mcflag, Nil),
    (q_ear_negflag, Nil),
  ])
  defer unbind_all(bs)
  if atom(ear_p) ||
    numberp(ear_p) ||
    (symval(q_algfac_star).truthy() && alg(ear_p).truthy()) {
    list1(ear_p)
  } else {
    factor72(ear_p)
  }
}

///|
fn factor72(ear_p : Value) -> Value raise {
  let bs = bind_all([(q_sharpcont, Fix(1L)), (q_plim, Nil)])
  defer unbind_all(bs)
  let p = if onevarp(ear_p).truthy() {
    mapcar(x => posize(x), fact5(ear_p))
  } else {
    set(q_many_star, t) |> ignore
    multfact(ear_p)
  }
  if symval(q_ear_negflag).truthy() {
    cons(pminus(car(p)), cdr(p))
  } else {
    p
  }
}

///|
fn posize(ear_p : Value) -> Value raise {
  if pminusp(ear_p).truthy() {
    set(q_ear_negflag, lbool(!symval(q_ear_negflag).truthy())) |> ignore
    pminus(ear_p)
  } else {
    ear_p
  }
}
