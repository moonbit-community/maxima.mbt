// Port of src/algfac.lisp: the algebraic factoring package (Berlekamp and
// Zassenhaus splitting over finite fields extended by an algebraic number).
//
// Toplevel functions are CPBGZASS and CPTOM.

///|
fn ziredup(p : Value) -> Value raise {
  let bs = bind_all([
    (q_modulus, Nil),
    (q_ear_alpha, Nil),
    (q_minpoly_star, Nil),
    (q_algfac_star, Nil),
    (q_gauss, Nil),
    (q_tellratlist, Nil),
    (q_many_star, Nil),
    (q_mm_star, Fix(1L)),
    (q_d_gcd, q_d_ez),
  ])
  defer unbind_all(bs)
  lbool(cddr(pfactor(p)) is Nil)
}

///|
fn intbasehk(p : Value) -> Value raise {
  let b = bind(q_modulus, Nil)
  defer unbind(b)
  set(q_modulus, symval(q_plim)) |> ignore
  let p = pctimes(symval(q_intbs_star), p)
  set(q_modulus, Nil) |> ignore
  car(ratreduce(p, symval(q_intbs_star)))
}

///|
fn findibase(p : Value) -> Value raise {
  let mainvar = car(p)
  let mut p = redresult(p, pderivative(p, mainvar))
  p = cfactorw(p)
  let mut mainvar : Value = Fix(1L)
  while !(p is Nil) {
    mainvar = num_mul(mainvar, expt(car(p), quot(cadr(p), Fix(2L))))
    p = cddr(p)
  }
  mainvar
}

///|
fn cpbgzass(qlist : Value, v : Value, m : Value) -> Value raise {
  if equal(m, Fix(1L)) {
    return list1(v)
  } else if equal(m, cadr(v)) {
    let var_ = symval(q_var)
    return with_special(q_var, list3(var_, Fix(1L), Fix(1L)), () => gfsplit(v))
  }
  let mut f = pmod(v)
  let lc = caddr(f)
  f = monize(f)
  let mut p2 : Value = Fix(1L)
  let mut qlist = cdr(nreverse(qlist))
  let mut oldfac = list2(Nil, f)
  let mut fnq : Value = Nil
  let mut fnj : Value = Nil
  let mut factors : Value = Nil
  let mut j : Value = Nil
  let mut v : Value = Nil
  let mut vj : Value = Nil
  // states: 0 nextq, 1 incrj, 2 tag2, 3 nextfac, 4 tag1, 5 out
  let mut state = 0
  while state != 5 {
    match state {
      0 => {
        v = car(qlist)
        qlist = cdr(qlist)
        j = findses(v, f)
        oldfac = nconc(oldfac, fnq)
        fnq = Nil
        state = 1
      }
      1 => {
        factors = nconc(oldfac, fnj)
        fnj = Nil
        vj = pplus(v, car(j))
        j = cdr(j)
        state = 2
      }
      2 => {
        let u = cadr(factors)
        let w = pgcdu(vj, u)
        if numberp(w) ||
          (symval(q_ear_alpha).truthy() && alg(w).truthy()) ||
          num_eq(cadr(u), cadr(w)) {
          state = 3
        } else {
          let y = car(pmodquo(u, w))
          fnq = cons(w, fnq)
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
        state = if !(cdr(factors) is Nil) {
          2
        } else if j.truthy() {
          1
        } else if qlist.truthy() {
          0
        } else {
          5
        }
    }
  }
  fnq = nconc(fnq, nconc(fnj, cdr(oldfac)))
  cons(ptimes(lc, car(fnq)), cdr(fnq))
}

// The function PMONZ used to be defined here.  It is also defined in
// RAT;RAT3A and BMT claims the definitions are equivalent.

///|
fn findses(g : Value, f : Value) -> Value raise {
  let bs = bind_all([(q_var, Nil), (q_tra_star, Nil), (q_trl_star, Nil)])
  defer unbind_all(bs)
  let g = zassg(cdr(g), cdr(f), car(g))
  set(q_var, list3(car(f), Fix(1L), Fix(1L))) |> ignore
  let f = gfsplit(g)
  mapcar(a => car(last(a)), f)
}

///|
fn coefvec(p : Value, n : Value, vec : Value) -> Value raise {
  let mut n = n
  let mut vec = vec
  while !zerop(n) {
    n = one_minus(n)
    vec = cons(ptterm(p, n), vec)
  }
  vec
}

///|
fn zassg(g : Value, f : Value, var_ : Value) -> Value raise {
  let bv = bind(q_var, var_)
  defer unbind(bv)
  let n = car(f)
  let mut gn = g
  let mut i : Value = Fix(1L)
  let mat = list1(coefvec(list2(Fix(0L), Fix(1L)), n, list1(Fix(1L))))
  while true {
    let ans = lindep(mat, coefvec(gn, n, list1(list3(var_, i, Fix(1L)))))
    if ans.truthy() {
      return ans
    }
    i = one_plus(i)
    gn = pgcd1(ptimes1(gn, g), f)
  }
  Nil
}

///|
fn divl(j : Value, a : Value) -> Value raise {
  mapcar(l => car(pmodquo(l, a)), j)
}

///|
fn pdifrows(a : Value, b : Value) -> Value raise {
  mapcar2((x, y) => pdifference(x, y), a, b)
}

///|
fn ptimesrow(var_ : Value, row : Value) -> Value raise {
  mapcar(a => ptimes(var_, a), row)
}

///|
fn ddiv(j : Value) -> Value raise {
  let mut b = j
  let mut a = car(b)
  while zerop(a) {
    b = cdr(b)
    a = car(b)
  }
  divl(j, a)
}

///|
fn lindep(mat : Value, vec : Value) -> Value raise {
  let mut m = mat
  let mut vec = vec
  if equal(Fix(0L), car(vec)) {
    vec = cdr(vec)
  } else {
    vec = pdifrows(cdr(vec), ptimesrow(car(vec), cdar(mat)))
  }
  while true {
    // loop
    if cdr(m) is Nil {
      if zerolp(cdr(reverse(vec))).truthy() {
        return car(last(vec))
      } else {
        rplacd(m, cons(ddiv(vec), cdr(m))) |> ignore
        return Nil
      }
    }
    let row = cadr(m)
    let mut rowd = row
    let mut vecd = vec
    // loop1
    let mut restart = false
    while true {
      let d = car(rowd)
      let e = car(vecd)
      if equal(Fix(0L), e) {
        if equal(Fix(0L), d) {
          vecd = cdr(vecd)
          rowd = cdr(rowd)
          continue
        } else {
          vec = cdr(vec)
          m = cdr(m)
          restart = true
          break
        }
      } else if equal(Fix(0L), d) {
        rplacd(m, cons(divl(vec, e), mapcar(x => cdr(x), cdr(m)))) |> ignore
        return Nil
      }
      vec = pdifrows(cdr(vec), ptimesrow(e, cdr(row)))
      m = cdr(m)
      break
    }
    ignore(restart)
  }
  Nil
}

///|
fn gfsplit(f : Value) -> Value raise {
  let btra = bind(q_tra_star, Nil)
  defer unbind(btra)
  let mut fl = list1(f)
  let n = cadr(f)
  let mut ans : Value = Nil
  let mut i : Value = Fix(0L)
  let mut nfl : Value = Nil
  while true {
    if fl is Nil {
      if nfl is Nil {
        if num_eq(n, int(length(ans))) {
          set(q_trl_star, Nil) |> ignore
          return ans
        } else {
          merr("GFSPLIT: unknown error.", []) |> ignore
        }
      } else {
        fl = nfl
        nfl = Nil
        i = one_plus(i)
      }
    }
    let f = car(fl)
    fl = cdr(fl)
    if num_gt(i, symval(q_mm_star)) {
      merr("GFSPLIT: unknown error.", []) |> ignore
    }
    let tr = tracemod0(f, i)
    if pcoefp(tr).truthy() ||
      (symval(q_algfac_star).truthy() && alg(tr).truthy()) {
      nfl = cons(f, nfl)
      continue
    }
    let f = cpbg0(tr, f)
    ans = nconc(ans, car(f))
    if cdr(f) is Nil {
      continue
    }
    nfl = nconc(nfl, cdr(f))
  }
  Nil
}

///|
fn cpbg0(tr : Value, f : Value) -> Value raise {
  let balc = bind(q_alc, Nil)
  defer unbind(balc)
  let mut tr = tr
  let mut f = f
  let mut m : Value = Fix(0L)
  let mut f1 : Value = Nil
  let mut f2 : Value = Nil
  if !numberp(caddr(tr)) && alg(caddr(tr)).truthy() {
    set(q_alc, painvmod(caddr(tr))) |> ignore
    tr = ptimes(symval(q_alc), tr)
  } else {
    set(q_alc, Fix(1L)) |> ignore
  }
  while true {
    // bk
    if pcoefp(f).truthy() {
      return if f1 is Nil && f2 is Nil {
        // NOTE TO TRANSLATORS: MEANING OF NEXT MESSAGE IS OBSCURE
        merr("CPBG0: wrong trace.", [])
      } else {
        cons(f1, f2)
      }
    } else if equal(cadr(f), Fix(1L)) {
      return cons(cons(f, f1), f2)
    } else if equal(m, symval(q_modulus)) {
      return cons(f1, cons(f, f2))
    }
    let trm = pdifference(tr, ptimes(m, symval(q_alc)))
    let g = pgcdu(trm, f)
    if numberp(g) || (symval(q_ear_alpha).truthy() && alg(g).truthy()) {
      m = one_plus(m)
      continue
    }
    f = car(pmodquo(f, g))
    if equal(cadr(g), Fix(1L)) {
      f1 = cons(g, f1)
    } else {
      f2 = cons(g, f2)
    }
  }
  Nil
}

///|
fn cpol2p(p : Value, var_ : Value) -> Value raise {
  let mut i = 0
  let mut ans : Value = Nil
  let mut p = nreverse(p)
  while !(p is Nil) {
    if !equal(Fix(0L), car(p)) {
      ans = cons(int(i), cons(car(p), ans))
    }
    p = cdr(p)
    i += 1
  }
  cons(var_, ans)
}

///|
fn tracemod(v : Value) -> Value raise {
  let mut ans : Value = Fix(0L)
  let mut tr = nreverse(symval(q_trl_star))
  set(q_trl_star, Nil) |> ignore
  let qlarge = atom(caar(tr)) && !numberp(caar(tr))
  while !(tr is Nil) {
    let term = if qlarge { car(tr) } else { cpol2p(car(tr), v) }
    tr = cdr(tr)
    ans = pplus(ans, term)
    set(q_trl_star, cons(term, symval(q_trl_star))) |> ignore
  }
  ans
}

///|
fn otracemod(term : Value, q : Value, m : Value, prime : Value) -> Value raise {
  let mut term = term
  let mut ans = term
  let mut i : Value = Fix(1L)
  set(q_trl_star, list1(term)) |> ignore
  while !equal(i, m) {
    term = pexptmod(term, prime, q)
    ans = pplus(ans, term)
    set(q_trl_star, cons(term, symval(q_trl_star))) |> ignore
    i = one_plus(i)
  }
  ans
}

///|
fn tracemod0(q : Value, i : Value) -> Value raise {
  let mut dl : Value = Nil
  if num_eq(i, Fix(0L)) {
    return if symval(q_trl_star).truthy() {
      tracemod(car(q))
    } else {
      otracemod(symval(q_var), q, symval(q_mm_star), symval(q_modulus))
    }
  } else if symval(q_trl_star).truthy() {
    dl = symval(q_trl_star)
    set(
      q_trl_star,
      mapcar(x => cons(car(x), pgcd1(cdr(x), cdr(q))), symval(q_trl_star)),
    )
    |> ignore
  }
  if !symval(q_tra_star).truthy() {
    let mut l = cdr(symval(q_trl_star))
    let mut a = symval(q_ear_alpha)
    set(q_tra_star, list1(symval(q_ear_alpha))) |> ignore
    while !(l is Nil) {
      l = cdr(l)
      a = pexpt(a, symval(q_modulus))
      set(q_tra_star, cons(a, symval(q_tra_star))) |> ignore
    }
  }
  // tag
  let ans = tracemod1(i, symval(q_tra_star), symval(q_trl_star))
  if dl.truthy() {
    set(q_trl_star, dl) |> ignore
  }
  ans
}

///|
fn tracemod1(n : Value, a : Value, l : Value) -> Value raise {
  let mut ans : Value = Fix(0L)
  let mut l = l
  let mut a = a
  while !(l is Nil) {
    ans = pplus(ans, ptimes(pexpt(car(a), n), car(l)))
    l = cdr(l)
    a = cdr(a)
  }
  ans
}

// The way arrays are manipulated has been changed to make this code
// reentrant: the symbols ANOTYPE, INVC and FCTC are bound to the arrays.
// They are set up in RAT;FACTOR.

///|
fn a(row : Value, col : Value) -> Value raise {
  aref(symval(q_anotype), [to_int(row), to_int(col)])
}

///|
fn invc(ind : Value) -> Value raise {
  aref1(symval(q_invc), to_int(ind))
}

///|
fn fctc(ind : Value) -> Value raise {
  aref1(symval(q_fctc), to_int(ind))
}

///|
fn algfac__set_a(row : Value, col : Value, v : Value) -> Unit raise {
  aset(symval(q_anotype), [to_int(row), to_int(col)], v) |> ignore
}

///|
fn cptomexp(p : Value, m : Value, u : Value, n : Value) -> Value raise {
  let mut b1 = x_star_starq1(list3(car(u), Fix(1L), Fix(1L)), u, m, p)
  if equal(cdr(b1), list2(Fix(1L), Fix(1L))) {
    set(q_split_star, t) |> ignore
    return Nil
  }
  let b2 = b1
  let mut j : Value = Fix(1L)
  let n_1 = one_minus(n)
  let mut first_ = true
  while true {
    if !first_ {
      // tag
      j = one_plus(j)
      if num_eq(j, n) {
        return Nil
      }
      b1 = pmodrem(ptimes(b1, b2), u)
    }
    first_ = false
    // tag1
    let mut l = p2cpol(b1, n_1)
    let mut i = n_1
    while !(l is Nil) {
      algfac__set_a(j, i, car(l))
      l = cdr(l)
      i = one_minus(i)
    }
    algfac__set_a(j, j, pdifference(a(j, j), Fix(1L)))
  }
  Nil
}

///|
/// `(last s 2)`
fn algfac__last2(s : Value) -> Value {
  let n = length(s)
  if n <= 2 {
    s
  } else {
    nthcdr(n - 2, s)
  }
}

///|
fn cptom(p : Value, m : Value, u : Value, n : Value) -> Value raise {
  let bs = bind_all([(q_n_starxn, Nil), (q_ind, Nil)])
  defer unbind_all(bs)
  let q = expt(p, m)
  let mut s : Value = Nil
  let mut j : Value = Fix(0L)
  let n_1 = one_minus(n)
  if num_gt(q, symval(q_thr_star)) {
    return cptomexp(p, m, u, n)
  }
  while true {
    // loop
    j = one_plus(j)
    if num_eq(j, n) {
      return Nil
    } else if symval(q_ind).truthy() {
      // sa
      cptimesxa(s, q) |> ignore
    } else {
      set(q_n_starxn, mapcar(x => pminus(x), p2cpol(cddr(u), n_1))) |> ignore
      s = x_star_starq(
        p2cpol(list3(symval(q_var), Fix(1L), Fix(1L)), n_1),
        p,
        m,
      )
      set(q_ind, t) |> ignore
    }
    // st
    if num_eq(j, Fix(1L)) &&
      equal(list2(Fix(1L), Fix(0L)), algfac__last2(s)) &&
      length(remove_equal(Fix(0L), copy_tree(s))) == 1 {
      return set(q_split_star, t)
    }
    let mut l = s
    let mut i = n_1
    while !(l is Nil) {
      algfac__set_a(j, i, car(l))
      l = cdr(l)
      i = one_minus(i)
    }
    algfac__set_a(j, j, pdifference(a(j, j), Fix(1L)))
  }
  Nil
}

///|
fn cptimesxa(p : Value, i : Value) -> Value raise {
  let mut i = i
  while !num_eq(i, Fix(0L)) {
    let mut xn = symval(q_n_starxn)
    let mut q = p
    let lc = car(p)
    while true {
      if !(cdr(q) is Nil) {
        rplaca(q, pplus(cadr(q), ptimes(lc, car(xn)))) |> ignore
        q = cdr(q)
        xn = cdr(xn)
      } else {
        rplaca(q, ptimes(lc, car(xn))) |> ignore
        i = one_minus(i)
        break
      }
    }
  }
  p
}

///|
fn x_star_starq(x : Value, p : Value, m : Value) -> Value raise {
  let mut i : Value = Fix(1L)
  set(q_trl_star, list1(x)) |> ignore
  let mut pp : Value = Fix(1L)
  while !num_eq(i, m) {
    let d = pp
    pp = num_mul(pp, p)
    cptimesxa(x, num_sub(pp, d)) |> ignore
    set(q_trl_star, cons(copy_tree(x), symval(q_trl_star))) |> ignore
    i = one_plus(i)
  }
  cptimesxa(x, num_sub(num_mul(pp, p), pp))
}

///|
fn cmnull(n : Value) -> Value raise {
  let sub1n = to_int(n) - 1
  let mone = cmod(Fix(-1L))
  let fa = symval(q_fctc)
  let ia = symval(q_invc)
  for i in 0..=sub1n {
    aset1(fa, i, Fix(-1L)) |> ignore
    aset1(ia, i, Fix(-1L)) |> ignore
  }
  let mut k = 1
  let mut nullsp = list1(Fix(1L))
  let ga = (r : Int, c : Int) => aref(symval(q_anotype), [r, c])
  let sa = (r : Int, c : Int, v : Value) => aset(symval(q_anotype), [r, c], v)
  while k <= sub1n {
    let mut j = 0
    // n3a
    while j <= sub1n &&
      (equal(ga(k, j), Fix(0L)) || num_gt(aref1(fa, j), Fix(-1L))) {
      j += 1
    }
    if j > sub1n {
      // null
      let mut nullv : Value = Nil
      for s in 0..=sub1n {
        if s == k {
          nullv = cons(int(s), cons(Fix(1L), nullv))
        } else if num_gt(aref1(ia, s), Fix(-1L)) {
          let vj = ga(k, to_int(aref1(ia, s)))
          if !equal(vj, Fix(0L)) {
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
      let m = ptimes(mone, painvmod(ga(k, j)))
      for s in k..=sub1n {
        sa(s, j, ptimes(m, ga(s, j))) |> ignore
      }
      for s in 0..=sub1n {
        if s != j {
          let aks = ga(k, s)
          for i in k..=sub1n {
            sa(i, s, pplus(ga(i, s), ptimes(ga(i, j), aks))) |> ignore
          }
        }
      }
    }
    // nextk
    k += 1
  }
  nullsp
}
