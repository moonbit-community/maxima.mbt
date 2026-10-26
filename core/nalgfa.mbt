// Port of src/nalgfa.lisp: factoring over algebraic number fields (Trager's
// algorithm), splitting fields, norms, traces and primitive elements.
//
// Specials of this file: vlist *nosplitf *algvar *denom *num *ans.

///|
fn nalgfa__make_poly(v : Value) -> Value {
  list3(v, Fix(1L), Fix(1L))
}

///|
fn new_alg() -> Value raise {
  newsym(d_gensym(x=Str("alg")))
}

///|
fn psqfrp(p : Value, var_ : Value) -> Value raise {
  lbool(zerop(pdegree(pgcd(p, pderivative(p, var_)), var_)))
}

///|
/// Generalized psubst: substitutes any expression for any var in p.
fn pgsubst(val : Value, var_ : Value, p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    p
  } else if eq(var_, car(p)) {
    if pzerop(val).truthy() {
      ptterm(cdr(p), Fix(0L))
    } else {
      let mut ld = cadr(p)
      let mut a = cdddr(p)
      let mut ans = caddr(p)
      while !(a is Nil) {
        let nans = pplus(ptimes(ans, pexpt(val, num_sub(ld, car(a)))), cadr(a))
        ld = car(a)
        a = cddr(a)
        ans = nans
      }
      ptimes(ans, pexpt(val, ld))
    }
  } else if pointergp(var_, car(p)).truthy() {
    p
  } else {
    let mut a = cdddr(p)
    let mut ans = ptimes(
      list3(car(p), cadr(p), Fix(1L)),
      pgsubst(val, var_, caddr(p)),
    )
    while !(a is Nil) {
      ans = pplus(
        ans,
        ptimes(list3(car(p), car(a), Fix(1L)), pgsubst(val, var_, cadr(a))),
      )
      a = cddr(a)
    }
    ans
  }
}

///|
fn pvsubst(nvar : Value, ovar : Value, p : Value) -> Value raise {
  if pcoefp(p).truthy() || pointergp(ovar, car(p)).truthy() {
    p
  } else if eq(ovar, car(p)) {
    cons(nvar, cdr(p))
  } else {
    pgsubst(nalgfa__make_poly(nvar), ovar, p)
  }
}

///|
fn ordervar(var_ : Value, l : Value) -> Value raise {
  let mvar = lmainvar(l)
  if mvar is Nil {
    l
  } else if !pointergp(mvar, var_).truthy() {
    cons(var_, l)
  } else {
    let newvar = gensym()
    set(q_genvar, append(symval(q_genvar), list1(newvar))) |> ignore
    set_symbol_plist(newvar, symbol_plist(var_)) |> ignore
    set(newvar, one_plus(symbol_value(mvar))) |> ignore
    cons(newvar, mapcar(p => pvsubst(newvar, var_, p), l))
  }
}

///|
/// Main var of list of poly's.
fn lmainvar(l : Value) -> Value raise {
  let mut v : Value = Nil
  for p in l.iter() {
    if pcoefp(p).truthy() {
      ()
    } else if v is Nil {
      v = car(p)
    } else if pointergp(car(p), v).truthy() {
      v = car(p)
    }
  }
  v
}

///|
/// An algebraic variable that occurs in the polynomial P, or NIL.
fn palgvar(p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    Nil
  } else if alg(p).truthy() {
    p__var(p)
  } else {
    let mut l = p__terms(p)
    while !(l is Nil) {
      let r = palgvar(cadr(l))
      if r.truthy() {
        return r
      }
      l = cddr(l)
    }
    Nil
  }
}

///|
/// X/Y if the quotient is a polynomial over the algebraic numbers, else
/// NIL.  PQUOTIENT can miss such a quotient when an algebraic variable of Y
/// is not its main variable, because then dividing term by term does not
/// see a relation like sqrt(c)^2 = c.  So make that variable the main one,
/// multiply X by the inverse of Y that RAINV computes, and divide by what
/// remains, which is free of that variable.
fn palgquotient(x : Value, y : Value) -> Value raise {
  let r = pquotientchk_safe(x, y)
  if r.truthy() {
    return r
  }
  let v = palgvar(y)
  if v is Nil {
    return Nil
  }
  let b = bind(q_genvar, symval(q_genvar))
  defer unbind(b)
  let l = ordervar(v, list2(x, y))
  let q = factor__ignore_rat_err(() => rattimes(
    cons(cadr(l), Fix(1L)),
    rainv(caddr(l)),
    t,
  ))
  if q.truthy() {
    palgquotient(
      pgsubst(nalgfa__make_poly(v), car(l), car(q)),
      pgsubst(nalgfa__make_poly(v), car(l), cdr(q)),
    )
  } else {
    Nil
  }
}

///|
fn presult(p1 : Value, p2 : Value, var_ : Value) -> Value raise {
  let b = bind(q_genvar, symval(q_genvar))
  defer unbind(b)
  let v = ordervar(var_, list2(p1, p2))
  let p1 = cadr(v)
  let p2 = caddr(v)
  let var_ = car(v)
  if zerop(pdegree(p1, var_)) {
    if zerop(pdegree(p2, var_)) {
      Fix(1L)
    } else {
      pexpt(p1, cadr(p2))
    }
  } else if zerop(pdegree(p2, var_)) {
    pexpt(p2, cadr(p1))
  } else {
    resultant(p1, p2)
  }
}

///|
fn pcoefvec(p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    list1(p)
  } else {
    let mut l : Value = Nil
    let mut i = cadr(p)
    let mut p = cdr(p)
    while !(numberp(i) && num_lt(i, Fix(0L))) {
      if !(p is Nil) && num_eq(car(p), i) {
        l = cons(cadr(p), l)
        p = cddr(p)
      } else {
        l = cons(Fix(0L), l)
      }
      i = one_minus(i)
    }
    nreverse(l)
  }
}

///|
fn algtrace1(bvec : Value, tvec : Value) -> Value raise {
  let mut bvec = bvec
  let mut i = int(length(tvec) - length(bvec))
  while !zerop(i) {
    bvec = cons(Fix(0L), bvec)
    i = one_minus(i)
  }
  algtrace_star(bvec, tvec)
}

///|
fn algtrace_star(bvec : Value, tvec : Value) -> Value raise {
  let mut b = bvec
  let mut tr = car(last(bvec))
  while !(cdr(b) is Nil) {
    if !pzerop(car(b)).truthy() {
      let mut l = cdr(b)
      let mut tv = tvec
      while !(l is Nil) {
        rplaca(l, pdifference(car(l), ptimes(car(b), car(tv)))) |> ignore
        l = cdr(l)
        tv = cdr(tv)
      }
    }
    let ntr = pplus(tr, car(last(b)))
    b = cdr(b)
    tr = ntr
  }
  tr
}

///|
/// CL `constantp` on a CRE coefficient.
fn nalgfa__constantp(x : Value) -> Bool {
  match x {
    Cons(_) => false
    Sym(_) => x is Nil || eq(x, t) || keywordp(x)
    _ => true
  }
}

///|
fn algtrace(f : Value, p : Value) -> Value raise {
  let r = cadr(pdivide(car(f), p))
  if nalgfa__constantp(car(r)) || !eq(caar(r), car(p)) {
    // r constant, or r constant in main var of p: r*deg(p)
    ratreduce(pctimes(cadr(p), car(r)), cdr(r))
  } else {
    ratreduce(algtrace1(pcoefvec(car(r)), cdr(pcoefvec(p))), cdr(r))
  }
}

///|
fn d_algtrace(f : Value, p : Value, var_ : Value) -> Value raise {
  let bs = bind_all([(q_varlist, list1(var_)), (q_genvar, Nil)])
  defer unbind_all(bs)
  let ff = rform(f)
  rdis_star(algtrace(ff, car(rform(p))))
}

///|
/// bad -> good
fn good_form(l : Value) -> Value raise {
  let mut l = l
  let mut ans : Value = Nil
  while !(l is Nil) {
    ans = cons(cons(cadr(l), car(l)), ans)
    l = cddr(l)
  }
  nreverse(ans)
}

///|
/// good -> bad
fn bad_form(l : Value) -> Value raise {
  mapcar(q => list2(cdr(q), car(q)), l)
}

///|
fn d_algfac(a1 : Value, a2? : Value, a3? : Value) -> Value raise {
  if a3 is Some(a3v) {
    return d_pfactoralg(a1, a2.unwrap_or(Nil), a3v)
  }
  let b = bind(q_varlist, Nil)
  defer unbind(b)
  match a2 {
    Some(a2v) => {
      newvar(a2v) |> ignore
      if alike1(a2v, car(symval(q_varlist))).truthy() {
        d_pfactoralg(a1, Nil, a2v)
      } else {
        d_pfactoralg(a1, a2v, car(last(symval(q_varlist))))
      }
    }
    None => {
      newvar(a1) |> ignore
      set(
        q_varlist,
        mapcan(
          q => if algpget(q).truthy() { list1(q) } else { Nil },
          symval(q_varlist),
        ),
      )
      |> ignore
      let n = length(symval(q_varlist))
      if n == 1 {
        d_pfactoralg(a1, Nil, car(symval(q_varlist)))
      } else if n > 1 {
        // MEANING OF NEXT MESSAGE IS UNCLEAR
        merr("algfac: too many algebraics.", [])
      } else {
        // MEANING OF NEXT MESSAGE IS UNCLEAR
        merr("algfac: no algebraics.", [])
      }
    }
  }
}

///|
fn d_pfactoralg(f : Value, p : Value, alg : Value) -> Value raise {
  let bs = bind_all([
    (q_varlist, list1(alg)),
    (q_genvar, Nil),
    (q_vlist, Nil),
    (q_tellratlist, Nil),
    (q_d_ratfac, Nil),
    (q_d_gcd, q_d_algebraic),
    (q_d_algebraic, Nil),
    (q_d_ratalgdenom, t),
    (q_n_stardenom, Fix(1L)),
    (q_n_starnum, Fix(1L)),
    (q_n_starans, Nil),
  ])
  defer unbind_all(bs)
  let mut p = p
  if p is Nil && radfunp(alg, t).truthy() {
    newvar(cadr(alg)) |> ignore
  } else {
    newvar(p) |> ignore
  }
  newvar1(f) |> ignore
  if symval(q_vlist) is Nil {
    merr("pfactoralg: attempt to factor a constant.", []) |> ignore
  }
  set(q_varlist, nconc(symval(q_varlist), sortgreat(symval(q_vlist)))) |> ignore
  if p.truthy() {
    p = cadr(ratrep_star(p))
    set(
      q_tellratlist,
      cons(cons(alg, mapcar(x => pdis(x), cdr(p))), symval(q_tellratlist)),
    )
    |> ignore
  } else {
    p = algpget(alg)
    p = pdifference(pexpt(cadr(ratrep_star(alg)), car(p)), cadr(p))
  }
  set(q_d_algebraic, t) |> ignore
  let f = cadr(ratrep_star(f))
  let f = pfactoralg1(f, p, Fix(0L))
  cons(
    list1(q_mtimes),
    cons(
      rdis(ratreduce(symval(q_n_starnum), symval(q_n_stardenom))),
      mapcar(x => pdis(x), f),
    ),
  )
}

///|
fn nalgfac(p : Value, mp : Value) -> Value raise {
  let bs = bind_all([
    (q_n_starnum, Fix(1L)),
    (q_n_stardenom, Fix(1L)),
    (q_n_starans, Nil),
    (q_algfac_star, Nil),
    (q_d_nalgfac, Nil),
    (q_d_algebraic, t),
    (q_d_gcd, q_d_algebraic),
  ])
  defer unbind_all(bs)
  let p = pfactoralg1(p, mp, Fix(0L))
  set(q_adn_star, num_mul(symval(q_adn_star), symval(q_n_stardenom))) |> ignore
  if equal(symval(q_n_starnum), Fix(1L)) {
    p
  } else {
    cons(symval(q_n_starnum), p)
  }
}

///|
fn nalgfa__push_ans(x : Value) -> Unit {
  set(q_n_starans, cons(x, symval(q_n_starans))) |> ignore
}

///|
fn nalgfa__pfactor_nonalg(f : () -> Value raise) -> Value raise {
  with_specials(
    [(q_d_algebraic, Nil), (q_d_gcd, car(symval(q_ear_gcdl)))],
    f,
  )
}

///|
fn pfactoralg1(f : Value, p : Value, ind : Value) -> Value raise {
  if pcoefp(f).truthy() {
    set(q_n_starnum, ptimeschk(f, symval(q_n_starnum))) |> ignore
    symval(q_n_starans)
  } else if num_eq(cadr(f), Fix(1L)) {
    let f = pshift(f, car(p), ind)
    nalgfa__push_ans(algnormal(f))
    let f = rquotient(f, car(symval(q_n_starans)))
    set(q_n_stardenom, ptimeschk(cdr(f), symval(q_n_stardenom))) |> ignore
    set(q_n_starnum, ptimeschk(car(f), symval(q_n_starnum))) |> ignore
    symval(q_n_starans)
  } else if equal(cdr(f), cdr(p)) {
    nalgfa__push_ans(
      pdifference(nalgfa__make_poly(car(f)), nalgfa__make_poly(car(p))),
    )
    let f = rquotient(f, car(symval(q_n_starans)))
    set(q_n_stardenom, ptimeschk(cdr(f), symval(q_n_stardenom))) |> ignore
    pfactoralg1(car(f), p, ind)
  } else if zerop(pdegree(f, car(p))) {
    let fl = nalgfa__pfactor_nonalg(() => pfactor1(f))
    for q in fl.iter() {
      if !pcoefp(q).truthy() {
        pfactoralg1(pshift(q, car(p), Fix(-1L)), p, one_plus(ind)) |> ignore
      }
    }
    symval(q_n_starans)
  } else {
    let mut f = f
    let mut l = nalgfa__pfactor_nonalg(() => pfactor(algnorm(f, p)))
    let mut polys : Value = Nil
    let alg = car(p)
    while !(l is Nil) {
      if !pcoefp(car(l)).truthy() {
        let mut temp = if cddr(l) is Nil { f } else { pgcd(f, car(l)) }
        if pcoefp(temp).truthy() {
          ()
        } else if num_eq(cadr(temp), Fix(1L)) {
          temp = algnormal(temp)
          nalgfa__push_ans(pshift(temp, alg, ind))
        } else if num_eq(cadr(l), Fix(1L)) {
          temp = algnormal(temp)
          nalgfa__push_ans(pshift(temp, alg, ind))
          if !symval(q_n_starnosplitf).truthy() {
            set(q_n_starnosplitf, list3(car(l), temp, ind)) |> ignore
          }
        } else {
          polys = cons(temp, polys)
        }
        f = rquotient(f, temp)
        set(q_n_stardenom, ptimeschk(cdr(f), symval(q_n_stardenom))) |> ignore
        f = car(f)
      }
      l = cddr(l)
    }
    set(q_n_starnum, ptimeschk(f, symval(q_n_starnum))) |> ignore
    for q in polys.iter() {
      pfactoralg1(pshift(q, alg, Fix(-1L)), p, one_plus(ind)) |> ignore
    }
    symval(q_n_starans)
  }
}

///|
fn pshift(f : Value, alg : Value, c : Value) -> Value raise {
  if num_eq(c, Fix(0L)) {
    f
  } else {
    pgsubst(
      pplus(nalgfa__make_poly(car(f)), pctimes(c, nalgfa__make_poly(alg))),
      car(f),
      f,
    )
  }
}

///|
fn d_splitfield(p : Value, var_ : Value) -> Value raise {
  let bs = bind_all([
    (q_varlist, Nil),
    (q_genvar, Nil),
    (q_genpairs, Nil),
    (q_n_staralgvar, Nil),
    (q_d_gcd, q_d_algebraic),
  ])
  defer unbind_all(bs)
  newsym(var_) |> ignore
  set(q_n_staralgvar, caar(new_alg())) |> ignore
  let p = psplit_field(cadr(ratf(p)))
  cons(list1(q_mlist), cons(pdis_star(car(p)), mapcar(x => rdis_star(x), cdr(p))))
}

///|
let nalgfa__splits_in_q : Value = sym("$splits in q")

///|
fn psplit_field(p : Value) -> Value raise {
  let l = mapcar(q => psplit_field1(cdr(q)), good_form(pfactor(p))) // don't normalize lcfs?
  let b = bind(q_d_algebraic, t)
  defer unbind(b)
  if cdr(l) is Nil {
    return car(l)
  }
  let mut l = l
  let mut prim : Value = Nil
  let mut zeroes : Value = Nil
  while !(l is Nil) {
    if eq(caar(l), q_linear) {
      zeroes = cons(cdar(l), zeroes)
    } else if prim is Nil {
      prim = caar(l)
      zeroes = nconc(cdar(l), zeroes)
    } else {
      let temp = primelmt(
        cons(car(p), cdr(prim)),
        cons(car(p), cdaar(l)),
        symval(q_n_staralgvar),
      )
      let z1_ = mapcar(q => ratgsubst(cadddr(temp), caaar(l), q), cdar(l))
      let pr = prim
      let z2_ = mapcar(q => ratgsubst(caddr(temp), car(pr), q), zeroes)
      zeroes = nconc(z1_, z2_)
      prim = car(temp)
    }
    l = cdr(l)
  }
  cons(if prim.truthy() { prim } else { nalgfa__splits_in_q }, zeroes)
}

///|
fn plsolve(p : Value) -> Value raise {
  ratreduce(ptterm(cdr(p), Fix(0L)), pminus(ptterm(cdr(p), Fix(1L))))
}

///|
/// Returns minimal poly and list of roots; p must be square free.
fn psplit_field1(p : Value) -> Value raise {
  let mut minpoly = cons(symval(q_n_staralgvar), cdr(p))
  let mut zeroes : Value = Nil
  let bs = bind_all([(q_d_algebraic, t), (q_d_ratalgdenom, t)])
  defer unbind_all(bs)
  if equal(cadr(p), Fix(1L)) {
    return cons(q_linear, plsolve(p))
  }
  let mut polys = list1(p)
  let mut nminpoly : Value = Nil
  let bn = bind(q_n_starnosplitf, Nil)
  defer unbind(bn)
  let mut alpha = cons(nalgfa__make_poly(car(minpoly)), Fix(1L))
  while !(polys is Nil) {
    zeroes = cons(alpha, zeroes)
    putprop(car(minpoly), cdr(minpoly), q_tellrat) |> ignore
    rplaca(
      polys,
      car(
        rquotient(
          pctimes(cdr(alpha), car(polys)),
          pdifference(pctimes(cdr(alpha), pget(caar(polys))), car(alpha)),
        ),
      ),
    )
    |> ignore
    let mp = minpoly
    let factored = mapcan(
      q => with_specials(
        [(q_n_starans, Nil), (q_n_starnum, Fix(1L)), (q_n_stardenom, Fix(1L))],
        () => nreverse(pfactoralg1(q, mp, Fix(0L))),
      ),
      polys,
    )
    polys = mapcan(
      q => if equal(cadr(q), Fix(1L)) {
        // linear factor
        zeroes = cons(plsolve(q), zeroes)
        Nil // flush linear factor
      } else {
        list1(q)
      },
      factored,
    )
    if symval(q_n_starnosplitf).truthy() {
      nminpoly = car(symval(q_n_starnosplitf))
      set(q_n_starnosplitf, cdr(symval(q_n_starnosplitf))) |> ignore
      putprop(symval(q_n_staralgvar), cdr(nminpoly), q_tellrat) |> ignore
      let nsf = symval(q_n_starnosplitf)
      let beta = plsolve(
        pgcd(
          cons(caar(nsf), cdr(minpoly)),
          exchangevar(car(nsf), symval(q_n_staralgvar)),
        ),
      )
      alpha = ratplus(
        cons(nalgfa__make_poly(symval(q_n_staralgvar)), Fix(1L)),
        rattimes(cons(num_neg(cadr(nsf)), Fix(1L)), beta, t),
      )
      let mp = minpoly
      zeroes = mapcar(q => ratgsubst(beta, car(mp), q), zeroes)
      polys = mapcar(q => car(rgsubst(beta, car(mp), q)), polys)
      minpoly = cons(symval(q_n_staralgvar), cdr(nminpoly))
    }
    // step
    set(q_n_starnosplitf, Nil) |> ignore
  }
  cons(minpoly, zeroes)
}

///|
fn exchangevar(poly : Value, var_ : Value) -> Value raise {
  let newvar = gensym()
  let ovar = car(poly)
  set(newvar, one_plus(symbol_value(ovar))) |> ignore
  pvsubst(ovar, newvar, pvsubst(var_, ovar, pvsubst(newvar, var_, poly)))
}

///|
/// Generalized psubst: substitutes any expression for any var in p.
fn rgsubst(val : Value, var_ : Value, p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    cons(p, Fix(1L))
  } else if eq(var_, car(p)) {
    if pzerop(val).truthy() {
      cons(ptterm(cdr(p), Fix(0L)), Fix(1L))
    } else {
      let mut ld = cadr(p)
      let mut a = cdddr(p)
      let mut ans = cons(caddr(p), Fix(1L))
      while !(a is Nil) {
        let nans = ratplus(
          rattimes(ans, ratexpt(val, num_sub(ld, car(a))), t),
          cons(cadr(a), Fix(1L)),
        )
        ld = car(a)
        a = cddr(a)
        ans = nans
      }
      rattimes(ans, ratexpt(val, ld), t)
    }
  } else if pointergp(var_, car(p)).truthy() {
    cons(p, Fix(1L))
  } else {
    let newsym = gensym()
    set(newsym, one_plus(symbol_value(car(p)))) |> ignore
    rgsubst(val, newsym, pvsubst(newsym, var_, p))
  }
}

///|
fn ratgsubst(val : Value, var_ : Value, rat : Value) -> Value raise {
  let n = rgsubst(val, var_, car(rat))
  ratquotient(n, rgsubst(val, var_, cdr(rat)))
}

///|
fn algnorm(f : Value, p : Value) -> Value raise {
  presult(f, p, car(p))
}

///|
fn d_algnorm(r : Value, p : Value, var_ : Value) -> Value raise {
  let bs = bind_all([(q_varlist, list1(var_)), (q_genvar, Nil)])
  defer unbind_all(bs)
  let r = ratf(r)
  let p = cadr(ratf(p))
  let n = algnorm(cadr(r), p)
  rdis_star(cons(n, algnorm(cddr(r), p)))
}

///|
/// f must be sqfr, p is minpoly, fvar # pvar.
fn sqfrnorm(f : Value, p : Value, fvar : Value) -> Value raise {
  let pvar = car(p)
  let fl = cdr(ordervar(pvar, list2(f, p))) // new main var will be car of p
  let p = cadr(fl)
  let f0 = car(fl) // make mainvar of f = mainvar(p)
  let mut i = 0
  let dif = pdifference(nalgfa__make_poly(fvar), nalgfa__make_poly(car(p)))
  let mut f = f0
  while true {
    if eq(car(f), car(p)) {
      let res = primpart(algnorm(f, p))
      if res.truthy() && psqfrp(res, fvar).truthy() {
        let modified = with_special(q_d_algebraic, t, () => {
          putprop(pvar, cdr(p), q_tellrat) |> ignore
          pvsubst(pvar, car(p), f)
        })
        return list([res, modified, car(p), p, int(i)])
      }
    }
    i += 1
    f = pgsubst(dif, fvar, f)
  }
  Nil
}

///|
fn primelmt(a : Value, b : Value, gvar : Value) -> Value raise {
  let ba = bind(q_d_algebraic, Nil)
  defer unbind(ba)
  // a is a poly with coeff's in k(b); gvar is new variable
  let norm_ = sqfrnorm(cons(gvar, cdr(a)), b, gvar)
  let br = bind(q_d_ratalgdenom, t)
  defer unbind(br)
  rplaca(norm_, primpart(car(norm_))) |> ignore
  putprop(gvar, cdar(norm_), q_tellrat) |> ignore
  set(q_d_algebraic, t) |> ignore
  let beta = subresgcd(cadddr(norm_), pvsubst(caddr(norm_), car(b), cadr(norm_)))
  let beta = plsolve(beta)
  let alpha = ratplus(
    cons(nalgfa__make_poly(gvar), Fix(1L)),
    rattimes(cons(num_neg(cadddr(cdr(norm_))), Fix(1L)), beta, t),
  )
  list([
    car(norm_), // minimal poly
    pplus(
      nalgfa__make_poly(car(a)), // new prim elm in old guys
      list3(car(b), Fix(1L), car(last(norm_))),
    ),
    alpha,
    beta,
  ]) // in terms of gamma
}

///|
/// p_a(a) is an irreducible polynomial in K defining an extension K[a] of
/// degree n_a.  Then f_b(b) is a polynomial in K[a] of degree n_f, which
/// defines a new extension K[a,b].  The output is a polynomial of degree
/// n_a*n_b, and the expression of its variable in terms of a root a of p_a
/// and a root b of f_b.  One assumes that p_a only depends on one variable a
/// and f_b of two different variables b and a.  So this works only for
/// algebraic numbers, not algebraic curves.
fn d_primelmt(f_b : Value, p_a : Value, c : Value) -> Value raise {
  let vla = newvar(p_a) // ensure varlist = ($a $b)
  let vlf = newvar(f_b)
  let bs = bind_all([
    (q_varlist, cons(car(vla), remove(car(vla), vlf))),
    (q_genvar, Nil), // start with a clean space of vars
    (q_genpairs, Nil),
  ])
  defer unbind_all(bs)
  let p = cadr(ratf(p_a)) // p_a in rat form
  let f = cadr(ratf(f_b)) // f_b in rat form mainvar b
  let algvar = caar(newsym(c)) // new primitive element
  let prim = primelmt(f, p, algvar)
  list3(list1(q_mlist), pdis(car(prim)), pdis(cadr(prim)))
}

// discriminant of a basis

///|
fn d_bdiscr(args : Value) -> Value raise {
  let bs = bind_all([(q_varlist, Nil), (q_genvar, Nil)])
  defer unbind_all(bs)
  let l = mapcar(x => rform(x), butlast(args))
  let r = bdiscr(l, car(rform(car(last(args)))))
  xcons(
    r,
    list4(q_mrat, q_simp, symval(q_varlist), symval(q_genvar)),
  )
}

///|
fn bdiscr(l : Value, minp : Value) -> Value raise {
  det(
    mapcar(
      q1 => mapcar(
        q2 => algtrace(cons(ptimes(car(q1), car(q2)), Fix(1L)), minp),
        l,
      ),
      l,
    ),
  )
}

///|
fn init_nalgfa() -> Unit raise {
  set(q_n_starnosplitf, t) |> ignore
}
