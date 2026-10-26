// Port of share/algebra/grob1.lisp: computations of Groebner bases, by
// D. Lazard (jun. 1988).
//
// STAND(CRE_list, ordering) computes the Groebner base of a list of
// polynomials; ordering is ORDLEX (pure lexicographical) or ORDDEG
// (degree-reverse-lexicographical). Polynomials are kept in an internal
// form: a list of monomials (coeff e1 ... en). Statistics are kept in
// NBSYZ (computed syzygies), NBRED (reduction steps), NBREDUC (reductions of
// polynomials already in the base) and NBRED0 (reductions leading to 0).
// ELIMPOL(base, ordering, var) returns 1 if the system has no solution, the
// string "dimension positive" if its set of solutions is not finite, or a
// univariate eliminating polynomial in VAR.

///|
/// `(apply 'min l)` (CL MIN needs at least one argument).
fn grob1__min(l : Value) -> Value raise {
  if l is Nil {
    lisp_error("invalid number of arguments: 0") |> ignore
  }
  let mut m = car(l)
  for x in cdr(l).iter() {
    m = num_min(m, x)
  }
  m
}

///|
/// `(apply '+ l)`
fn grob1__sum(l : Value) -> Value raise {
  let mut s : Value = Fix(0L)
  for x in l.iter() {
    s = num_add(s, x)
  }
  s
}

///|
/// `(mapcar f a b)`: stops at the shorter list.
fn grob1__map2(f : (Value, Value) -> Value raise, a : Value, b : Value) -> Value raise {
  let c = Collector::new()
  let mut a = a
  let mut b = b
  while a.truthy() && b.truthy() {
    c.add(f(car(a), car(b)))
    a = cdr(a)
    b = cdr(b)
  }
  c.result()
}

///|
/// `(mapcar '- a b)`
fn grob1__minus(a : Value, b : Value) -> Value raise {
  grob1__map2((x, y) => num_sub(x, y), a, b)
}

///|
/// `(funcall ordexp a b)` on the special variable ORDEXP.
fn grob1__ordexp(a : Value, b : Value) -> Bool raise {
  funcall(symval(q_ordexp), [a, b]).truthy()
}

///|
/// Maclisp QUOTIENT on integers.
fn grob1__quotient(a : Value, b : Value) -> Value raise {
  num_truncate(a, b=b).0
}

///|
fn d_stand(d_liste : Value, ordre? : Value = q_ordlex) -> Value raise {
  let lis = lire(d_liste, ordre)
  let base = grob1__grobner(lis, ordre)
  cons(list1(q_mlist), mapcar(w => d_decode_poly(w, Nil), base))
}

// LE LECTEUR
// Il faut traduire une liste de polynomes CRE; on suppose ici les
// coefficients rationnels. Il faut avoir appele' RAT sur la liste de
// polynomes pour toutes les variables apparaissent dans les en-tetes de tous
// les polynomes

///|
/// Passer de CRE a polynome en la premiere variable (en-tete deja enlevee)
fn lire1(pol : Value, var_ : Value) -> Value raise {
  if numberp(pol) {
    list1(list2(pol, Fix(0L)))
  } else if equal(car(pol), var_) {
    let c = Collector::new()
    let mut p = cdr(pol)
    while p.truthy() {
      c.add(list2(cadr(p), car(p)))
      p = cddr(p)
    }
    c.result()
  } else {
    list1(list2(pol, Fix(0L)))
  }
}

///|
/// passer de CRE a polynome en n variables
fn lire2(pol : Value, lvar : Value) -> Value raise {
  if cdr(lvar) is Nil {
    lire1(pol, car(lvar))
  } else {
    mapcan(
      u => mapcar(v => append(v, cdr(u)), lire2(car(u), cdr(lvar))),
      lire1(pol, car(lvar)),
    )
  }
}

///|
/// appliquer lire2 a une liste macsyma de polynomes
fn lire(mliste : Value, ordexp0 : Value) -> Value raise {
  let b = bind(q_ordexp, ordexp0)
  defer unbind(b)
  let mut mliste = mliste
  if d_ratp(mliste) is Nil {
    mliste = d_rat(mliste, Nil)
  }
  set(q_d_header, car(second(mliste))) |> ignore
  if !eq(car(symval(q_d_header)), q_mrat) {
    lisp_error("bad rat form") |> ignore
  }
  mapcar(
    u => sort_list(lire2(cadr(u), reverse(cadddr(caadr(mliste)))), (v, w) => ordexp(
        cdr(v),
        cdr(w),
      ).truthy()),
    cdr(mliste),
  )
}

// LES ORDRES

///|
/// ordre lexico inverse pour les exposants
fn orddeg(m1 : Value, m2 : Value) -> Value raise {
  let d = num_sub(grob1__sum(m1), grob1__sum(m2))
  if plusp(d) {
    t
  } else if minusp(d) {
    Nil
  } else {
    let mut a = num_sub(car(m1), car(m2))
    let mut m1 = cdr(m1)
    let mut m2 = cdr(m2)
    while zerop(a) && m1.truthy() {
      a = num_sub(car(m1), car(m2))
      m1 = cdr(m1)
      m2 = cdr(m2)
    }
    lbool(minusp(a))
  }
}

///|
fn ordlex(m1 : Value, m2 : Value) -> Value raise {
  let mut a = num_sub(car(m1), car(m2))
  let mut m1 = cdr(m1)
  let mut m2 = cdr(m2)
  while zerop(a) && m1.truthy() {
    a = num_sub(car(m1), car(m2))
    m1 = cdr(m1)
    m2 = cdr(m2)
  }
  lbool(plusp(a))
}

///|
/// ancienne version
fn ordexp(m1 : Value, m2 : Value) -> Value raise {
  let d = num_sub(grob1__sum(m1), grob1__sum(m2))
  if plusp(d) {
    t
  } else if minusp(d) {
    Nil
  } else {
    let mut m1 = m1
    let mut m2 = m2
    while m1.truthy() && num_eq(car(m1), car(m2)) {
      m1 = cdr(m1)
      m2 = cdr(m2)
    }
    lbool(m1.truthy() && num_lt(car(m1), car(m2)))
  }
}

///|
/// ancienne version (the second DEFUN of ORDPAIRS in the file)
fn ordpairs(p1 : Value, p2 : Value) -> Value raise {
  let exp1 = caar(p1)
  let exp2 = caar(p2)
  lbool(
    grob1__ordexp(exp2, exp1) ||
    (
      equal(exp1, exp2) &&
      (
        grob1__ordexp(caadr(p2), caadr(p1)) ||
        (
          equal(caadr(p1), caadr(p2)) &&
          grob1__ordexp(cdadr(p2), cdadr(p1))
        )
      )
    ),
  )
}

// OPERATIONS ELEMENTAIRES PRESERVATIVES (POLYNOMES) COEFFICIENTS GENERAUX

///|
fn n_stargpolmon(pol : Value, mon : Value) -> Value raise {
  mapcar(u => n_stargterm(u, mon), pol)
}

///|
fn n_stargterm(m1 : Value, m2 : Value) -> Value raise {
  cons(
    mactimes(car(m1), car(m2)),
    grob1__map2((x, y) => num_add(x, y), cdr(m1), cdr(m2)),
  )
}

// OPERATIONS ELEMENTAIRES DESTRUCTIVES (POLYNOMES) COEFFICIENTS GENERAUX

///|
/// destructif resultat dans p
fn n_stargcofpol(c : Value, p : Value) -> Value raise {
  for u in p.iter() {
    rplaca(u, mactimes(c, car(u))) |> ignore
  }
  p
}

///|
/// Cette fonction retourne et lie a p1 la difference (cdr p1) - p2;
/// iteratif et destructif; le polynome nul est retourne (cons nil nil)
fn n_gpol(p1 : Value, p2 : Value) -> Value raise {
  let mut p = p1
  let mut q = p2
  while q.truthy() {
    let e1 = cdadr(p)
    let e2 = cdar(q)
    if grob1__ordexp(e1, e2) {
      p = cdr(p)
    } else if equal(e1, e2) {
      let a = macmoins(caadr(p), caar(q))
      if zerop(a) {
        rplacd(p, cddr(p)) |> ignore
      } else {
        p = cdr(p)
        rplaca(car(p), a) |> ignore
      }
      q = cdr(q)
    } else {
      p = cdr(rplacd(p, cons(cons(macmoins(Fix(0L), caar(q)), cdar(q)), cdr(p))))
      q = cdr(q)
    }
  }
  rplaca(p1, cadr(p1)) |> ignore
  rplacd(p1, cddr(p1))
}

///|
/// On definit maintenant la division d'un polynome par une base unitaire;
/// le polynome est remplace par le resultat (destructif, resultat dans
/// pol1; pol2 est unitaire)
fn red1(pol1 : Value, p : Value, pol2 : Value) -> Value raise {
  let a = grob1__minus(cdar(p), cdar(pol2))
  if minusp(grob1__min(a)) {
    pol1
  } else {
    n_gpol(p, n_stargpolmon(cdr(pol2), cons(caar(p), a)))
  }
}

///|
fn div_terme(p1 : Value, p : Value, base : Value) -> Value raise {
  let mut a = cdar(p)
  let mut b : Value = Nil
  while !eq(a, b) {
    for u in base.iter() {
      red1(p1, p, u) |> ignore
    }
    b = a
    a = cdar(p)
  }
  p
}

///|
fn divise(p1 : Value, base : Value) -> Value raise {
  let mut p = cdr(div_terme(p1, p1, base))
  while p.truthy() {
    p = cdr(div_terme(p1, p, base))
  }
  p1
}

///|
fn monic(pol : Value) -> Value raise {
  let c = caar(pol)
  for u in pol.iter() {
    rplaca(u, macdiv(car(u), c)) |> ignore
  }
  pol
}

// OPERATIONS ELEMENTAIRES PRESERVATIVES (POLYNOMES) COEFFICIENTS ENTIERS

///|
fn n_staripolmon(pol : Value, mon : Value) -> Value raise {
  mapcar(u => n_stariterm(u, mon), pol)
}

///|
fn n_stariterm(m1 : Value, m2 : Value) -> Value raise {
  cons(
    num_mul(car(m1), car(m2)),
    grob1__map2((x, y) => num_add(x, y), cdr(m1), cdr(m2)),
  )
}

///|
fn isyz(pair : Value) -> Value raise {
  let f = caddr(pair)
  let g = cdddr(pair)
  let exp = caar(pair)
  set(q_d_nbsyz, num_add(symval(q_d_nbsyz), Fix(1L))) |> ignore
  let mut a = caar(g)
  let mut b = caar(f)
  let d = num_gcd(a, b)
  a = grob1__quotient(a, d)
  b = grob1__quotient(b, d)
  n_ipol(
    n_staripolmon(f, cons(a, grob1__minus(exp, cdar(f)))),
    n_staripolmon(cdr(g), cons(b, grob1__minus(exp, cdar(g)))),
  )
}

// OPERATIONS ELEMENTAIRES DESTRUCTIVES (POLYNOMES) COEFFICIENTS ENTIERS

///|
/// destructif resultat dans p
fn n_staricofpol(c : Value, p : Value) -> Value raise {
  for u in p.iter() {
    rplaca(u, num_mul(c, car(u))) |> ignore
  }
  p
}

///|
/// Cette fonction retourne et lie a p1 la difference (cdr p1) - p2;
/// iteratif et destructif; le polynome nul est retourne (cons nil nil)
fn n_ipol(p1 : Value, p2 : Value) -> Value raise {
  n_ipol2(p1, p2) |> ignore
  rplaca(p1, cadr(p1)) |> ignore
  rplacd(p1, cddr(p1))
}

///|
fn n_ipol2(p1 : Value, p2 : Value) -> Value raise {
  let mut p = p1
  let mut q = p2
  while q.truthy() {
    let e1 = cdadr(p)
    let e2 = cdar(q)
    if grob1__ordexp(e1, e2) {
      p = cdr(p)
    } else if equal(e1, e2) {
      let a = num_sub(caadr(p), caar(q))
      if zerop(a) {
        rplacd(p, cddr(p)) |> ignore
      } else {
        p = cdr(p)
        rplaca(car(p), a) |> ignore
      }
      q = cdr(q)
    } else {
      p = cdr(rplacd(p, cons(cons(num_neg(caar(q)), cdar(q)), cdr(p))))
      q = cdr(q)
    }
  }
  Nil
}

///|
/// On definit maintenant la division d'un polynome par une base; le
/// polynome est remplace par le resultat. Pseudo division pour eviter les
/// divisions de coefficients. Destructif, resultat dans pol1; rend nil si
/// pol1 non modifie, (cons nil nil) si pol1 devient nul.
fn ired2(pol1 : Value, pol2 : Value) -> Value raise {
  let a = grob1__minus(cdar(pol1), cdar(pol2))
  if minusp(grob1__min(a)) {
    Nil
  } else {
    set(q_d_nbred, num_add(symval(q_d_nbred), Fix(1L))) |> ignore
    let mut b = caar(pol2)
    let mut c = caar(pol1)
    let d = num_gcd(b, c)
    b = grob1__quotient(b, d)
    c = grob1__quotient(c, d)
    n_staricofpol(b, cdr(pol1)) |> ignore
    n_ipol(pol1, n_staripolmon(cdr(pol2), cons(c, a)))
  }
}

///|
fn iredp(p1 : Value, p : Value, q : Value) -> Value raise {
  let pp = cdr(p)
  if pp is Nil {
    return Nil
  }
  let a = grob1__minus(cdar(pp), cdar(q))
  if !minusp(grob1__min(a)) {
    let mut b = caar(q)
    let mut c = caar(pp)
    let d = num_gcd(b, c)
    b = grob1__quotient(b, d)
    c = grob1__quotient(c, d)
    n_staricofpol(b, p1) |> ignore
    n_ipol2(pp, n_staripolmon(cdr(q), cons(c, a))) |> ignore
    rplacd(p, cdr(pp))
  } else {
    Nil
  }
}

///|
/// pour idivise2, il faut multiplier tout le polynome dividende
fn idivp(p1 : Value, p : Value, base : Value) -> Value raise {
  let mut a = cdadr(p)
  let mut b : Value = Nil
  while !eq(a, b) {
    for u in base.iter() {
      iredp(p1, p, u) |> ignore
    }
    b = a
    a = cdadr(p)
  }
  cdr(p)
}

///|
fn idivise2(p1 : Value, base : Value) -> Value raise {
  let mut p = p1
  while p.truthy() {
    p = idivp(p1, p, base)
  }
  grob1__primpart(p1)
}

// OPERATIONS SUR LES COEFFICIENTS

///|
fn mactimes(a : Value, b : Value) -> Value raise {
  meval(list3(list1(q_mtimes), a, b))
}

///|
fn macplus(a : Value, b : Value) -> Value raise {
  meval(list3(list1(q_mplus), a, b))
}

///|
fn macmoins(a : Value, b : Value) -> Value raise {
  meval(list3(list1(q_mplus), a, list2(list1(q_mminus), b)))
}

///|
fn macdiv(a : Value, b : Value) -> Value raise {
  meval(list3(list1(q_mquotient), a, b))
}

///|
/// PRIMPART of grob1.lisp: divide the (integer) coefficients of P by their
/// content. (The contract name PRIMPART is the ratmac.lisp macro, which the
/// compiled core keeps; loading grob1 redefines the function for grob1's
/// own callers.)
fn grob1__primpart(p : Value) -> Value raise {
  // calcul du contenu
  let mut q = cdr(p)
  let mut g = caar(p)
  while !(eql(num_abs(g), Fix(1L)) || q is Nil) {
    g = num_gcd(g, caar(q))
    q = cdr(q)
  }
  let d = g
  if !eql(num_abs(d), Fix(1L)) {
    // diviser par le contenu
    for u in p.iter() {
      rplaca(u, grob1__quotient(car(u), d)) |> ignore
    }
  }
  p
}

// LA BASE STANDARD
// Construction de la base. Methode a la Buchberger-Bouzeghoub.
// base: liste de polynomes
// paires: candidats sygyzies: ((exp."deja reduite").((exp1.exp2).(f.g)))
// algorithme: reduire tous les polynomes; calculer la liste des paires;
// vivier construit celles qui ne sont pas encore visitees; reduire la
// premiere paire, inserer le resultat dans la base et rereduire; remettre a
// jour la liste des paires et recommencer

///|
/// "critere 3": look for h in base dividing exp such that the syzygies
/// (f h) and (g h) have been computed.
fn grob1__critere3(exp : Value, exp1 : Value, exp2 : Value) -> Value raise {
  let base = symval(q_d_base)
  let mut l1 = cdr(base)
  let mut l3 = cddr(base)
  let mut exph = cdaadr(base)
  while true {
    if l1 is Nil {
      // pas trouve de h
      return l1
    } else if grob1__ordexp(exph, exp) {
      return Nil
    } else if !minusp(grob1__min(grob1__minus(exp, exph))) &&
      {
        let exph1 = grob1__map2((x, y) => num_max(x, y), exph, exp1)
        grob1__ordexp(exp, exph1) ||
        (equal(exp, exph1) && grob1__ordexp(exp2, exph))
      } &&
      {
        let exph2 = grob1__map2((x, y) => num_max(x, y), exph, exp2)
        grob1__ordexp(exp, exph2) ||
        (equal(exp, exph2) && grob1__ordexp(exp1, exph))
      } {
      return l1
    }
    l1 = l3
    exph = cdaar(l3)
    l3 = cdr(l3)
  }
  Nil
}

///|
fn grob1__stats(with_pairs : Value?) -> Unit raise {
  match with_pairs {
    None =>
      format(
        t,
        "~% nbsyz = ~a    nbred = ~a    nbreduc = ~a     nbred0 = ~a    lbase = ~d~%",
        [
          symval(q_d_nbsyz),
          symval(q_d_nbred),
          symval(q_d_nbreduc),
          symval(q_d_nbred0),
          int(length(cdr(symbol_value(q_base)))),
        ],
      )
      |> ignore
    Some(l) =>
      format(
        t,
        "~% nbsyz = ~a    nbred = ~a    nbreduc = ~a     nbred0 = ~a    lbase = ~a~% paires a voir = ~d~%",
        [
          symval(q_d_nbsyz),
          symval(q_d_nbred),
          symval(q_d_nbreduc),
          symval(q_d_nbred0),
          int(length(cdr(symbol_value(q_base)))),
          int(length(l)),
        ],
      )
      |> ignore
  }
}

///|
fn grob1__grobner(gener : Value, ordexp0 : Value) -> Value raise {
  let bd = bind(q_ordexp, ordexp0)
  defer unbind(bd)
  set(
    q_d_base,
    cons(
      Nil,
      sort_list(copy_tree(gener), (u, v) => ordexp(cdar(v), cdar(u)).truthy()),
    ),
  )
  |> ignore
  set(q_d_nbsyz, Fix(0L)) |> ignore
  set(q_d_nbred, Fix(0L)) |> ignore
  set(q_d_nbreduc, Fix(0L)) |> ignore
  set(q_d_nbred0, Fix(0L)) |> ignore
  let base = symval(q_d_base)
  reduire(base, cdr(base), cddr(base)) |> ignore
  let pc = Collector::new()
  let mut u = cdr(symval(q_d_base))
  while u.truthy() {
    let exp = cdaar(u)
    let f = car(u)
    for v in cdr(u).iter() {
      pc.add(apparier(f, v, exp, cdar(v)))
    }
    u = cdr(u)
  }
  let paires = cons(
    Nil,
    sort_list(pc.result(), (a, b) => funcall(symval(q_ordpairs), [a, b]).truthy()),
  )
  // parcourir les paires
  let mut l = vivier(paires)
  while l.truthy() {
    let mut p = car(l)
    let exp = caar(p)
    let exp1 = caadr(p)
    let exp2 = cdadr(p)
    if cdar(p).truthy() {
      // paire deja vue
      l = cdr(l)
    } else if grob1__critere3(exp, exp1, exp2).truthy() {
      l = cdr(l)
      rplacd(car(p), t) |> ignore // le critere 3 est verifie
    } else {
      rplacd(car(p), t) |> ignore // la paire va etre traitee
      p = isyz(p)
      let q = inserer(p, symval(q_d_base))
      if q.truthy() {
        reduire(symval(q_d_base), q, Nil) |> ignore
        grob1__stats(None)
        print(escalier(cdr(symval(q_d_base)))) |> ignore
        print(Str("\n")) |> ignore
        rafraichir(paires, p, symval(q_d_base)) |> ignore
        l = vivier(paires)
      } else {
        l = cdr(l)
        grob1__stats(Some(l))
      }
    }
  }
  set(q_d_base, cdr(symval(q_d_base))) |> ignore
  let base = symval(q_d_base)
  // reduire completement
  for u in base.iter() {
    idivise2(u, base) |> ignore
  }
  for u in base.iter() {
    monic(u) |> ignore
  }
  base
}

///|
fn apparier(p : Value, q : Value, expp : Value, expq : Value) -> Value raise {
  cons(
    cons(
      grob1__map2((x, y) => num_max(x, y), expp, expq), // caar
      // cdar: exposants etrangers
      lbool(zerop(grob1__sum(grob1__map2((x, y) => num_min(x, y), expp, expq)))),
    ),
    cons(
      cons(expp, expq), // caadr cdadr
      cons(p, q), // caddr cdddr
    ),
  )
}

///|
fn vivier(paires : Value) -> Value raise {
  let c = Collector::new()
  for x in cdr(paires).iter() {
    // paire deja vue?
    if cdar(x) is Nil {
      c.add(x)
    }
  }
  sort_list(c.result(), (a, b) => funcall(symval(q_ordpairs), [a, b]).truthy())
}

///|
fn rafraichir(paires : Value, q : Value, base : Value) -> Value raise {
  let nvp = cons(Nil, Nil)
  if car(q).truthy() {
    // paires p q pour p dans base
    let mut l = cdr(base)
    let mut p = cadr(base)
    let mut nvpa = nvp // liste des nouvelles paires
    let expq = cdar(q)
    let mut bit = true
    while l.truthy() {
      if eq(q, p) {
        bit = false
      } else if bit {
        nvpa = cdr(rplacd(nvpa, list1(apparier(p, q, cdar(p), expq))))
      } else {
        nvpa = cdr(rplacd(nvpa, list1(apparier(q, p, expq, cdar(p)))))
      }
      p = cadr(l)
      l = cdr(l)
    }
  }
  // rafraichir les anciennes
  let mut l = paires
  while cdr(l).truthy() {
    let mut pp = cadr(l)
    let f = caddr(pp)
    let g = cdddr(pp)
    let ef = cdar(f)
    let eg = cdar(g)
    if ef is Nil || eg is Nil {
      // enlever si un pol est nul
      rplacd(l, cddr(l)) |> ignore
    } else if !equal(ef, caadr(pp)) || !equal(eg, cdadr(pp)) {
      // un pol a change?
      pp = if grob1__ordexp(ef, eg) {
        apparier(g, f, eg, ef)
      } else {
        apparier(f, g, ef, eg)
      }
      rplacd(l, cons(pp, cddr(l))) |> ignore
      l = cdr(l)
    } else {
      l = cdr(l)
    }
  }
  nconc(paires, cdr(nvp))
}

///|
/// recherche des reductibles et reduction des elements de base;
/// a ---> dernier element reduit (vient d'etre insere),
/// b ---> provenance de cet element
fn reduire(base : Value, a : Value, b : Value) -> Value raise {
  let mut b = b
  let mut l0 = a
  let mut l1 = cdr(a)
  let mut q0 = car(a)
  let mut q = cadr(a)
  let mut bit = eq(a, cdr(b))
  while l1.truthy() {
    if bit {
      // reduction par tout ce qui precede: q reductible?
      let mut l = cdr(base)
      while true {
        if eq(l, l1) {
          // q irreductible
          l0 = l1
          break
        } else if ired2(q, car(l)).truthy() {
          // ired2 est un predicat
          rplacd(l0, cdr(l1)) |> ignore // enlever q
          set(q_d_nbreduc, num_add(symval(q_d_nbreduc), Fix(1L))) |> ignore
          l1 = inserer(q, base)
          if l1.truthy() {
            q0 = q
            b = l0
            l0 = l1
            bit = eq(l0, cdr(b))
          }
          break
        }
        l = cdr(l)
      }
    } else if ired2(q, q0).truthy() {
      // reduction par q0 seulement: q reductible
      rplacd(l0, cdr(l1)) |> ignore // enlever q
      set(q_d_nbreduc, num_add(symval(q_d_nbreduc), Fix(1L))) |> ignore
      l1 = inserer(q, base)
      if l1.truthy() {
        q0 = q
        b = l0
        l0 = l1
        bit = eq(l0, cdr(b))
      }
    } else {
      l0 = l1
    }
    l1 = cdr(l0)
    q = car(l1)
    bit = bit || eq(l1, cdr(b))
  }
  base
}

///|
/// retourne le lieu d'insertion
fn inserer(q : Value, base : Value) -> Value raise {
  let mut q = q
  let mut l2 = base // chercher ou` inserer q...
  let mut l3 = cdr(base)
  let mut qq = cadr(base)
  let mut expq = cdar(q)
  while true {
    if expq is Nil {
      set(q_d_nbred0, num_add(symval(q_d_nbred0), Fix(1L))) |> ignore
      // si q est nul retourner nil pour inserer, mais t pour cond
      l2 = q
      if l2.truthy() {
        return cdr(l2)
      }
    } else if l3 is Nil || grob1__ordexp(cdar(qq), expq) {
      rplacd(l2, Nil) |> ignore // pour accelerer la reduction
      q = grob1__primpart(q)
      q = idivise2(q, cdr(symval(q_d_base))) // reduire completement
      rplacd(l2, cons(q, l3)) |> ignore // inserer q
      return cdr(l2) // lieu a retourner
    }
    if ired2(q, qq).truthy() {
      // reduire q et repartir
      expq = cdar(q)
      l2 = base
    } else {
      l2 = l3
    }
    l3 = cdr(l2)
    qq = car(l3)
  }
  Nil
}

// RESOLUTION DE SYSTEMES
// On part d'une base standard pour un ordre compatible avec le degre. Elle
// est representee par une liste de polynomes, chacun d'eux etant une liste
// de monomes de la forme (coeff e1 ... en).

///|
/// L'escalier est la liste des vecteurs exposants des monomes dominants.
fn escalier(base : Value) -> Value raise {
  mapcar(x => cdar(x), base)
}

///|
/// La variete est vide (i.e. de dim. -1) si l'escalier est reduit au
/// vecteur nul (monome constant)
fn dim_1(esc : Value) -> Value raise {
  lbool(every(x => zerop(x), car(esc)))
}

///|
/// La dimension est 0 si il y a un element de l'escalier sur chaque axe. On
/// suppose la base reduite, ce qui implique qu'il n'y a pas 2 elements de
/// l'escalier sur le meme axe
fn dim0(esc : Value) -> Value raise {
  let d = dim_1(esc)
  if d.truthy() {
    return d
  }
  let mut i : Value = Fix(0L)
  for x in esc.iter() {
    let s = grob1__sum(mapcar(u => num_min(u, Fix(1L)), x))
    i = num_add(i, num_sub(Fix(2L), num_min(Fix(2L), s)))
  }
  lbool(num_eq(i, int(length(car(esc)))))
}

///|
/// Construction de la liste des monomes sous l'escalier. Le predicat sousp
/// indique si un monome est sous l'escalier
fn sous_esc(esc : Value) -> Value raise {
  let mut l : Value = Nil
  let m = mapcar(_ => Fix(0L), car(esc))
  let mut i = cons(Fix(0L), Nil)
  while i.truthy() {
    rplaca(i, num_add(car(i), Fix(1L))) |> ignore
    if sousp(m, esc).truthy() {
      l = cons(copy_tree(m), l)
      i = m
    } else {
      rplaca(i, Fix(0L)) |> ignore
      i = cdr(i)
    }
  }
  l
}

///|
/// Test mon2 ne divise pas mon1 pour 2 vecteurs d'exposants
fn notdivmon(mon1 : Value, mon2 : Value) -> Value raise {
  lbool(minusp(grob1__min(grob1__minus(mon1, mon2))))
}

///|
/// sousp est utilise par sous-esc pour tester si un monome est au sous
/// l'escalier
fn sousp(mon : Value, esc : Value) -> Value raise {
  lbool(every(u => notdivmon(mon, u).truthy(), esc))
}

///|
/// Construction de la matrice dont le polynome caracteristique a pour
/// racine les premieres coordonnees des solutions; les lignes et colonnes
/// sont indexees par basli, chaque ligne etant en representation creuse.
/// DIVISE retourne le reste de la division d'un polynome par la base
/// standard
fn umat(basli : Value, base : Value) -> Value raise {
  mapcar(
    u => divise(
      cons(
        cons(Fix(1L), rplaca(copy_tree(u), num_add(car(u), Fix(1L)))),
        Nil,
      ),
      base,
    ),
    basli,
  )
}

///|
/// densification d'une ligne
fn densif(ligne : Value, basli : Value) -> Value raise {
  let nl = cons(list1(q_mlist), Nil)
  let mut b = basli
  let mut l = ligne
  let mut c : Value = Fix(0L)
  let mut nl1 = nl
  while b.truthy() {
    if equal(car(b), cdar(l)) {
      c = caar(l)
      if c.truthy() {
        l = cdr(l)
      }
    }
    nl1 = cdr(rplacd(nl1, cons(c, Nil)))
    b = cdr(b)
    c = Fix(0L)
  }
  nl
}

///|
/// matrice macsyma; umatr est le resultat de umat
fn matmac(basli : Value, base : Value) -> Value raise {
  meval(
    cons(list1(q_d_matrix), mapcar(u => densif(u, basli), umat(basli, base))),
  )
}

///|
/// Enfin le polynome eliminant, retourne en macsyma
fn elimpol(base : Value, ordexp0 : Value, var1 : Value) -> Value raise {
  let bd = bind(q_ordexp, ordexp0)
  defer unbind(bd)
  set(q_d_ratmx, t) |> ignore
  let esc = escalier(base)
  with_special(q_d_ratmx, t, () => if dim_1(esc).truthy() {
    Fix(1L)
  } else if dim0(esc).truthy() {
    d_charpoly(
      matmac(
        sort_list(sous_esc(esc), (a, b) => funcall(symval(q_ordexp), [a, b]).truthy()),
        base,
      ),
      var1,
    )
  } else {
    Str("dimension positive")
  })
}

///|
fn d_elimpol_err(ordexp0 : Value, var1 : Value) -> Value raise {
  let bd = bind(q_ordexp, ordexp0)
  defer unbind(bd)
  elimpol(symbol_value(q_d_errexp1), symval(q_ordexp), var1)
}

///|
fn decmon(a : Value) -> Value raise {
  grob1__map2((u, v) => list3(list1(q_mexpt), u, v), symval(q_lvar), a)
}

///|
fn decterm(a : Value) -> Value raise {
  meval(cons(list1(q_mtimes), cons(car(a), decmon(cdr(a)))))
}

///|
fn decpol(a : Value) -> Value raise {
  meval(cons(list1(q_mplus), mapcar(x => decterm(x), a)))
}

///|
fn decode(lpol : Value, lvar : Value) -> Value raise {
  with_special(q_lvar, lvar, () => meval(
    cons(list1(q_mlist), mapcar(x => decpol(x), lpol)),
  ))
}

///|
fn d_decode_poly(poly : Value, sample : Value) -> Value raise {
  let header = if sample.truthy() && consp(sample) {
    car(sample)
  } else {
    symval(q_d_header)
  }
  let monoms = mapcar(v => list3(v, Fix(1L), Fix(1L)), fourth(header))
  let mut ans : Value = Fix(0L)
  for v in poly.iter() {
    let mut term = car(v)
    let mut degs = cdr(v)
    let mut mons = monoms
    while degs.truthy() && mons.truthy() {
      let deg = car(degs)
      let mon = car(mons)
      if !eql(Fix(0L), deg) {
        term = ptimes(term, pexpt(mon, deg))
      }
      degs = cdr(degs)
      mons = cdr(mons)
    }
    ans = pplus(ans, term)
  }
  cons(header, cons(ans, Fix(1L)))
}

///|
fn show_lazard(term : Value) -> Value raise {
  if atom(term) || atom(car(term)) {
    lisp_error("bad term")
  } else if consp(caar(term)) {
    for v in term.iter() {
      show_lazard(v) |> ignore
    }
    Nil
  } else {
    displa(d_decode_poly(term, Nil))
  }
}

///|
/// Top-level forms of grob1.lisp.
fn init_share_grob1() -> Unit raise {
  set(q_orddeg, q_orddeg) |> ignore
  set(q_d_orddeg, q_orddeg) |> ignore
  set(q_ordlex, q_ordlex) |> ignore
  set(q_d_ordlex, q_ordlex) |> ignore
  set(q_ordpairs, q_ordpairs) |> ignore
}
