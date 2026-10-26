// Port of src/algsys.lisp: the algsys package.
//
// It solves systems of polynomial equations by straight-forward
// resultant hackery.  Other possible methods seem worse: the
// Buchberger-Spear canonical ideal basis algorithm is slow, and the
// "resolvent" method (see van der Waerden, section 79) blows up in time
// and space.

///|
/// `(merrset l)`: the argument form is already evaluated here.  With
/// ERRSET bound to T the ERRSET macro re-signals any error, so on return
/// the value is just `(list l)`.  Call sites inline the binding of ERRSET.
fn merrset(l : Value) -> Value raise {
  list1(l)
}

///|
fn d_algsys(lhslist : Value, varxlist : Value) -> Value raise {
  with_specials([(q_varlist, Nil), (q_genvar, Nil)], () => {
    set(q_d__pctrnum_list, list1(list1(q_mlist))) |> ignore
    if !d_listp(lhslist).truthy() {
      merr("algsys: first argument must be a list; found ~M", [lhslist])
      |> ignore
    } else if !d_listp(varxlist).truthy() {
      merr("algsys: second argument must be a list; found ~M", [varxlist])
      |> ignore
    }
    let numerflg = symval(q_d_numer)
    with_specials(
      [
        (q_ear_tvarxlist, Nil),
        (q_d_ratprint, Nil),
        (q_d_ratepsilon, Flo(1.0e-7)),
        (q_d_keepfloat, Nil),
        (q_varlist, reverse(cdr(varxlist))),
        (q_genvar, Nil),
        (q_d_ratfac, Nil),
        (q_d_breakup, Nil),
        (q_d_solvefactors, Nil),
        (q_n_starroots, Nil),
        (q_n_starfailures, Nil),
        (q_ear_ivar, Nil),
        (q_d_polyfactor, Nil),
        (q_d_infeval, Nil),
        (q_d_numer, Nil),
        (q_d_float, Nil),
      ],
      () => {
        let mut varxl : Value = Nil
        for var_ in cdr(
            d_listofvars(list3(list2(q_mlist, q_simp), lhslist, varxlist)),
          ).iter() {
          if symbolp(var_) && !constant(var_).truthy() {
            varxl = cons(var_, varxl)
          }
        }
        orderpointer(symval(q_varlist)) |> ignore
        let tlhslist = mapcar(q => cadr(ratf(meqhk(q))), cdr(lhslist))
        set(q_ear_ivar, caadr(ratf(q_d__pcti))) |> ignore
        set(
          q_ear_tvarxlist,
          mapcar(
            q => if mnump(q).truthy() {
              merr("algsys: variable cannot be a number; found ~M", [q])
            } else {
              caadr(ratf(q))
            },
            cdr(varxlist),
          ),
        )
        |> ignore
        putorder(symval(q_ear_tvarxlist)) |> ignore
        // (mbinding (varxl varxl) ...)
        let temp = varxl
        let mut solnlist : Value = Nil
        {
          let mut win = false
          defer {
            if win {
              munbind(temp) |> ignore
            }
          }
          mbind(temp, temp, Nil) |> ignore
          win = true
          solnlist = mapcar(
            q => addmlist(bbsorteqns(addparam(roundroots1(q), varxlist))),
            algsys(tlhslist),
          )
        }
        remorder(symval(q_ear_tvarxlist)) |> ignore
        solnlist = addmlist(solnlist)
        if numerflg.truthy() {
          with_specials([(q_d_numer, t), (q_d_float, t)], () => resimplify(
            solnlist,
          ))
        } else {
          solnlist
        }
      },
    )
  })
}

///|
/// Condense a solution list, discarding any solution that is a special
/// case of another one. (For example, if the list contained [x=1, y=1] as
/// a solution, but also just [x=1], then the first solution would be
/// discarded)
fn condensesolnl(tempsolnl : Value) -> Value raise {
  let mut solnl : Value = Nil
  let mut q = sort_list(tempsolnl, (a, b) => length(a) > length(b))
  while q is Cons(_) {
    if !subsetl(cdr(q), car(q)).truthy() {
      solnl = cons(car(q), solnl)
    }
    q = cdr(q)
  }
  solnl
}

///|
/// Check whether some element of L1 is a subset of S2 (comparing elements
/// with ALIKE1). As a special case, if S2 is '(NIL) then return true.
fn subsetl(l1 : Value, s2 : Value) -> Value raise {
  if equal(s2, list1(Nil)) {
    t
  } else {
    member_if(
      x => subsetp(x, s2, pred2=(a, b) => alike1(a, b).truthy()),
      l1,
    )
  }
}

///|
fn algsys(tlhslist : Value) -> Value raise {
  condensesolnl(
    mapcan(x => algsys0(x), distrep(mapcar(x => lofactors(x), tlhslist))),
  )
}

///|
fn algsys0(tlhslist : Value) -> Value raise {
  if tlhslist is Nil {
    list1(Nil)
  } else if equal(tlhslist, list1(Nil)) {
    Nil
  } else {
    algsys1(tlhslist)
  }
}

///|
fn algsys1(tlhslist : Value) -> Value raise {
  let rv = findleastvar(tlhslist)
  let resulteq = car(rv)
  let vartorid = cdr(rv)
  bakalevel(
    algsys(
      mapcar(
        q => if among(vartorid, q).truthy() {
          presultant(q, resulteq, vartorid)
        } else {
          q
        },
        remove_equal(resulteq, tlhslist),
      ),
    ),
    tlhslist,
    vartorid,
  )
}

///|
fn addmlist(l : Value) -> Value raise {
  cons(list1(q_mlist), l)
}

///|
/// macro for calling $EV when you are not really sure why you are calling
/// it, but you want the features of multiple evaluations and
/// unpredictabiltiy anyway.
fn what_the__dolev(l : Value) -> Value raise {
  meval(cons(list1(q_d_ev), l))
}

///|
/// eqn is ((MLIST) eq deriv)
fn rootsp(asolnset : Value, eqn : Value) -> Value raise {
  with_specials([(q_d_keepfloat, t), (q_d_numer, t), (q_d_float, t)], () => {
    let rr = what_the__dolev(list2(eqn, asolnset)) // ratsimp?
    if complexnump(cadr(rr)).truthy() && complexnump(caddr(rr)).truthy() {
      lbool(
        num_lt(
          cabs(cadr(rr)),
          num_mul(
            symval(q_d_algdelta),
            num_max(Fix(1L), cabs(caddr(rr))),
          ),
        ),
      )
    } else {
      Nil
    }
  })
}

///|
fn round1_(a : Value) -> Value raise {
  if floatp(a) {
    let a = maxima_rationalize(a)
    fpcofrat1(car(a), cdr(a))
  } else {
    a
  }
}

///|
fn roundrhs(eqn : Value) -> Value raise {
  list3(car(eqn), cadr(eqn), round1_(caddr(eqn)))
}

///|
fn roundroots1(lsoln : Value) -> Value raise {
  mapcar(x => roundrhs(x), lsoln)
}

///|
fn bbsorteqns(l : Value) -> Value raise {
  sort_list(copy_list(l), (a, b) => orderlessp(a, b).truthy())
}

///|
fn putorder(tempvarl : Value) -> Value raise {
  let mut n = 1
  let mut l = tempvarl
  while !(l is Nil) {
    putprop(car(l), int(n), q_varorder) |> ignore
    n += 1
    l = cdr(l)
  }
  Nil
}

///|
fn remorder(gvarl : Value) -> Value raise {
  mapc(x => remprop(x, q_varorder) |> ignore, gvarl)
}

///|
fn orderlessp(eqn1 : Value, eqn2 : Value) -> Value raise {
  lbool(
    num_lt(
      get(caadr(ratf(cadr(eqn1))), q_varorder),
      get(caadr(ratf(cadr(eqn2))), q_varorder),
    ),
  )
}

///|
fn addparam(asolnsetl : Value, varxlist : Value) -> Value raise {
  if length(asolnsetl) == length(symval(q_ear_tvarxlist)) {
    asolnsetl
  } else {
    let mut asolnsetl = asolnsetl
    let defvar = mapcar(x => cadr(x), asolnsetl)
    for var_ in cdr(varxlist).iter() {
      if !memalike(var_, defvar).truthy() {
        let param = make_param()
        asolnsetl = cons(
          list3(list1(q_mequal), var_, param),
          cdr(maxima_substitute(param, var_, addmlist(asolnsetl))),
        )
      }
    }
    asolnsetl
  }
}

///|
/// Iterate over the polynomials in LHSL, trying to find a "least var",
/// which is a variable that will hopefully be easiest to solve for.
/// Variables from *TVARXLIST* and their products are considered.
///
/// The function returns the polynomial with the variable with minimal
/// maximum degree, together with that variable.
fn findleastvar(lhsl : Value) -> Value raise {
  with_special(q_ear_vardegs, Nil, () => {
    let mut leasteq : Value = Nil
    let mut leastvar : Value = Nil
    // most-positive-fixnum is larger than any polynomial degree
    let mut leastdeg : Value = Fix(4611686018427387903L)
    for teq in lhsl.iter() {
      set(q_ear_vardegs, getvardegs(teq)) |> ignore
      let tdeg = killvardegsc(teq)
      for q in symval(q_ear_vardegs).iter() {
        if num_le(cdr(q), leastdeg) {
          leastdeg = cdr(q)
          leasteq = teq
          leastvar = car(q)
        }
      }
      if num_lt(tdeg, leastdeg) {
        leastdeg = tdeg
        leasteq = teq
        leastvar = car(teq)
      }
    }
    cons(leasteq, leastvar)
  })
}

///|
/// For each monomial in POLY that is mixed in the variables in *VARDEGS*,
/// iterate over all but the first variable, checking to see whether its
/// degree in the monomial is at least as high as that in *VARDEGS*. If so,
/// delete that variable and its degree from *VARDEGS*.
///
/// Returns the maximum total degree of any term in the polynomial, summing
/// degrees over the variables in *VARDEGS*.
fn killvardegsc(poly : Value) -> Value raise {
  if pconstp(poly).truthy() {
    Fix(0L)
  } else {
    let mut tdeg : Value = Fix(0L)
    let mut pt = p__terms(poly)
    while !(pt is Nil) {
      let le = pt_le(pt)
      let lc = pt_lc(pt)
      tdeg = num_max(
        tdeg,
        num_add(
          le,
          if num_eq(le, Fix(0L)) {
            killvardegsc(lc)
          } else {
            killvardegsn(lc)
          },
        ),
      )
      pt = pt_red(pt)
    }
    tdeg
  }
}

///|
/// For each monomial in POLY, look at its degree in each variable in
/// *TVARXLIST*. If the degree is at least as high as that recorded in
/// *VARDEGS*, delete that variable and its degree from *VARDEGS*.
fn killvardegsn(poly : Value) -> Value raise {
  if pconstp(poly).truthy() {
    Fix(0L)
  } else {
    let x = assq(p__var(poly), symval(q_ear_vardegs))
    if x.truthy() && num_le(cdr(x), p__le(poly)) {
      set(q_ear_vardegs, remove_equal(x, symval(q_ear_vardegs))) |> ignore
    }
    let mut tdeg : Value = Fix(0L)
    let mut pt = p__terms(poly)
    while !(pt is Nil) {
      let le = pt_le(pt)
      let lc = pt_lc(pt)
      tdeg = num_max(tdeg, num_add(le, killvardegsn(lc)))
      pt = pt_red(pt)
    }
    tdeg
  }
}

///|
/// Return degrees of POLY's monomials in the variables for which we're
/// solving. Ignores mixed terms (like x*y). Results are returned as an
/// alist with elements (VAR . DEGREE).
fn getvardegs(poly : Value) -> Value raise {
  if pconstp(poly).truthy() {
    Nil
  } else if pconstp(caddr(poly)).truthy() {
    cons(cons(car(poly), cadr(poly)), getvardegs(ptterm(cdr(poly), Fix(0L))))
  } else {
    getvardegs(ptterm(cdr(poly), Fix(0L)))
  }
}

///|
fn pconstp(poly : Value) -> Value raise {
  lbool(atom(poly) || memq(car(poly), symval(q_ear_tvarxlist)) is Nil)
}

///|
/// If POLY isn't a polynomial in the variables for which we're solving,
/// disrep it and simplify appropriately.
fn pfreeofmainvarsp(poly : Value) -> Value raise {
  if atom(poly) || memq(car(poly), symval(q_ear_tvarxlist)).truthy() {
    poly
  } else {
    simplify_after_subst(pdis(poly))
  }
}

///|
/// If POLY is a polynomial in one of the variables for which we're solving,
/// then factor it into a list of factors.
///
/// If POLY is not a polynomial in one of the solution variables, return
/// NIL.
fn lofactors(poly : Value) -> Value raise {
  let main_var_poly = pfreeofmainvarsp(poly)
  if pzerop(main_var_poly).truthy() {
    list1(Fix(0L))
  } else if atom(main_var_poly) || !atom(car(main_var_poly)) {
    // If POLY isn't a polynomial in our chosen variables, RADCAN will
    // return something whose CAR is a cons. In that case, or if the
    // polynomial is something like a number, there are no factors to
    // extract.
    Nil
  } else {
    let mut tfactors = pfactor(main_var_poly)
    let mut lfactors : Value = Nil
    while !(tfactors is Nil) {
      let main_var_factor = pfreeofmainvarsp(car(tfactors))
      if pzerop(main_var_factor).truthy() {
        return list1(Fix(0L))
      } else if !atom(main_var_factor) && atom(car(main_var_factor)) {
        lfactors = cons(pabs(main_var_factor), lfactors)
      }
      tfactors = cddr(tfactors)
    }
    lfactors
  }
}

///|
/// Combine "independent" lists in LISTOFL. If all the lists have empty
/// pairwise intersections, this returns all selections of items, one from
/// each list.
fn combiney(listofl : Value) -> Value raise {
  if member(Nil, listofl).truthy() {
    Nil
  } else {
    combiney1(remove_equal(list1(Fix(0L)), listofl))
  }
}

///|
fn combiney1(listofl : Value) -> Value raise {
  if listofl is Nil {
    list1(Nil)
  } else {
    mapcan(
      r => if intersection(car(listofl), r, pred2=(a, b) => equal(a, b)).truthy() {
        list1(r)
      } else {
        mapcar(q => cons(q, r), car(listofl))
      },
      combiney1(cdr(listofl)),
    )
  }
}

///|
fn midpnt(l : Value) -> Value raise {
  rhalf(rplus_star(car(l), cadr(l)))
}

///|
fn rflot(l : Value) -> Value raise {
  let rr = midpnt(l)
  if symval(q_realonlyratnum).truthy() {
    list3(list1(q_rat), car(rr), cdr(rr))
  } else {
    num_div(num_add(Flo(0.0), car(rr)), cdr(rr))
  }
}

///|
fn memberroot(a : Value, x : Value, eps : Value) -> Value raise {
  if x is Nil {
    Nil
  } else if num_lt(
      num_abs(num_sub(a, car(x))),
      num_div(num_add(Flo(0.0), car(eps)), cdr(eps)),
    ) {
    t
  } else {
    memberroot(a, cdr(x), eps)
  }
}

///|
fn commonroots(eps : Value, solnl1 : Value, solnl2 : Value) -> Value raise {
  if solnl1 is Nil {
    Nil
  } else if memberroot(car(solnl1), solnl2, eps).truthy() {
    cons(car(solnl1), commonroots(eps, cdr(solnl1), solnl2))
  } else {
    commonroots(eps, cdr(solnl1), solnl2)
  }
}

///|
/// Return a copy of L with all elements in odd positions removed.
fn remove_mult(l : Value) -> Value raise {
  if l.truthy() {
    cons(car(l), remove_mult(cddr(l)))
  } else {
    Nil
  }
}

///|
fn punivarp(poly : Value) -> Value raise {
  // Check if called with the number zero, return nil.
  // Related bugs: SF[609466], SF[1430379], SF[1663399]
  if numberp(poly) && num_eq(poly, Fix(0L)) {
    return Nil
  }
  let mut l = cdr_strict(poly)
  while !(l is Nil) {
    if !(
        numberp(cadr(l)) ||
        (eq(caadr(l), symval(q_ear_ivar)) && punivarp(cadr(l)).truthy())
      ) {
      return Nil
    }
    l = cddr(l)
  }
  t
}

///|
/// Return only the elements of ROOTSL whose $IMAGPART simplifies to zero
/// with SRATSIMP.
fn realonly(rootsl : Value) -> Value raise {
  remove_if_not(
    root => equal(Fix(0L), sratsimp(d_imagpart(caddr(root)))),
    rootsl,
  )
}

///|
fn presultant(p1 : Value, p2 : Value, var_ : Value) -> Value raise {
  cadr(
    ratf(
      simplify(
        d_resultant(pdis(p1), pdis(p2), pdis(list3(var_, Fix(1L), Fix(1L)))),
      ),
    ),
  )
}

///|
fn ptimeftrs(l : Value) -> Value raise {
  let ll = cddr(l)
  if ll is Nil {
    car(l)
  } else {
    ptimes(car(l), ptimeftrs(ll))
  }
}

///|
/// Substitute a solution for one variable back into the "left hand side
/// list", simplifying with SIMPLIFY-AFTER-SUBST.
fn ebaksubst(solnl : Value, lhsl : Value) -> Value raise {
  mapcar(q => ebaksubst1(solnl, q), lhsl)
}

///|
fn ebaksubst1(solnl : Value, q : Value) -> Value raise {
  let e = d_substitute(cons(list1(q_mlist), solnl), pdis(q))
  let e = simplify_after_subst(e)
  cadr(ratf(e))
}

///|
fn baksubst(solnl : Value, lhsl : Value) -> Value raise {
  // catches arith. ovfl
  let lhsl = remove(
    t,
    mapcar(
      q => car(
        merrset(with_special(q_errset, t, () => baksubst1(solnl, q))),
      ),
      lhsl,
    ),
  )
  if memq(Nil, lhsl).truthy() {
    list1(Nil)
  } else {
    lhsl
  }
}

///|
fn baksubst1(solnl : Value, poly : Value) -> Value raise {
  // sturm1 needs poly with integer coefs
  with_special(q_d_keepfloat, lbool(!symval(q_d_realonly).truthy()), () => {
    let poly1 = cdr(
      ratf(
        what_the__dolev(
          list3(pdis(poly), cons(list1(q_mlist), solnl), q_d_numer),
        ),
      ),
    )
    if complexnump(pdis(car(poly1))).truthy() && numberp(cdr(poly1)) {
      rootsp(
        cons(list1(q_mlist), solnl),
        list3(list1(q_mlist), pdis(poly), tayapprox(poly)),
      )
    } else {
      car(poly1)
    }
  })
}

///|
fn complexnump(p : Value) -> Value raise {
  let p = cadr(ratf(d_ratsimp(p, Nil)))
  lbool(numberp(p) || eq(pdis(pget(car(p))), q_d__pcti))
}

///|
/// Simplify expression after substitution.
///
/// Focus is on constant expressions:
/// o failure to reduce a constant expression that is equivalent
///   to zero causes solutions to be falsely rejected
/// o some operations, such as the reduction of nested square roots,
///   requires known sign and ordering of all terms
/// o inappropriate simplification by $RADCAN introduced errors
fn simplify_after_subst(expr : Value) -> Value raise {
  with_specials(
    [
      (q_d_keepfloat, t),
      (q_d_algebraic, t),
      (q_genvar, Nil),
      (q_varlist, Nil),
      (q_d_rootsconmode, t),
      (q_d_radexpand, t),
    ],
    () => {
      let mut e = expr
      let growth_factor : Value = Flo(1.2)
      // Try two approaches
      // 1) ratsimp
      // 2) if $constantp(e) sqrtdenest + rectform + rootscontract + ratsimp
      // take smallest expression
      let e1 = sratsimp(e)
      if d_constantp(e).truthy() {
        e = d_sqrtdenest(e)
        // Rectform does more than is wanted.  A function that denests and
        // rationalizes nested complex radicals would be better.
        // Limit expression growth.  The factor is based on trials.
        let tmp = d_rectform(e)
        if num_lt(conssize(tmp), num_mul(growth_factor, conssize(e))) {
          e = tmp
        }
        e = d_rootscontract(e)
        let e2 = sratsimp(e)
        if num_lt(conssize(e1), conssize(e2)) {
          e1
        } else {
          e2
        }
      } else {
        e1
      }
    },
  )
}

///|
/// Recursively try to find a solution to the list of polynomials in LHSL.
/// SOLNL should be a non-empty list of partial solutions.
fn bakalevel(solnl : Value, lhsl : Value, var_ : Value) -> Value raise {
  mapcan(q => bakalevel1(q, lhsl, var_), solnl)
}

///|
fn bakalevel1(solnl : Value, lhsl : Value, var_ : Value) -> Value raise {
  if !exactonly(solnl).truthy() {
    mergesoln(solnl, apprsys(baksubst(solnl, lhsl)))
  } else if solnl.truthy() {
    mergesoln(solnl, algsys(ebaksubst(solnl, lhsl)))
  } else if cdr(lhsl).truthy() {
    let poly_and_var = findleastvar(lhsl)
    bakalevel(
      callsolve(poly_and_var),
      remove_equal(car(poly_and_var), lhsl),
      var_,
    )
  } else {
    // LHSL contains one polynomial and we try to solve in one variable VAR.
    // CALLSOLVE can miss solutions when the coefficient of the highest
    // order term in VAR contains other variables in *TVARXLIST**.
    // BAKALEVELSOLVE looks for these missed solutions.
    let a = callsolve(cons(car(lhsl), var_))
    nconc(a, bakalevelsolve(car(lhsl), var_).0)
  }
}

///|
fn algsys__every_atom(pred : (Value) -> Bool raise, x : Value) -> Bool raise {
  if atom(x) {
    pred(x)
  } else {
    algsys__every_atom(pred, car(x)) && algsys__every_atom(pred, cdr(x))
  }
}

///|
/// Evaluates to true if (PRED Y) is true for every atom Y in the cons tree
/// X.
fn every_atom(pred : Value, x : Value) -> Value raise {
  if atom(x) {
    funcall(pred, [x])
  } else {
    let a = every_atom(pred, car(x))
    if a.truthy() {
      every_atom(pred, cdr(x))
    } else {
      Nil
    }
  }
}

///|
/// True if the list of solutions doesn't contain any terms that look
/// inexact (just floating point numbers, unless realonlyratnum is true)
fn exactonly(solnl : Value) -> Value raise {
  lbool(
    algsys__every_atom(
      x => !floatp(x) &&
        (symval(q_realonlyratnum) is Nil || !eq(x, q_rat)),
      solnl,
    ),
  )
}

///|
/// For each solution S in SOLNL, evaluate each element of ASOLN in light of
/// S and, collecting up the results and prepending them to S. If evaluating
/// an element in light of S caused an error, ignore the combination of
/// ASOLN and S.
fn mergesoln(asoln : Value, solnl : Value) -> Value raise {
  let unbind_ = cons(symval(q_bindlist), symval(q_loclist))
  with_special(q_errorsw, t, () => {
    let out = Collector::new()
    for q in solnl.iter() {
      let result = catch_tag(q_errorsw, () => append(
        mapcar(
          r => what_the__dolev(list2(r, cons(list1(q_mlist), q))),
          asoln,
        ),
        q,
      ))
      if eq(result, t) {
        errlfun1(unbind_) |> ignore
      }
      if !eq(result, t) {
        out.add(result)
      }
    }
    out.result()
  })
}

///|
/// Try to solve a polynomial with respect to the given variable. PV is a
/// cons pair (POLY . VAR). On success, return a list of solutions.
///
/// SOLVE introduces solutions with nested radicals, which causes problems
/// in EBAKSUBST1.  Try to clean up the solutions now.
fn callsolve(pv : Value) -> Value raise {
  mapcar(x => callsolve2(x), callsolve1(pv))
}

///|
fn callsolve1(pv : Value) -> Value raise {
  let poly = car(pv)
  let var_ = cdr(pv)
  with_specials(
    [
      (q_varlist, symval(q_varlist)),
      (q_genvar, symval(q_genvar)),
      (q_n_starroots, Nil),
      (q_n_starfailures, Nil),
      (q_d_programmode, t),
    ],
    () => if symval(q_d_algexact).truthy() ||
      !punivarp(poly).truthy() ||
      biquadraticp(poly).truthy() {
      // Call SOLVE to try to solve POLY. When it returns, the solutions it
      // found end up in *ROOTS. *FAILURES contains expressions that, if
      // solved, would lead to further solutions.
      solve(pdis(poly), pdis(list3(var_, Fix(1L), Fix(1L))), Fix(1L))
      |> ignore
      if !(
          symval(q_n_starroots).truthy() || symval(q_n_starfailures).truthy()
        ) {
        // We're certain there are no solutions
        list1(Nil)
      } else {
        // Try to find approximate solutions to the terms that SOLVE gave
        // up on (in *FAILURES) and remove any roots from SOLVE that
        // aren't known to be real if $REALONLY is true.
        let a = mapcan(
          q => callapprs(cadr(ratf(meqhk(q)))),
          remove_mult(symval(q_n_starfailures)),
        )
        let b = mapcar(
          x => list1(x),
          if symval(q_d_realonly).truthy() {
            realonly(remove_mult(symval(q_n_starroots)))
          } else {
            remove_mult(symval(q_n_starroots))
          },
        )
        append(a, b)
      }
    } else {
      callapprs(poly)
    },
  )
}

///|
/// Simplify solution returned by callsolve1
fn callsolve2(l : Value) -> Value raise {
  // l is a single element list '((mequal simp) var expr)
  let e = first(l)
  list1(list3(list1(mop(e)), second(e), simplify_after_subst(third(e))))
}

///|
/// Check whether POLY is biquadratic in its main variable: either of degree
/// at most two or of degree four and with only even powers.
fn biquadraticp(poly : Value) -> Value raise {
  if atom(poly) {
    t
  } else if symval(q_algnotexact).truthy() {
    lbool(num_lt(p__le(poly), Fix(2L)))
  } else if num_lt(p__le(poly), Fix(3L)) {
    t
  } else if num_eq(p__le(poly), Fix(4L)) {
    biquadp1(p__red(poly))
  } else {
    Nil
  }
}

///|
fn biquadp1(terms : Value) -> Value raise {
  if terms is Nil {
    t
  } else if num_eq(pt_le(terms), Fix(2L)) || num_eq(pt_le(terms), Fix(0L)) {
    biquadp1(pt_red(terms))
  } else {
    Nil
  }
}

///|
/// Try to find approximate solutions to POLY, which should be a polynomial
/// in a single variable. Uses STURM1 if we're only after real roots
/// (because $REALONLY is set). Otherwise, calls $ALLROOTS.
fn callapprs(poly : Value) -> Value raise {
  if !punivarp(poly).truthy() {
    merr(
      "algsys: Couldn't reduce system to a polynomial in one variable.",
      [],
    )
    |> ignore
  }
  with_special(q_d_dispflag, Nil, () => if symval(q_d_realonly).truthy() {
    let dis_var = pdis(list3(car(poly), Fix(1L), Fix(1L)))
    mapcar(
      q => list1(list3(list1(q_mequal), dis_var, rflot(q))),
      sturm1(poly, cons(Fix(1L), symval(q_d_algepsilon))),
    )
  } else {
    mapcar(
      x => list1(x),
      with_special(q_d_programmode, t, () => {
        let roots = cdr(d_allroots(pdis(poly)))
        if eq(caaar(roots), q_mequal) {
          roots
        } else {
          cdr(roots)
        }
      }),
    )
  })
}

///|
fn apprsys(lhsl : Value) -> Value raise {
  if lhsl is Nil {
    list1(Nil)
  } else {
    let mut tlhsl = lhsl
    while true {
      if tlhsl is Nil {
        // SHOULD TRY TO BE MORE SPECIFIC: "TOO COMPLICATED" IN WHAT SENSE??
        merr("algsys: system too complicated; give up.", []) |> ignore
      } else if pconstp(car(tlhsl)).truthy() {
        return Nil
      } else if punivarp(car(tlhsl)).truthy() {
        return bakalevel(callapprs(car(tlhsl)), lhsl, Nil)
      }
      tlhsl = cdr(tlhsl)
    }
    Nil
  }
}

///|
fn tayapprox(p : Value) -> Value raise {
  cons(
    list1(q_mplus),
    mapcar(
      x => list2(
        list1(q_mycabs),
        pdis(ptimes(list3(x, Fix(1L), Fix(1L)), pderivative(p, x))),
      ),
      listovars(p),
    ),
  )
}

///|
fn mycabs(x : Value) -> Value raise {
  if complexnump(x).truthy() {
    cabs(x)
  } else {
    Nil
  }
}

///|
/// Take selections from LOL, a list of lists, using COMBINEY, then filter
/// them with CONDENSESOLNL.
fn distrep(lol : Value) -> Value raise {
  condensesolnl(mapcar(x => reverse(x), combiney(lol)))
}

///|
fn exclude(l1 : Value, l2 : Value) -> Value raise {
  if l2 is Nil {
    Nil
  } else if member_equal(car(l2), l1).truthy() {
    exclude(l1, cdr(l2))
  } else {
    cons(car(l2), exclude(l1, cdr(l2)))
  }
}

///|
/// P is a polynomial in VAR.  VAR may not be the main variable.
/// CALLSOLVE can miss solutions when the leading (highest order)
/// coefficient C of VAR contains other variables in *TVARXLIST*.
/// Seek these missing solutions by separating P into C*VAR^N + D and
/// looking for solutions of form (C=0,D=0).
///
/// The Lisp function returns a single value; the second element of the
/// declared tuple is always nil.
fn bakalevelsolve(p : Value, var_ : Value) -> (Value, Value) raise {
  if pcoefp(p).truthy() {
    // a bare coefficient isn't an equation
    (Nil, Nil)
  } else {
    // N is highest power of VAR in polynomial P.
    // No equation in VAR if N=0.  No solution.
    let n = p__hipow_var(p, var_)
    if num_eq(n, Fix(0L)) {
      (Nil, Nil)
    } else {
      // express P as C*VAR^N + D
      let (c, d) = p__coef_x(p, var_, n)
      if p__allvars(c).truthy() {
        // Does C contain any variables from *TVARXLIST*
        (algsys(list2(c, d)), Nil) // Try and solve C=0 and D=0 using algsys
      } else {
        (Nil, Nil) // C is freeof of *TVARXLIST*.  No solution.
      }
    }
  }
}

///|
/// De-duplicated list of variables in polynomial P
fn p__allvars(p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    Nil
  } else {
    remove_duplicates(p__allvars1(p))
  }
}

///|
/// List of variables in polynomial P.  May contain duplicates.
fn p__allvars1(p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    Nil
  } else {
    let acc = Collector::new()
    let mut l = p__terms(p)
    while l is Cons(_) {
      let ci = cadr(l)
      if !pcoefp(ci).truthy() {
        acc.append_list(copy_list(p__allvars1(ci)))
      }
      l = cddr(l)
    }
    cons(p__var(p), acc.result())
  }
}

///|
/// Maximum degree of variable V in polynomial P
/// V may not be the main variable in P
fn p__hipow_var(p : Value, v : Value) -> Value raise {
  if pcoefp(p).truthy() {
    Fix(0L) // bare coefficient has degree 0
  } else if eq(p__var(p), v) {
    p__le(p) // V is main variable - return leading exponent
  } else {
    // Recursively search through coefficients of p
    let mut result : Value = Nil
    let mut l = p__terms(p)
    while l is Cons(_) {
      let h = p__hipow_var(cadr(l), v)
      if result is Nil || num_gt(h, result) {
        result = h
      }
      l = cddr(l)
    }
    if result is Nil {
      Fix(0L)
    } else {
      result
    }
  }
}

///|
/// Separate multivariable polynomial P with main variable V into C*x^n + D
/// where X may be different to V.  Return (values C D)
/// Assumes terms of P are in decending order
fn p__coef_x(p : Value, x : Value, n : Value) -> (Value, Value) raise {
  if pcoefp(p).truthy() {
    // p is a bare coefficient
    if num_eq(n, Fix(0L)) {
      (p, pzero()) // c = bare coef, d = 0
    } else {
      (pzero(), p) // c = 0,         d = bare coef
    }
  } else if eq(p__var(p), x) {
    // main variable V in P is X
    p__coef_main(p, n)
  } else {
    // P is polynomial with main variable V other than X
    // iterate over coefficients ai
    // find (ci di) such that ai = ci*x^n + di
    let v = p__var(p)
    let cterms = Collector::new()
    let dterms = Collector::new()
    let mut l = p__terms(p)
    while l is Cons(_) {
      let i = car(l)
      let ai = cadr(l)
      let (ci, di) = p__coef_x(ai, x, n)
      if !pzerop(ci).truthy() {
        cterms.add(i)
        cterms.add(ci)
      }
      if !pzerop(di).truthy() {
        dterms.add(i)
        dterms.add(di)
      }
      l = cddr(l)
    }
    (psimp(v, cterms.result()), psimp(v, dterms.result()))
  }
}

///|
/// Separate multivariable polynomial P with main variable X into C*x^n + D
/// Return (values C D)
/// Assumes terms of P are in decending order
fn p__coef_main(p : Value, n : Value) -> (Value, Value) raise {
  if pcoefp(p).truthy() {
    // bare coefficient
    if num_eq(n, Fix(0L)) {
      (p, Fix(0L)) // c = bare coef & d = 0
    } else {
      (Fix(0L), p) // c = 0         & d = bare coef
    }
  } else {
    // proper polynomial
    let mut l = p__terms(p) // list of terms in polynomial
    let var_ = p__var(p) // main variable
    let terms = Collector::new()
    while true {
      let i = car(l) // power of term
      l = cdr(l)
      let ai = car(l) // coefficient of term x^i
      l = cdr(l)
      if !num_ge(i, n) {
        break // exit via finally if n-th power not present
      }
      if num_gt(i, n) {
        // accumulate higher order terms
        terms.add(i)
        terms.add(ai)
      } else {
        // have i==n so C=ai.  Construct D and return
        return (ai, psimp(var_, append(terms.result(), l)))
      }
      if l is Nil {
        break // exit via finally if all coefficients examined
      }
    }
    (Fix(0L), p)
  }
}

///|
fn init_algsys() -> Unit raise {
  ()
}
