// Port of share/tensor/symtry.lisp (symmetrization module for itensor):
// DECSYM, DISPSYM, REMSYM and CANFORM. itensor.lisp autoloads it
// (AUTOF '$DECSYM / '$CANFORM '|symtry|).

///|
/// Top-level forms of symtry.lisp.
fn init_share_symtry() -> Unit raise {
  set(q_symtypes, list3(q_d_sym, q_d_anti, q_d_cyc)) |> ignore
  set(q_d_symmetries, share_itensor__empty_ml()) |> ignore
}

///|
/// `($canform e f)`.
fn symtry__canform2(e : Value, f : Value) -> Value raise {
  d_canform(list2(e, f))
}

// $SYMMETRIES is a list of indexed objects with declared symmetries
// $ALLSYM if non-nil means that all indexed objects are assumed symmetric

///|
/// DEClare SYMmetries
fn d_decsym(
  name : Value,
  ncov : Value,
  ncontr : Value,
  covl : Value,
  contrl : Value,
) -> Value raise {
  if !symbolp(name) {
    merr("First argument must be a possible tensor name", []) |> ignore
  } else if !(
      fixnump(ncov) &&
      fixnump(ncontr) &&
      num_ge(ncov, Fix(0L)) &&
      num_ge(ncontr, Fix(0L))
    ) {
    merr("2nd and 3rd arguments must be non-negative integers", []) |> ignore
  } else if !(eq(caar(covl), q_mlist) && eq(caar(contrl), q_mlist)) {
    merr("4th and 5th arguments must be lists", []) |> ignore
  } else if num_lt(ncov, Fix(2L)) && num_lt(ncontr, Fix(2L)) {
    merr("This object can have no symmetry properties", []) |> ignore
  } else if (num_lt(ncov, Fix(2L)) && cdr(covl).truthy()) ||
    (num_lt(ncontr, Fix(2L)) && cdr(contrl).truthy()) {
    merr(
      "Non-null list associated with zero or single index specification",
      [],
    )
    |> ignore
  }
  let tensor = share_itensor__symname(name, ncov, ncontr)
  let symtypes = symval(q_symtypes)
  for carl in cdr(covl).iter() {
    let prop = caar(carl)
    let arglist = if member_equal(prop, symtypes) is Nil {
      merr("Invalid symmetry operator: ~M", [carl])
    } else if cddr(carl) is Nil && eq(cadr(carl), q_d_all) {
      interval(Fix(1L), ncov)
    } else {
      check_symargs(cdr(carl), one_plus(ncov))
    }
    let old = zl_get(tensor, prop)
    putprop(tensor, cons(cons(arglist, car(old)), cdr(old)), prop) |> ignore
  }
  for carl in cdr(contrl).iter() {
    let prop = caar(carl)
    let arglist = if member_equal(prop, symtypes) is Nil {
      merr("Invalid symmetry operator: ~M", [carl])
    } else if cddr(carl) is Nil && eq(cadr(carl), q_d_all) {
      interval(Fix(1L), ncontr)
    } else {
      check_symargs(cdr(carl), one_plus(ncontr))
    }
    let old = zl_get(tensor, prop)
    putprop(tensor, cons(car(old), cons(arglist, cdr(old))), prop) |> ignore
  }
  add2lnc(tensor, symval(q_d_symmetries)) |> ignore
  q_d_done
}

///|
/// Returns an ascending list of the unique elements of LL and checks that
/// they are integers between 0 and N
fn check_symargs(ll : Value, n : Value) -> Value raise {
  let mut ans : Value = Nil
  for c in ll.iter() {
    if !(fixnump(c) && num_lt(Fix(0L), c) && num_lt(c, n)) {
      merr("Bad argument encountered for symmetry operator", []) |> ignore
    } else if member_equal(c, ans) is Nil {
      ans = cons(c, ans)
    }
  }
  if cdr(ans) is Nil {
    merr("Only one distinct index in symmetry property declaration", [])
  } else {
    sort_list(ans, (a, b) => num_lt(a, b))
  }
}

///|
/// DISPlay SYMmetries
fn d_dispsym(
  name : Value,
  ncov : Value,
  ncontr : Value,
) -> Value raise {
  let tensor = share_itensor__symname(name, ncov, ncontr)
  if member_equal(tensor, cdr(symval(q_d_symmetries))) is Nil {
    return list1(share_itensor__sm())
  }
  let mut l : Value = Nil
  for q in symval(q_symtypes).iter() {
    let prop = zl_get(tensor, q)
    if prop.truthy() {
      l = append(
        l,
        list1(
          consmlist(
            list3(
              q,
              consmlist(mapcar(x => consmlist(x), car(prop))),
              consmlist(mapcar(x => consmlist(x), cdr(prop))),
            ),
          ),
        ),
      )
    }
  }
  consmlist(l)
}

///|
fn d_remsym(
  name : Value,
  ncov : Value,
  ncontr : Value,
) -> Value raise {
  let tensor = share_itensor__symname(name, ncov, ncontr)
  if member_equal(tensor, cdr(symval(q_d_symmetries))) is Nil {
    mtell(list1(Str("~&No symmetries have been declared for this tensor.~%")))
    |> ignore
  } else {
    set(q_d_symmetries, remove_equal(tensor, symval(q_d_symmetries))) |> ignore
    zl_remprop(tensor, q_d_sym) |> ignore
    zl_remprop(tensor, q_d_anti) |> ignore
    zl_remprop(tensor, q_d_cyc) |> ignore
  }
  q_d_done
}

///|
/// Convert E into CANonical FORM
fn d_canform(args : Value) -> Value raise {
  let f = if length(args) == 1 {
    t
  } else if length(args) == 2 {
    cadr(args)
  } else {
    merr("CANFORM requires one or two arguments", [])
  }
  let e = car(args)
  if atom(e) {
    e
  } else if eq(caar(e), q_mequal) {
    let a = symtry__canform2(cadr(e), f)
    mysubst0(list3(car(e), a, symtry__canform2(caddr(e), f)), e)
  } else if eq(caar(e), q_mplus) {
    mysubst0(
      simplus(
        cons(list1(q_mplus), mapcar(ee => symtry__canform2(ee, f), cdr(e))),
        Fix(1L),
        Nil,
      ),
      e,
    )
  } else if eq(caar(e), q_mtimes) {
    mysubst0(simplifya(canprod(e, f), Nil), e)
  } else if rpobj(e).truthy() {
    canten(e, f)
  } else {
    mysubst0(
      simplifya(
        cons(
          list1(caar(e)),
          mapcar(ee => symtry__canform2(ee, f), cdr(e)),
        ),
        t,
      ),
      e,
    )
  }
}

///|
/// CANonical TENsor. NFPRPOBJS is Not From Product of RP (indexed) OBJects.
fn canten(e : Value, nfprpobjs : Value) -> Value raise {
  let mut e = e
  let dummy = nonumber(cdaddr(d_indices(e)))
  if nfprpobjs.truthy() && dummy.truthy() {
    e = rename1(e, dummy)
  }
  let mut cov = copy_tree(cdadr(e))
  let mut contr = copy_tree(cdaddr(e))
  let deriv = copy_tree(cdddr(e))
  let tensor0 = share_itensor__symname(caar(e), int(length(cov)), int(length(contr)))
  // Set when reordering antisymmetric indices. Indicates whether overall
  // sign of expression needs changing.
  set(q_csign, Nil) |> ignore
  let op = caar(e)
  if eq(op, q_d_levi_civita) ||
    eq(op, q_p_levi_civita) ||
    eq(op, q_d_kdelta) ||
    eq(op, q_p_kdelta) {
    cov = antisort(cov)
    contr = antisort(contr)
  } else if symval(q_d_allsym).truthy() || eq(op, q_d_kdels) || eq(op, q_p_kdels) {
    cov = itensor_sort(cov)
    contr = itensor_sort(contr)
  } else if member_equal(d_verbify(tensor0), cdr(symval(q_d_symmetries))).truthy() {
    for type_ in symval(q_symtypes).iter() {
      for p in car(zl_get(d_verbify(tensor0), type_)).iter() {
        cov = inserts(
          symsort(extract_elements(p, cov), type_),
          cov,
          p,
        )
      }
      for p in cdr(zl_get(d_verbify(tensor0), type_)).iter() {
        contr = inserts(
          symsort(extract_elements(p, contr), type_),
          contr,
          p,
        )
      }
    }
  }
  if boundp(q_d_imetric) &&
    eq(caar(e), symval(q_d_imetric)) &&
    length(cov) == 2 &&
    length(contr) == 0 &&
    length(deriv) == 1 {
    // g([a,b],[],y) = -g([a,u],[])*g([b,v],[])*g([],[u,v],y)
    let d1 = d_idummy()
    let d2 = d_idummy()
    let sg : Value = if symval(q_csign).truthy() { Fix(1L) } else { Fix(-1L) }
    return symtry__canform2(
      list([
        list2(q_mtimes, q_simp),
        sg,
        share_itensor__metric(
          share_itensor__msl([nth(0, cov), d1]),
          share_itensor__empty_ml(),
          [],
        ),
        share_itensor__metric(
          share_itensor__msl([nth(1, cov), d2]),
          share_itensor__empty_ml(),
          [],
        ),
        append(
          list3(
            share_itensor__metric_head(),
            share_itensor__empty_ml(),
            share_itensor__msl([d1, d2]),
          ),
          deriv,
        ),
      ]),
      nfprpobjs,
    )
  }
  if boundp(q_d_imetric) &&
    eq(caar(e), symval(q_d_imetric)) &&
    length(cov) == 2 &&
    length(contr) == 0 &&
    length(deriv) == 2 {
    // g([a,b],[],y,d)
    let d1 = d_idummy()
    let d2 : Value = d_idummy()
    fn sg() -> Value { if symval(q_csign).truthy() { Fix(1L) } else { Fix(-1L) } }
    let gl = (a : Value, b : Value, ders : Array[Value]) => share_itensor__metric(
      share_itensor__msl([a, b]),
      share_itensor__empty_ml(),
      ders,
    )
    let gu = (ders : Array[Value]) => share_itensor__metric(
      share_itensor__empty_ml(),
      share_itensor__msl([d1, d2]),
      ders,
    )
    return symtry__canform2(
      list4(
        list2(q_mplus, q_simp),
        list([
          list2(q_mtimes, q_simp),
          sg(),
          gl(nth(0, cov), d1, [nth(1, deriv)]),
          gl(nth(1, cov), d2, []),
          gu([nth(0, deriv)]),
        ]),
        list([
          list2(q_mtimes, q_simp),
          sg(),
          gl(nth(0, cov), d1, []),
          gl(nth(1, cov), d2, [nth(1, deriv)]),
          gu([nth(0, deriv)]),
        ]),
        list([
          list2(q_mtimes, q_simp),
          sg(),
          gl(nth(0, cov), d1, []),
          gl(nth(1, cov), d2, []),
          gu([nth(0, deriv), nth(1, deriv)]),
        ]),
      ),
      nfprpobjs,
    )
  }
  let mut tensor = mysubst0(
    append(
      list3(car(e), consmlist(cov), consmlist(contr)),
      if symval(q_d_iframe_flag).truthy() {
        deriv
      } else {
        itensor_sort(deriv)
      },
    ),
    e,
  )
  if symval(q_csign).truthy() {
    tensor = neg(tensor)
  }
  tensor
}

///|
/// Renames dummy indices in a consistent manner
fn rename1(e : Value, dummy : Value) -> Value raise {
  sublis(cleanup0(dummy), e)
}

///|
fn cleanup0(a : Value) -> Value raise {
  let mut l : Value = Nil
  let mut n = 1
  for b in a.iter() {
    let dumx = sym(format_to_string("~a~d", [symval(q_d_idummyx), int(n)]))
    if !eq(dumx, b) {
      l = cons(cons(b, dumx), l)
    }
    n = n + 1
  }
  l
}

///|
/// Extracts the elements from B specified by the indices in A, i.e.
/// (EXTRACT-elements '(2 5) '(A B C D E F)) yields (B E)
fn extract_elements(a : Value, b : Value) -> Value raise {
  let mut a = a
  let mut b = b
  let mut n = 1
  let mut l : Value = Nil
  while a.truthy() {
    if equal(car(a), int(n)) {
      l = cons(car(b), l)
      a = cdr(a)
    }
    b = cdr(b)
    n = n + 1
  }
  nreverse(l)
}

///|
/// Substitutes A into B with respect to the index specification C
fn inserts(a : Value, b : Value, c : Value) -> Value raise {
  let mut a = a
  let mut b = b
  let mut c = c
  let mut n = 1
  let mut l : Value = Nil
  while a.truthy() {
    if equal(car(c), int(n)) {
      l = cons(car(a), l)
      a = cdr(a)
      c = cdr(c)
    } else {
      l = cons(car(b), l)
    }
    b = cdr(b)
    n = n + 1
  }
  nreconc(l, b)
}

///|
fn symsort(l : Value, type_ : Value) -> Value raise {
  if eq(type_, q_d_sym) {
    // SORT SYMmetric indices
    sort_list(l, share_itensor__less_p)
  } else if eq(type_, q_d_anti) {
    antisort(l)
  } else {
    cycsort(l)
  }
}

///|
/// SORT ANTIsymmetric indices and set CSIGN as needed
fn antisort(l : Value) -> Value raise {
  let q = sort_list(index(l), (a, b) => share_itensor__less_p(
    car(a),
    car(b),
  ))
  if equal(d_levi_civita(consmlist(mapcar(x => cdr(x), q))), Fix(-1L)) {
    set(q_csign, lbool(symval(q_csign) is Nil)) |> ignore
  }
  mapcar(x => car(x), q)
}

///|
/// (INDEX '(A B C)) yields ((A . 1) (B . 2) (C . 3))
fn index(l : Value) -> Value raise {
  let mut q : Value = Nil
  let mut n = 1
  for x in l.iter() {
    q = cons(cons(x, int(n)), q)
    n = n + 1
  }
  nreverse(q)
}

///|
/// SORT CYClic indices
fn cycsort(l : Value) -> Value raise {
  let n = to_int(cdr(least(l))) - 1
  if n == 0 {
    l
  } else {
    append(nthcdr(n, l), reverse(nthcdr(length(l) - n, reverse(l))))
  }
}

///|
/// Returns a dotted pair containing the alphanumerically least element in L
/// in the car and its index in L in the cdr
fn least(l : Value) -> Value raise {
  let mut a = cons(car(l), Fix(1L))
  let mut n = 2
  for x in cdr(l).iter() {
    if less(x, car(a)).truthy() {
      a = cons(x, int(n))
    }
    n = n + 1
  }
  a
}

///|
fn canprod(e : Value, f : Value) -> Value raise {
  let mut scalars : Value = Nil
  let mut indexed : Value = Nil
  let mut has_sum = false
  for obj in cdr(e).iter() {
    if atom(obj) {
      scalars = cons(obj, scalars)
    } else if rpobj(obj).truthy() {
      indexed = cons(obj, indexed)
    } else if eq(caar(obj), q_mplus) {
      // (throw 'foo t)
      has_sum = true
      break
    } else {
      scalars = cons(obj, scalars)
    }
  }
  if has_sum {
    return symtry__canform2(d_expand(e), f)
  }
  scalars = nreverse(scalars)
  indexed = nreverse(indexed)
  if indexed is Nil {
    e
  } else if cdr(indexed) is Nil {
    nconc_n([
      list1(list1(q_mtimes)),
      scalars,
      list1(canten(car(indexed), t)),
    ])
  } else {
    let free_indices = nonumber(cdadr(d_indices(e)))
    let described = mapcar(
      x => describe_tensor(free_indices, x),
      indexed,
    )
    let sorted = sort_list(described, (a, b) => tensorpred(
        car(a),
        car(b),
      ).truthy())
    let sorted = if symval(q_d_flipflag).truthy() {
      reverse(sorted)
    } else {
      sorted
    }
    let q = mapcar(x => cdr(x), sorted)
    let q = if f.truthy() {
      rename1(
        q,
        nonumber(cdaddr(d_indices2(cons(list1(q_mtimes), reverse(q))))),
      )
    } else {
      q
    }
    nconc_n([
      list1(list1(q_mtimes)),
      scalars,
      mapcar(z => canten(z, Nil), q),
    ])
  }
}

///|
fn tensorpred(x : Value, y : Value) -> Value raise {
  let mut x = x
  let mut y = y
  while x.truthy() {
    let a = car(x)
    let b = car(y)
    if !equal(a, b) {
      return if fixnump(a) {
        lbool(num_lt(a, b))
      } else if listp(a) && listp(b) {
        tensorpred(a, b)
      } else if a is Nil {
        t
      } else if b is Nil {
        Nil
      } else {
        alphalessp(a, b)
      }
    }
    x = cdr(x)
    y = cdr(y)
  }
  Nil
}

///|
fn describe_tensor(free_indices : Value, f : Value) -> Value raise {
  cons(tdescript(free_indices, f), f)
}

///|
fn tdescript(free_indices : Value, f : Value) -> Value raise {
  let name = caar(f)
  let indices = append_n([cdadr(f), cdaddr(f), cdddr(f)])
  let lcov = length(cdadr(f))
  let lcontr = length(cdaddr(f))
  let lderiv = length(cdddr(f))
  list([
    car(least(intersect(indices, free_indices))),
    int(lcov + lcontr + lderiv),
    int(lderiv),
    int(lcov),
    name,
  ])
}
