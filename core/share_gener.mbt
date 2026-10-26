// Port of share/tensor/gener.lisp (autoloaded by itensor): IC_CONVERT,
// MAKEBOX, AVERAGE, CONMETDERIV, FLUSH1DERIV and IGEODESIC_COORDS.

///|
/// Top-level forms of gener.lisp.
fn init_share_gener() -> Unit raise {
  set(q_d_funcs, list1(list1(q_mlist))) |> ignore
  add2lnc(
    list2(list1(q_d_average), q_d_tensor),
    symval(q_d_funcs),
  )
  |> ignore
  add2lnc(
    list3(list1(q_d_conmetderiv), q_d_exp, q_d_name),
    symval(q_d_funcs),
  )
  |> ignore
  add2lnc(
    list3(list1(q_d_flush1deriv), q_d_exp, q_d_name),
    symval(q_d_funcs),
  )
  |> ignore
  add2lnc(
    list3(list1(q_d_igeodesic_coords), q_d_exp, q_d_name),
    symval(q_d_funcs),
  )
  |> ignore
}

///|
/// Is e a symbol, or an indexed object with no dummy indices?
fn gener__assignable(e : Value) -> Bool raise {
  symbolp(e) || (rpobj(e).truthy() && cdaddr(d_indices2(e)) is Nil)
}

///|
/// $METRICCONVERT if non-NIL will allow $IC_CONVERT to rename the metric
/// tensor ($IMETRIC must be bound) with 2 covariant indices to LG and with 2
/// contravariant indices to UG.
fn d_ic_convert(ee : Value) -> Value raise {
  let e = d_expand(ee)
  let mut free : Value = Nil
  let mut lhs : Value = Nil
  let mut rhs : Value = Nil
  if atom(e) || !eq(caar(e), q_mequal) {
    merr("IC_CONVERT requires an equation as an argument", []) |> ignore
  } else {
    free = d_indices(e)
    if equal(free, symval(q_empty)) {
      return cons(list1(q_msetq), cdr(e))
    } else if gener__assignable(cadr(e)) {
      lhs = cadr(e)
      rhs = caddr(e)
    } else if gener__assignable(caddr(e)) {
      lhs = caddr(e)
      rhs = cadr(e)
    } else {
      merr(
        "At least one side of the equation must be a~\n\t\t\t      ~%symbol or a single indexed object",
        [],
      )
      |> ignore
    }
  }
  if !symbolp(lhs) && cdddr(lhs).truthy() {
    merr("Cannot assign to indexed objects with derivative ~\n\t\t\t    indices:~%~M", [
      ishow(lhs),
    ])
    |> ignore
  }
  // Set FREE to just the free indices
  free = nreverse(itensor_sort(cdadr(free)))
  set(q_indlist, Nil) |> ignore
  if symval(q_d_metricconvert).truthy() && boundp(q_d_imetric) {
    let g = symval(q_d_imetric)
    lhs = changename(
      g,
      t,
      Fix(0L),
      Fix(2L),
      q_d_ug,
      changename(g, t, Fix(2L), Fix(0L), q_d_lg, lhs),
    )
    rhs = changename(
      g,
      t,
      Fix(0L),
      Fix(2L),
      q_d_ug,
      changename(g, t, Fix(2L), Fix(0L), q_d_lg, rhs),
    )
  }
  tabulate(rhs) |> ignore
  set(q_indlist, unique(symval(q_indlist))) |> ignore
  let mut q = mapcar(x => car(x), symval(q_indlist))
  while q.truthy() {
    if memq(car(q), cdr(q)).truthy() {
      merr(
        "~\nIC_CONVERT cannot currently handle indexed objects of the same name~\n~%with different numbers of covariant and//or contravariant indices:~%~M",
        [car(q)],
      )
      |> ignore
    }
    q = cdr(q)
  }
  if !symbolp(lhs) {
    let mut flag = false
    while !flag {
      let tst = list3(caar(lhs), int(length(cdadr(lhs))), int(length(cdaddr(lhs))))
      if member_equal(tst, symval(q_indlist)).truthy() ||
        memq(car(tst), mapcar(x => car(x), symval(q_indlist))) is Nil {
        flag = true
      } else {
        mtell(
          list2(
            Str(
              "Assignment is to be made to ~M~\n~%This name with a different number of covariant and//or contravariant~\n~%indices appears on the other side of the equation. To avoid array name~\n~%conflicts, choose a new name for this object:~%",
            ),
            ishow(lhs),
          ),
        )
        |> ignore
        let name = retrieve(Nil, Nil)
        if !symbolp(name) {
          merr("Name not an atom", []) |> ignore
        }
        lhs = cons(list1(name), cdr(lhs))
      }
    }
  }
  let mut equ = cons(
    list1(q_msetq),
    list2(
      changeform(lhs),
      t_convert(summer1(rhs)),
    ),
  )
  for f in free.iter() {
    equ = append_n([
      list1(list1(q_mdo)),
      list1(f),
      list([Fix(1L), Fix(1L), Nil, q_d_dim, Nil]),
      list1(equ),
    ])
  }
  equ
}

///|
/// For each indexed object in E, appends a list of the name of that object
/// and the number of covariant and contravariant indices to the global list
/// INDLIST
fn tabulate(e : Value) -> Value raise {
  if atom(e) {
    t
  } else if rpobj(e).truthy() {
    set(
      q_indlist,
      cons(
        list3(caar(e), int(length(cdadr(e))), int(length(cdaddr(e)))),
        symval(q_indlist),
      ),
    )
  } else if eq(caar(e), q_mplus) || eq(caar(e), q_mtimes) {
    mapcar(x => tabulate(x), cdr(e))
  } else {
    Nil
  }
}

///|
/// Returns a list of the unique elements of L
fn unique(l : Value) -> Value raise {
  let mut b : Value = Nil
  for x in l.iter() {
    if member_equal(x, b) is Nil {
      b = cons(x, b)
    }
  }
  b
}

///|
/// Applies SUMMER to the products and indexed objects in E
fn summer1(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mplus) {
    cons(car(e), mapcar(x => summer1(x), cdr(e)))
  } else if eq(caar(e), q_mtimes) || rpobj(e).truthy() {
    summer(e, cdaddr(d_indices(e)))
  } else {
    e
  }
}

///|
/// Makes implicit sums explicit in the product or indexed object P where
/// DUMMY is the list of dummy indices of P at this level
fn summer(p : Value, dummy : Value) -> Value raise {
  let dummy2 = intersect(all(d_indices2(p)), dummy)
  let mut scalars : Value = Nil
  let mut indexed : Value = Nil
  let mut s : Value = Nil
  let factors = if eq(caar(p), q_mtimes) { cdr(p) } else { list1(p) }
  for obj in factors.iter() {
    if atom(obj) {
      scalars = cons(obj, scalars)
    } else if rpobj(obj).truthy() {
      if intersect(dummy2, all(d_indices2(obj))) is Nil {
        scalars = cons(obj, scalars)
      } else {
        indexed = cons(obj, indexed)
      }
    } else if eq(caar(obj), q_mplus) {
      s = t
      if intersect(dummy, all(d_indices(obj))) is Nil {
        scalars = cons(summer1(obj), scalars)
      } else {
        indexed = cons(summer1(obj), indexed)
      }
    } else {
      scalars = cons(obj, scalars)
    }
  }
  let mut regroup = false
  if s.truthy() {
    s = cdaddr(d_indices(append_n([list1(list1(q_mtimes)), scalars, indexed])))
    regroup = samelists(dummy2, s) is Nil
  }
  if regroup {
    let dummy3 = s
    s = scalars
    scalars = Nil
    for obj in s.iter() {
      if intersect(dummy3, all(d_indices(obj))) is Nil {
        scalars = cons(obj, scalars)
      } else {
        indexed = cons(obj, indexed)
      }
    }
  }
  let sums = if indexed.truthy() {
    let mut indxd = simptimes(cons(list1(q_mtimes), indexed), Fix(1L), Nil)
    for d in itensor_sort(dummy2).iter() {
      indxd = list([list1(q_d_sum), indxd, d, Fix(1L), q_d_dim])
    }
    list1(indxd)
  } else {
    Nil
  }
  simptimes(nconc_n([list1(list1(q_mtimes)), scalars, sums]), Fix(1L), Nil)
}

///|
/// Converts [[A, B], [C, D]] into (A B C D)
fn all(l : Value) -> Value raise {
  append(cdadr(l), cdaddr(l))
}

///|
/// Applies CHANGEFORM to each individual object in an expression
fn t_convert(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mplus) || eq(caar(e), q_mtimes) {
    cons(car(e), mapcar(x => t_convert(x), cdr(e)))
  } else if eq(caar(e), q_d_sum) {
    append_n([list1(car(e)), list1(t_convert(cadr(e))), cddr(e)])
  } else {
    changeform(e)
  }
}

///|
/// Converts a single object from ITENSOR format to ETENSR format
fn changeform(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() {
    let mut new_ = if covi(e) is Nil && conti(e) is Nil {
      // If no covariant and contravariant indices then make into an atom
      caar(e)
    } else {
      cons(
        list2(equiv_table(caar(e)), q_array),
        append(covi(e), conti(e)),
      )
    }
    for d in cdddr(e).iter() {
      new_ = list3(list1(q_d_diff), new_, list2(list2(q_d_ct_coords, q_array), d))
    }
    new_
  } else {
    e
  }
}

///|
/// Makes appropriate name changes converting from ITENSOR to ETENSR
fn equiv_table(a : Value) -> Value raise {
  if eq(a, q_d_ichr1) || eq(a, q_p_ichr1) {
    q_d_lcs
  } else if eq(a, q_d_ichr2) || eq(a, q_p_ichr2) {
    q_d_mcs
  } else {
    a
  }
}

///|
fn d_makebox(e : Value, name : Value) -> Value raise {
  if atom(e) {
    e
  } else if mtimesp(e).truthy() {
    makebox(e, name)
  } else if mplusp(e).truthy() {
    mysubst0(
      simplifya(
        cons(list1(q_mplus), mapcar(q => d_makebox(q, name), cdr(e))),
        Nil,
      ),
      e,
    )
  } else if mexptp(e).truthy() {
    list3(car(e), d_makebox(cadr(e), name), caddr(e))
  } else {
    e
  }
}

///|
fn makebox(e : Value, name : Value) -> Value raise {
  let mut l1 : Value = Nil
  let mut l2 : Value = Nil
  let mut l3 : Value = Nil
  for x in cdr(e).iter() {
    if rpobj(x).truthy() {
      if eq(caar(x), name) &&
        cdddr(x) is Nil &&
        cdadr(x) is Nil &&
        length(cdaddr(x)) == 2 {
        l1 = cons(x, l1)
      } else if cdddr(x).truthy() {
        l2 = cons(x, l2)
      } else {
        l3 = cons(x, l3)
      }
    } else {
      l3 = cons(x, l3)
    }
  }
  if l1 is Nil || l2 is Nil {
    return e
  }
  let mut ll2 = l2
  while ll2.truthy() {
    let mut l = l1
    while true {
      let x = car(l)
      if memq(car(cdaddr(x)), cdddar(ll2)).truthy() &&
        memq(cadr(cdaddr(x)), cdddar(ll2)).truthy() {
        l3 = cons(
          nconc(
            list3(
              list1(
                implode(append(list2(sym("["), sym("]")), cdr(explodec(caaar(ll2))))),
              ),
              cadar(ll2),
              caddar(ll2),
            ),
            setdiff(cdddar(ll2), cdaddr(x)),
          ),
          l3,
        )
        l1 = share_itensor__delete_first_equal(x, l1)
        break
      }
      l = cdr(l)
      if l is Nil {
        l3 = cons(car(ll2), l3)
        break
      }
    }
    ll2 = cdr(ll2)
  }
  simptimes(cons(list1(q_mtimes), nconc(l1, l3)), Fix(1L), Nil)
}

///|
fn d_average(n : Value) -> Value raise {
  let tensr = if length(n) == 2 { nth(1, n) } else { Nil }
  simplifya(average(tensr, nth(0, n)), Nil)
}

///|
fn average(tensr : Value, e : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() {
    if tensr is Nil || eq(caar(e), tensr) {
      average1(e)
    } else {
      e
    }
  } else {
    cons(list1(caar(e)), mapcar(e1 => average(tensr, e1), cdr(e)))
  }
}

///|
fn average1(e : Value) -> Value raise {
  if length(cdadr(e)) == 2 {
    list3(
      list1(q_mtimes),
      list3(list2(q_rat, q_simp), Fix(1L), Fix(2L)),
      list3(
        list1(q_mplus),
        cons(car(e), cons(arev(cadr(e)), cddr(e))),
        e,
      ),
    )
  } else if length(cdaddr(e)) == 2 {
    // (sic: the Lisp header is (rat smp))
    list3(
      list1(q_mtimes),
      list3(list2(q_rat, sym("smp")), Fix(1L), Fix(2L)),
      list3(
        list1(q_mplus),
        cons(car(e), cons(cadr(e), cons(arev(caddr(e)), cdddr(e)))),
        e,
      ),
    )
  } else {
    e
  }
}

///|
fn arev(l : Value) -> Value raise {
  list3(car(l), caddr(l), cadr(l))
}

///|
fn d_conmetderiv(e : Value, g : Value) -> Value raise {
  if !symbolp(g) {
    merr("Invalid metric name: ~M", [g])
  } else {
    let l = d_indices(e)
    conmetderiv(e, g, append(cdadr(l), cdaddr(l)))
  }
}

///|
fn conmetderiv(e : Value, g : Value, indexl : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() {
    if eq(caar(e), g) &&
      cdadr(e) is Nil &&
      length(cdaddr(e)) == 2 &&
      cdddr(e).truthy() {
      let mut r = cmdexpand(
        car(e),
        car(cdaddr(e)),
        cadr(cdaddr(e)),
        cadddr(e),
        indexl,
      )
      for d in cddddr(e).iter() {
        r = conmetderiv(d_idiff(list2(r, d)), g, indexl)
      }
      r
    } else {
      e
    }
  } else {
    mysubst0(
      cons(car(e), mapcar(q => conmetderiv(q, g, indexl), cdr(e))),
      e,
    )
  }
}

///|
fn cmdexpand(
  g : Value,
  i : Value,
  j : Value,
  k : Value,
  indexl : Value,
) -> Value raise {
  let mut dummy : Value = Nil
  let mut flag = false
  while !flag {
    dummy = d_idummy()
    if memq(dummy, indexl) is Nil {
      flag = true
    }
  }
  let sm = share_itensor__sm()
  list3(
    list2(q_mplus, q_simp),
    list4(
      list2(q_mtimes, q_simp),
      Fix(-1L),
      list3(g, list1(sm), list3(sm, dummy, i)),
      list3(list2(q_d_ichr2, q_simp), list3(sm, dummy, k), list2(sm, j)),
    ),
    list4(
      list2(q_mtimes, q_simp),
      Fix(-1L),
      list3(g, list1(sm), list3(sm, dummy, j)),
      list3(list2(q_d_ichr2, q_simp), list3(sm, dummy, k), list2(sm, i)),
    ),
  )
}

///|
fn d_flush1deriv(e : Value, g : Value) -> Value raise {
  if !symbolp(g) {
    merr("Invalid metric name: ~M", [g])
  } else {
    flush1deriv(e, g)
  }
}

///|
fn flush1deriv(e : Value, g : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() {
    if eq(caar(e), g) &&
      length(cdddr(e)) == 1 &&
      (
        (length(cdadr(e)) == 2 && cdaddr(e) is Nil) ||
        (length(cdaddr(e)) == 2 && cdadr(e) is Nil)
      ) {
      Fix(0L)
    } else {
      e
    }
  } else {
    subst0(
      cons(list1(caar(e)), mapcar(q => flush1deriv(q, g), cdr(e))),
      e,
    )
  }
}

///|
fn d_igeodesic_coords(exp : Value, g : Value) -> Value raise {
  d_flush1deriv(d_flush(list3(exp, q_d_ichr2, q_p_ichr2)), g)
}
