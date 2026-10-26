// Port of share/tensor/itensor.lisp, part 3: Levi-Civita symbols, INDICES,
// FLUSH, RENAME, COMPONENTS, CHANGENAME, HODGE, IDIM, the redefined
// I-$DEPENDENCIES and the file's top-level forms.

///|
fn d_lc0(l1 : Value) -> Value raise {
  let mut a = cdr(l1)
  if !(a.truthy() && cdr(a).truthy()) {
    return list2(list1(q_p_levi_civita), l1)
  }
  let mut b = a
  // loop1
  while true {
    if !fixnump(car(a)) {
      return list2(list1(q_p_levi_civita), l1)
    }
    a = cdr(a)
    if a is Nil {
      break
    }
  }
  let mut sign = false
  // loop3
  while true {
    a = car(b)
    b = cdr(b)
    let mut c = b
    // loop2
    while true {
      if num_eq(car(c), a) {
        return Fix(0L)
      } else if num_lt(car(c), a) {
        sign = !sign
      }
      c = cdr(c)
      if c is Nil {
        break
      }
    }
    if cdr(b) is Nil {
      break
    }
  }
  if sign {
    Fix(-1L)
  } else {
    Fix(1L)
  }
}

///|
fn d_levi_civita(l1 : Value, l2? : Value = Nil) -> Value raise {
  if l2 is Nil {
    d_lc0(l1)
  } else if like(l1, list1(list1(q_mlist))).truthy() {
    let mut l : Value = Nil
    let mut i = d_length(l2)
    while !num_lt(i, Fix(1L)) {
      l = cons(i, l)
      i = num_sub(i, Fix(1L))
    }
    list3(list2(q_d_kdelta, q_simp), share_itensor__ml(l), l2)
  } else if like(l2, list1(list1(q_mlist))).truthy() {
    let mut l : Value = Nil
    let mut i = d_length(l1)
    while !num_lt(i, Fix(1L)) {
      l = cons(i, l)
      i = num_sub(i, Fix(1L))
    }
    list3(list2(q_d_kdelta, q_simp), l1, share_itensor__ml(l))
  } else {
    merr("Mixed-index Levi-Civita symbols not supported", [])
  }
}

///|
/// `nn` fresh dummy indices.
fn share_itensor__dummies(nn : Value) -> Value raise {
  let mut l : Value = Nil
  let mut i = nn
  while !num_lt(i, Fix(1L)) {
    l = cons(d_idummy(), l)
    i = num_sub(i, Fix(1L))
  }
  l
}

///|
/// simplification rules for the totally antisymmetric LC symbol
fn d_lc_l(e : Value) -> (Value, Value) raise {
  // (catch 'match ...): a MATCHERR makes the rule fail
  if atom(e) || atom(car(e)) {
    return (Nil, Nil)
  }
  if !(eq(caar(e), q_d_levi_civita) || eq(caar(e), q_p_levi_civita)) {
    return (Nil, Nil)
  }
  let l1 = d_covi(e)
  if !d_listp(l1).truthy() {
    return (Nil, Nil)
  }
  let l2 = d_conti(e)
  if !alike1(share_itensor__empty_ml(), l2).truthy() {
    return (Nil, Nil)
  }
  if cdddr(e).truthy() {
    return (Nil, Nil)
  }
  let nn = d_length(l1)
  let l = share_itensor__dummies(nn)
  (
    list4(
      list2(q_mtimes, q_simp),
      d_kdelta(l1, share_itensor__ml(l)),
      list3(
        list2(caar(e), q_simp),
        share_itensor__ml(l),
        list1(share_itensor__sm()),
      ),
      list3(
        list2(q_mexpt, q_simp),
        meval(list2(q_mfactorial, nn)),
        Fix(-1L),
      ),
    ),
    t,
  )
}

///|
fn d_lc_u(e : Value) -> (Value, Value) raise {
  if atom(e) || atom(car(e)) {
    return (Nil, Nil)
  }
  if !(eq(caar(e), q_d_levi_civita) || eq(caar(e), q_p_levi_civita)) {
    return (Nil, Nil)
  }
  let l1 = d_covi(e)
  if !alike1(share_itensor__empty_ml(), l1).truthy() {
    return (Nil, Nil)
  }
  let l2 = d_conti(e)
  if !d_listp(l2).truthy() {
    return (Nil, Nil)
  }
  if cdddr(e).truthy() {
    return (Nil, Nil)
  }
  let nn = d_length(l2)
  let l = share_itensor__dummies(nn)
  (
    list4(
      list2(q_mtimes, q_simp),
      d_kdelta(share_itensor__ml(l), l2),
      list3(
        list2(caar(e), q_simp),
        list1(share_itensor__sm()),
        share_itensor__ml(l),
      ),
      list3(
        list2(q_mexpt, q_simp),
        meval(list2(q_mfactorial, nn)),
        Fix(-1L),
      ),
    ),
    t,
  )
}

///|
fn nonumber(l : Value) -> Value raise {
  if numberp(car(l)) {
    nonumber(cdr(l))
  } else if l is Nil {
    Nil
  } else {
    cons(car(l), nonumber(cdr(l)))
  }
}

///|
fn removeindex(e : Value, l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else if atom(e) {
    if eq(e, car(l)) {
      cdr(l)
    } else {
      cons(car(l), removeindex(e, cdr(l)))
    }
  } else {
    removeindex(cdr(e), removeindex(car(e), l))
  }
}

///|
fn indices(e : Value) -> Value raise {
  let mut top : Value = Nil
  let mut bottom : Value = Nil
  if rpobj(e).truthy() {
    top = nonumber(conti(e))
    bottom = nonumber(append(covi(e), cdddr(e)))
  } else if atom(e) {
    ()
  } else if eq(caar(e), q_mexpt) && eql(caddr(e), Fix(-1L)) {
    let x = indices(cadr(e))
    bottom = append(bottom, car(x))
    top = append(top, cadr(x))
  } else if (eq(caar(e), q_p_derivative) || eq(caar(e), q_d_diff)) &&
    (length(e) == 3 || eql(cadddr(e), Fix(1L))) {
    let x = indices(cadr(e))
    bottom = append(bottom, cadr(x))
    top = append(top, car(x))
    let x = indices(caddr(e))
    bottom = append(bottom, car(x))
    top = append(top, cadr(x))
  } else if eq(caar(e), q_mtimes) ||
    eq(caar(e), q_mnctimes) ||
    eq(caar(e), q_mncexpt) {
    for v in cdr(e).iter() {
      let x = indices(v)
      bottom = append(bottom, cadr(x))
      top = append(top, car(x))
    }
  } else if eq(caar(e), q_mplus) || eq(caar(e), q_mequal) {
    top = indices(cadr(e))
    bottom = cadr(top)
    top = car(top)
    let p0 = intersect(top, bottom)
    let q = removeindex(p0, bottom)
    let p = removeindex(p0, top)
    for v in cddr(e).iter() {
      let x0 = indices(v)
      let y0 = cadr(x0)
      let x1 = car(x0)
      let r = intersect(x1, y0)
      let x = removeindex(r, x1)
      let y = removeindex(r, y0)
      if !(samelists(x, p).truthy() && samelists(y, q).truthy()) {
        merr("Improper indices in ~M", [v]) |> ignore
      }
      top = union_(top, r)
      bottom = union_(bottom, r)
    }
  } else if eq(caar(e), q_d_sum) || eq(caar(e), q_p_sum) {
    top = list1(caddr(e))
    bottom = list1(caddr(e))
  } else if eq(caar(e), q_p_idiff) || eq(caar(e), q_d_idiff) {
    // Derivative indices are not counted: if the user wants to count
    // derivative indices, those should be part of the tensor expression; if
    // the expression is undiff'd, there must be a reason!
    let x = indices(cadr(e))
    bottom = append(bottom, cadr(x))
    top = append(top, car(x))
  }
  list2(top, bottom)
}

///|
fn d_indices(e : Value) -> Value raise {
  let top0 = indices(e)
  let bottom0 = cadr(top0)
  let top1 = car(top0)
  let x = if symval(q_d_flipflag).truthy() {
    intersect(bottom0, top1)
  } else {
    intersect(top1, bottom0)
  }
  let top = removeindex(x, top1)
  let bottom = removeindex(x, bottom0)
  share_itensor__ml(
    list2(share_itensor__ml(append(top, bottom)), share_itensor__ml(x)),
  )
}

///|
/// "True" if A and B have the same distinct elements
fn samelists(a : Value, b : Value) -> Value raise {
  if length(a) != length(b) {
    return Nil
  }
  for x in a.iter() {
    if memq(x, b) is Nil {
      return Nil
    }
  }
  t
}

///|
/// Replaces the given (as arguments to FLUSH) indexed objects by zero if
/// they have no derivative indices.
fn d_flush(n : Value) -> Value raise {
  if length(n) < 2 {
    merr("FLUSH takes at least 2 arguments", [])
  } else {
    let l = cdr(n)
    if !every(v => symbolp(v), l) {
      merr(
        "All arguments but the first must be names of\nindexed objects",
        [],
      )
    } else {
      flush(nth(0, n), l, t)
    }
  }
}

///|
/// Replaces the given (as arguments to FLUSHD) indexed objects by zero if
/// they have any derivative indices.
fn d_flushd(n : Value) -> Value raise {
  if length(n) < 2 {
    merr("FLUSH takes at least 2 arguments", [])
  } else {
    let l = cdr(n)
    if !every(v => symbolp(v), l) {
      merr(
        "All arguments but the first must be names of\nindexed objects",
        [],
      )
    } else {
      flush(nth(0, n), l, Nil)
    }
  }
}

///|
fn flush(e : Value, l : Value, flag : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() {
    if memq(caar(e), l) is Nil {
      e
    } else if cdddr(e).truthy() {
      if flag.truthy() {
        e
      } else {
        Fix(0L)
      }
    } else if flag.truthy() {
      Fix(0L)
    } else {
      e
    }
  } else {
    subst0(cons(list1(caar(e)), mapcar(q => flush(q, l, flag), cdr(e))), e)
  }
}

///|
/// Replaces by zero all indexed objects that have n or more derivative
/// indices
fn d_flushnd(e : Value, name : Value, n : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() {
    if equal(caar(e), name) &&
      num_gt(int(length(cdddr(e))), num_sub(n, Fix(1L))) {
      Fix(0L)
    } else {
      e
    }
  } else {
    subst0(
      cons(list1(caar(e)), mapcar(q => d_flushnd(q, name, n), cdr(e))),
      e,
    )
  }
}

///|
fn d_rename(nargs : Value) -> Value raise {
  let index : Value = if length(nargs) == 1 { Fix(1L) } else { nth(1, nargs) }
  rename(nth(0, nargs), index)
}

///|
/// Renames dummy indices consistently
fn rename(e : Value, index : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() ||
    eq(caar(e), q_mtimes) ||
    (
      (eq(caar(e), q_p_derivative) || eq(caar(e), q_d_diff)) &&
      (length(e) == 3 || eql(cadddr(e), Fix(1L)))
    ) {
    // If an indexed object or a product or a derivative expression
    let l = cdaddr(d_indices(e)) // Gets list of dummy indices
    simptimes(
      reorder(
        if l.truthy() {
          set(q_itensor_n, index) |> ignore
          sublis(itensor_cleanup(l, index), e)
        } else {
          e
        },
      ),
      Fix(1L),
      t,
    )
  } else {
    // Otherwise map $RENAME on each of the subparts e.g. a sum
    mysubst0(
      simplifya(cons(list1(caar(e)), mapcar(x => rename(x, index), cdr(e))), t),
      e,
    )
  }
}

///|
/// Reorders contravariant, covariant, derivative indices
/// Example: F([A,B],[C,D],E,F)
fn reorder(e : Value) -> Value raise {
  mysubst0(
    cons(
      list1(q_mtimes),
      mapcar(
        x => if rpobj(x).truthy() {
          let x = d_renorm(x)
          let allsym = symval(q_d_allsym).truthy()
          nconc(
            list3(
              car(x), // ($f simp)
              share_itensor__ml(
                if allsym {
                  itensor_sort(copy_tree(cdadr(x)))
                } else {
                  cdadr(x)
                },
              ), // ($a $b)
              share_itensor__ml(
                if allsym {
                  itensor_sort(copy_tree(cdaddr(x)))
                } else {
                  cdaddr(x)
                },
              ),
            ), // ($c $d)
            if symval(q_d_iframe_flag).truthy() {
              cdddr(x)
            } else {
              itensor_sort(copy_tree(cdddr(x)))
            },
          ) // ($e $f)
        } else {
          x
        },
        if eq(caar(e), q_mtimes) {
          cdr(e)
        } else {
          list1(e)
        },
      ),
    ),
    e,
  )
}

///|
/// The closure variable DUMX shared by ITENSOR-CLEANUP and CLEANUP1.
let share_itensor__dumx : Ref[Value] = Ref(Nil)

///|
fn itensor_cleanup(a : Value, nn : Value) -> Value raise {
  set(q_itensor_n, nn) |> ignore
  share_itensor__dumx.val = Nil
  cleanup1(a)
}

///|
/// Make list of dotted pairs indicating substitutions i.e. ((a . #1) (b . #2))
fn cleanup1(a : Value) -> Value raise {
  if a is Nil {
    return Nil
  }
  // Keep proper order of indices
  share_itensor__dumx.val = implode(
    nconc(exploden(symval(q_d_idummyx)), exploden(symval(q_itensor_n))),
  )
  set(q_itensor_n, one_plus(symval(q_itensor_n))) |> ignore
  if eq(share_itensor__dumx.val, car(a)) {
    cleanup1(cdr(a))
  } else {
    let p = cons(car(a), share_itensor__dumx.val)
    cons(p, cleanup1(cdr(a)))
  }
}

///|
/// Sort into ascending order
fn itensor_sort(l : Value) -> Value raise {
  if cdr(l).truthy() {
    sort_list(l, share_itensor__less_p)
  } else {
    l
  }
}

///|
fn d_remcomps(tensor : Value) -> Value raise {
  zl_remprop(tensor, q_expr) |> ignore
  zl_remprop(tensor, q_carrays) |> ignore
  zl_remprop(tensor, q_texprs) |> ignore
  zl_remprop(tensor, q_indexed) |> ignore
  zl_remprop(tensor, q_indexed) |> ignore
  zl_remprop(tensor, q_tsubr) |> ignore
  if functionp(tensor) {
    fmakunbound(tensor) |> ignore
  }
  q_d_done
}

///|
fn d_indexed_tensor(tensor : Value) -> Value raise {
  if zl_get(tensor, q_expr).truthy() {
    merr("~M has expr", [tensor]) |> ignore
  }
  let fp = zl_get(tensor, q_subr)
  if fp.truthy() {
    let new_ = gensym()
    putprop(new_, fp, q_subr) |> ignore
    zl_remprop(tensor, q_subr) |> ignore
    putprop(tensor, new_, q_tsubr) |> ignore
  }
  putprop(tensor, t, q_indexed) |> ignore
  let nn = sym("nn")
  putprop(
    tensor,
    list3(
      q_lambda,
      nn,
      list3(q_tensoreval, list2(q_quote, tensor), list2(q_listify, nn)),
    ),
    q_expr,
  )
  |> ignore
  // (eval (subst tensor 'g '(defmfun g nn (tensoreval 'g (listify nn)))))
  defun(tensor, args => tensoreval(tensor, list(args)))
  q_d_done
}

///|
fn allfixed(l : Value) -> Value raise {
  lbool(
    l.truthy() &&
    fixnump(car(l)) &&
    (cdr(l) is Nil || allfixed(cdr(l)).truthy()),
  )
}

///|
fn tensoreval(tensor : Value, indxs : Value) -> Value raise {
  let mut der : Value = Nil
  let mut con : Value = Nil
  if cdr(indxs).truthy() {
    con = cdadr(indxs)
    der = cddr(indxs)
  }
  select(tensor, cdar(indxs), con, der)
}

///|
fn d_components(tensor : Value, comp : Value) -> Value raise {
  let mut comp = comp
  if !rpobj(tensor).truthy() {
    merr("Improper 1st arg to COMPONENTS: ~M", [tensor]) |> ignore
  }
  let len1 = length(covi(tensor))
  let len2 = length(conti(tensor))
  let len3 = length(deri(tensor))
  if !atom(comp) && eq(caar(comp), q_d_matrix) {
    if len1 + len2 + len3 == 2 {
      let name = gensym()
      set(name, comp) |> ignore
      comp = name
    } else {
      merr("Needs two indices for COMPONENTS from matrix:~%~M", [tensor])
      |> ignore
    }
  }
  let prop = if symbolp(comp) && len1 + len2 + len3 > 0 {
    q_carrays
  } else {
    let name = append_n([covi(tensor), conti(tensor), deri(tensor)])
    if samelists(name, cdadr(d_indices(comp))).truthy() {
      comp = cons(comp, name)
      q_texprs
    } else {
      merr("Args to COMPONENTS do not have the same free indices", [])
    }
  }
  let tensor = caar(tensor)
  let key = list3(int(len1), int(len2), int(len3))
  let name = zl_get(tensor, prop)
  let entry = if name.truthy() { assoc_equal(key, name) } else { Nil }
  if entry.truthy() {
    rplacd(entry, comp) |> ignore
  } else {
    putprop(tensor, cons(cons(key, comp), name), prop) |> ignore
  }
  if zl_get(tensor, q_indexed) is Nil {
    d_indexed_tensor(tensor) |> ignore
  }
  q_d_done
}

///|
fn select(tensor : Value, l1 : Value, l2 : Value, l3 : Value) -> Value raise {
  let l2 = append(minusi(l1), l2)
  let l1 = plusi(l1)
  let mut subs = append_n([l1, l2, l3])
  let idx = list3(int(length(l1)), int(length(l2)), int(length(l3)))
  let mut prop : Value = Nil
  let mut carray = false
  if allfixed(subs).truthy() {
    prop = zl_get(tensor, q_carrays)
    if prop.truthy() {
      prop = assoc_equal(idx, prop)
      carray = prop.truthy()
    }
  }
  if carray {
    prop = cons(list2(cdr(prop), q_array), subs)
    subs = meval(prop)
    if alike1(prop, subs).truthy() {
      Fix(0L)
    } else {
      subs
    }
  } else {
    prop = assoc_equal(idx, zl_get(tensor, q_texprs))
    if prop.truthy() {
      sublis(
        mapcar2((a, b) => cons(a, b), cddr(prop), subs),
        d_rename(
          list2(
            cadr(prop),
            if boundp(q_itensor_n) {
              symval(q_itensor_n)
            } else {
              Fix(1L)
            },
          ),
        ),
      )
    } else {
      prop = zl_get(tensor, q_tsubr)
      if prop.truthy() {
        apply(
          prop,
          list3(
            share_itensor__ml(l1),
            share_itensor__ml(l2),
            share_itensor__ml(l3),
          ),
        )
      } else if l3.truthy() {
        d_idiff(list2(select(tensor, l1, l2, cdr(l3)), car(l3)))
      } else {
        append(
          list3(list2(tensor, q_simp), share_itensor__ml(l1), share_itensor__ml(l2)),
          l3,
        )
      }
    }
  }
}

///|
fn d_entertensor(nargs : Value) -> Value raise {
  let n = length(nargs)
  let fun = if n > 1 {
    merr("ENTERTENSOR takes 0 or 1 arguments only", [])
  } else if n == 0 {
    mtell(list1(Str("Enter tensor name: "))) |> ignore
    meval(retrieve(Nil, Nil))
  } else {
    nth(0, nargs)
  }
  mtell(list1(Str("Enter a list of the covariant indices: "))) |> ignore
  let mut cov = checkindex(meval(retrieve(Nil, Nil)), fun)
  if atom(cov) {
    cov = share_itensor__ml(list1(cov))
  }
  mtell(list1(Str("Enter a list of the contravariant indices: "))) |> ignore
  let mut contr = checkindex(meval(retrieve(Nil, Nil)), fun)
  if atom(contr) {
    contr = share_itensor__ml(list1(contr))
  }
  mtell(list1(Str("Enter a list of the derivative indices: "))) |> ignore
  let deriv0 = checkindex(meval(retrieve(Nil, Nil)), fun)
  let deriv = if atom(deriv0) { list1(deriv0) } else { cdr(deriv0) }
  if memberl(cdr(cov), deriv).truthy() {
    mtell(
      list1(
        Str(
          "Warning: There are indices that are both covariant and derivative%",
        ),
      ),
    )
    |> ignore
  }
  d_ishow(nconc(list3(list2(fun, q_simp), cov, contr), deriv))
}

///|
fn checkindex(e : Value, f : Value) -> Value raise {
  if atom(e) && !eq(e, f) {
    e
  } else if eq(caar(e), q_mlist) &&
    every(v => atom(v), cdr(e)) &&
    memq(f, e) is Nil {
    e
  } else {
    merr("Indices must be atoms different from the tensor name", [])
  }
}

///|
fn memberl(a : Value, b : Value) -> Value raise {
  for carl in a.iter() {
    if symbolp(carl) && member_equal(carl, b).truthy() {
      return t
    }
  }
  Nil
}

///|
/// Converts from Lisp list to Macsyma list
fn consmlist(l : Value) -> Value raise {
  share_itensor__ml(l)
}

///|
/// `(delete x l :count 1 :test #'equal)` on a fresh copy.
fn share_itensor__delete_first_equal(x : Value, l : Value) -> Value {
  let c = Collector::new()
  let mut found = false
  for y in l.iter() {
    if !found && equal(x, y) {
      found = true
    } else {
      c.add(y)
    }
  }
  c.result()
}

///|
/// $INDICES2 is similar to $INDICES except that here dummy indices are
/// picked off as they first occur in going from left to right through the
/// product or indexed object. Also, $INDICES2 works only on the top level of
/// a product and will miss indices for products of sums (which is used to
/// advantage by $IC_CONVERT).
fn d_indices2(e : Value) -> Value raise {
  if atom(e) {
    return symval(q_empty)
  }
  if !(eq(caar(e), q_mtimes) || eq(caar(e), q_mnctimes) || rpobj(e).truthy()) {
    return d_indices(e)
  }
  let mut l : Value = Nil
  let factors = if eq(caar(e), q_mtimes) || eq(caar(e), q_mnctimes) {
    cdr(e)
  } else {
    list1(e)
  }
  for a in factors.iter() {
    if rpobj(a).truthy() {
      l = append_n([l, covi(a), conti(a), cdddr(a)])
    }
  }
  let mut ind = l
  let mut free : Value = Nil
  let mut dummy : Value = Nil
  while ind.truthy() {
    let index = car(ind)
    if member_equal(index, dummy).truthy() {
      merr("~M has improper indices", [ishow(e)]) |> ignore
    } else if member_equal(index, cdr(ind)).truthy() {
      dummy = cons(index, dummy)
      ind = share_itensor__delete_first_equal(index, copy_tree(cdr(ind)))
    } else {
      free = cons(index, free)
      ind = cdr(ind)
    }
  }
  consmlist(list2(consmlist(nreverse(free)), consmlist(nreverse(dummy))))
}

///|
/// Change the name of the indexed object A to B in E
fn d_changename(a : Value, b : Value, e : Value) -> Value raise {
  // INDSPEC is INDex SPECification flag
  let mut old : Value = Nil
  let mut indspec : Value = Nil
  let mut ncov : Value = Nil
  let mut ncontr : Value = Nil
  let mut ok = false
  if symbolp(a) {
    old = a
    ok = old.truthy()
  }
  if !ok && d_listp(a).truthy() && length(cdr(a)) == 3 {
    old = cadr(a)
    if symbolp(old) {
      ncov = caddr(a)
      if fixnump(ncov) {
        ncontr = cadddr(a)
        if fixnump(ncontr) {
          indspec = t
          ok = true
        }
      }
    }
  }
  if !ok {
    merr("Improper first argument to CHANGENAME: ~M", [a])
  } else if !symbolp(b) {
    merr("Second argument to CHANGENAME must be a symbol", [])
  } else {
    changename(old, indspec, ncov, ncontr, b, e)
  }
}

///|
fn changename(
  a : Value,
  indspec : Value,
  ncov : Value,
  ncontr : Value,
  b : Value,
  e : Value,
) -> Value raise {
  if atom(e) || eq(caar(e), q_rat) {
    e
  } else if rpobj(e).truthy() {
    if eq(caar(e), a) &&
      (
        if indspec.truthy() {
          equal(int(length(cdadr(e))), ncov) &&
          equal(int(length(cdaddr(e))), ncontr)
        } else {
          true
        }
      ) {
      cons(cons(b, cdar(e)), cdr(e))
    } else {
      e
    }
  } else {
    mysubst0(
      cons(car(e), mapcar(q => changename(a, indspec, ncov, ncontr, b, q), cdr(e))),
      e,
    )
  }
}

///|
fn d_coord(n : Value) -> Value raise {
  for a in n.iter() {
    if !symbolp(a) {
      merr("~M is not a valid name.", [a]) |> ignore
    } else {
      add2lnc(a, symval(q_d_coord)) |> ignore
    }
  }
  q_d_done
}

///|
fn d_remcoord(args : Value) -> Value raise {
  if length(args) == 1 && eq(car(args), q_d_all) {
    set(q_d_coord, list1(list1(q_mlist))) |> ignore
    q_d_done
  } else {
    for c in args.iter() {
      set(q_d_coord, delete(c, symval(q_d_coord))) |> ignore
    }
    q_d_done
  }
}

// Additions on 5/19/2004 -- VTT

///|
fn d_listoftens(e : Value) -> Value raise {
  itensor_sort(share_itensor__ml(listoftens(e)))
}

///|
fn listoftens(e : Value) -> Value raise {
  if atom(e) {
    Nil
  } else if rpobj(e).truthy() {
    list1(e)
  } else {
    let mut l : Value = Nil
    for x in cdr(e).iter() {
      l = union_(l, listoftens(x), pred2=(a, b) => equal(a, b))
    }
    l
  }
}

///|
fn numlist(n? : Value = Fix(1L)) -> Value raise {
  let c = Collector::new()
  let mut i = n
  while num_le(i, symval(q_d_dim)) {
    c.add(i)
    i = one_plus(i)
  }
  c.result()
}

///|
/// showcomps(tensor):=block([i1,i2,ind:indices(tensor)[1]],
///   if length(ind)=0 then ishow(ev(tensor))
///   else if length(ind)=1 then ishow(makelist(ev(tensor,ind[1]=i1),i1,1,dim))
///   else if length(ind)=2 then ishow(tensor=apply('matrix,makelist(makelist(
///     ev(tensor,[ind[1]=i1,ind[2]=i2]),i1,1,dim),i2,1,dim)))
///   else for i1 thru dim do (showcomps(subst(i1,last(ind),tensor)),
///     if length(ind)=3 and i1<dim then linenum:linenum+1));
fn d_showcomps(e : Value) -> Value raise {
  let ind = cdadr(d_indices(e))
  let n = length(ind)
  if n < 1 {
    d_ishow(meval(list2(list1(q_d_ev), e))) |> ignore
  } else if n < 2 {
    d_ishow(
      share_itensor__ml(
        mapcar(
          i => meval(list3(list1(q_d_ev), e, list3(list1(q_mequal), car(ind), i))),
          numlist(),
        ),
      ),
    )
    |> ignore
  } else if n < 3 {
    d_ishow(
      list3(
        list1(q_mequal),
        e,
        cons(
          list2(q_d_matrix, q_simp),
          mapcar(
            j => share_itensor__ml(
              mapcar(
                i => meval(
                  list4(
                    list1(q_d_ev),
                    e,
                    list3(list1(q_mequal), car(ind), i),
                    list3(list1(q_mequal), cadr(ind), j),
                  ),
                ),
                numlist(),
              ),
            ),
            numlist(),
          ),
        ),
      ),
    )
    |> ignore
  } else {
    mapcar(
      i => {
        d_showcomps(d_substitute(i, car(last(ind)), expr=e)) |> ignore
        if n < 4 && num_lt(i, symval(q_d_dim)) {
          set(q_d_linenum, one_plus(symval(q_d_linenum)))
        } else {
          Nil
        }
      },
      numlist(),
    )
    |> ignore
  }
  Nil
}

///|
/// Implementation of the Hodge star operator. Based on the following
/// MAXIMA-language implementation:
///
/// hodge(e):=
/// (
///     [
///         len:length(indices(e)[1]),
///         idx1:makelist(idummy(),i,len+1,dim),
///         idx2:makelist(idummy(),i,len+1,dim)
///     ],
///     funmake("*",makelist(funmake(imetric,[[idx1[i],idx2[i]]]),i,1,dim-len))*
///                 funmake(levi_civita,[[],append(idx1,indices(e)[1])])*e/len!
/// )$
fn d_hodge(e : Value) -> Value raise {
  let len = d_length(cadr(d_indices(e)))
  if num_gt(len, symval(q_d_dim)) {
    return Fix(0L)
  }
  let mk_idx = () => {
    let mut l : Value = Nil
    let mut i = symval(q_d_dim)
    while !eql(i, len) {
      l = cons(d_idummy(), l)
      i = num_sub(i, Fix(1L))
    }
    l
  }
  let mut idx1 = mk_idx()
  let mut idx2 = mk_idx()
  let head = list4(
    list1(q_mtimes),
    e,
    list3(list1(q_rat), Fix(1L), factorial(len)),
    list3(
      list1(q_d_levi_civita),
      share_itensor__empty_ml(),
      cons(
        list2(q_mlist, q_simp),
        append(reverse(idx1), cdadr(d_indices(e))),
      ),
    ),
  )
  let mut l : Value = Nil
  while idx1.truthy() {
    l = cons(
      list2(
        list1(symval(q_d_imetric)),
        cons(list1(q_mlist), list2(car(idx1), car(idx2))),
      ),
      l,
    )
    idx1 = cdr(idx1)
    idx2 = cdr(idx2)
  }
  append(head, l)
}

///|
/// "name-ncov-ncontr": the symbol carrying the symmetries of a tensor.
fn share_itensor__symname(name : Value, ncov : Value, ncontr : Value) -> Value raise {
  implode(
    append_n([
      exploden(name),
      list1(Fix(45L)),
      exploden(ncov),
      list1(Fix(45L)),
      exploden(ncontr),
    ]),
  )
}

///|
/// This version of remsym remains silent when an attempt is made to remove
/// non-existent symmetries. Used by $idim below.
fn remsym(name : Value, ncov : Value, ncontr : Value) -> Value raise {
  let tensor = share_itensor__symname(name, ncov, ncontr)
  if member_equal(tensor, cdr(symval(q_d_symmetries))).truthy() {
    set(q_d_symmetries, remove_equal(tensor, symval(q_d_symmetries))) |> ignore
    zl_remprop(tensor, q_d_sym) |> ignore
    zl_remprop(tensor, q_d_anti) |> ignore
    zl_remprop(tensor, q_d_cyc)
  } else {
    Nil
  }
}

///|
/// This function sets the metric dimensions and Levi-Civita symmetries.
fn d_idim(n : Value) -> Value raise {
  let rm = () => {
    let dim = symval(q_d_dim)
    remsym(q_p_levi_civita, dim, Fix(0L)) |> ignore
    remsym(q_p_levi_civita, Fix(0L), dim) |> ignore
    remsym(q_d_levi_civita, dim, Fix(0L)) |> ignore
    remsym(q_d_levi_civita, Fix(0L), dim) |> ignore
  }
  rm()
  set(q_d_dim, n) |> ignore
  rm()
  let anti = () => lread("((mlist) (($anti) $all))")
  let none = () => list1(list1(q_mlist))
  funcall(q_d_decsym, [q_p_levi_civita, n, Fix(0L), anti(), none()]) |> ignore
  funcall(q_d_decsym, [q_p_levi_civita, Fix(0L), n, none(), anti()]) |> ignore
  funcall(q_d_decsym, [q_d_levi_civita, n, Fix(0L), anti(), none()]) |> ignore
  funcall(q_d_decsym, [q_d_levi_civita, Fix(0L), n, none(), anti()])
}

///|
/// The literal '((mlist simp)) of I-$DEPENDENCIES, which the Lisp code
/// assigns to $DEPENDENCIES and then extends destructively.
let share_itensor__deps_lit : Value = list1(list2(q_mlist, q_simp))

///|
/// The itensor redefinition of I-$DEPENDENCIES (comm.lisp): dependencies
/// on arbitrary (non-symbol) objects, e.g. indexed objects, are allowed.
fn share_itensor__i_dependencies(l : Value) -> Value raise {
  let mut res : Value = Nil
  for z in l.iter() {
    if atom(z) {
      merr("depends: argument must be a non-atomic expression; found ~M", [z])
      |> ignore
    } else if eq(caar(z), q_mqapply) || memq(q_array, cdar(z)).truthy() {
      merr("depends: argument cannot be a subscripted expression; found ~M", [
        z,
      ])
      |> ignore
    } else {
      let mut zz = z
      let mut y : Value = Nil
      while zz.truthy() {
        if cadr(zz).truthy() && member(cadr(zz), y) is Nil {
          y = cons(cadr(zz), y)
        }
        zz = cdr(zz)
      }
      y = reverse(y)
      mputprop(caar(z), y, q_depends) |> ignore
      res = cons(cons(list1(caar(z)), y), res)
      if cdr(symval(q_d_dependencies)) is Nil {
        set(q_d_dependencies, share_itensor__deps_lit) |> ignore
      }
      add2lnc(cons(cons(caar(z), Nil), y), symval(q_d_dependencies)) |> ignore
    }
  }
  cons(list2(q_mlist, q_simp), reverse(res))
}

///|
/// AUTOF (autol.lisp). The stub calls AALOAD through its function cell: a
/// direct call would make the top-level initializer of autol's loader hook
/// part of a definition cycle through this file's init.
fn share_itensor__autof(fun : Value, file : Value) -> Unit {
  if !fboundp(fun) {
    defun(fun, l => {
      funcall(q_aload, [file]) |> ignore
      apply(fun, list(l))
    })
  }
}

///|
/// A stub in the function cell of `fun` that loads the symtry module (as
/// AUTOF does for a Lisp file) and then calls the real definition.
fn share_itensor__autof_symtry(fun : Value) -> Unit {
  if !fboundp(fun) {
    defun(fun, l => {
      share_itensor__load_symtry()
      apply(fun, list(l))
    })
  }
}

///|
/// Top-level forms of itensor.lisp.
fn init_share_itensor() -> Unit raise {
  if d_get(q_d_itensor, q_d_version).truthy() {
    merr("ITENSOR already loaded", []) |> ignore
  } else {
    d_put(q_d_itensor, q_d_v20210714, q_d_version) |> ignore
  }
  // Various functions in Itensor have been parceled out to separate files.
  // A function in one of these files will only be loaded in (automatically)
  // if explicitly used in the Maxima. The current status of these separate
  // files are:
  //    Filename          Macsyma Functions
  //    --------          -----------------
  //    CANTEN FASL       CANTEN, CONCAN, IRPMON
  //    GENER FASL        IC_CONVERT, MAKEBOX, AVERAGE, CONMETDERIV,
  //                      FLUSH1DERIV, IGEODESIC_COORDS
  //    SYMTRY FASL       CANFORM, DECSYM, DISPSYM, REMSYM
  // Port: symtry.lisp and gener.lisp are ported with itensor
  // (share_itensor_symtry.mbt, share_itensor_gener.mbt) and loaded on first
  // use; canten.lisp is not ported (its autoload stubs report that the Lisp
  // file cannot be loaded).
  share_itensor__autof_gener(q_d_ic_convert)
  share_itensor__autof_symtry(q_d_decsym)
  share_itensor__autof_symtry(q_d_canform)
  share_itensor__autof(q_d_canten, Str("canten"))
  share_itensor__autof_gener(q_d_makebox)
  share_itensor__autof_gener(q_d_igeodesic_coords)
  share_itensor__autof_gener(q_d_conmetderiv)
  share_itensor__autof(q_d_name, Str("canten"))
  set(q_d_idummyx, q_d_op_pct) |> ignore // Prefix for dummy indices
  set(q_d_icounter, Fix(0L)) |> ignore // Dummy variable numeric index
  set(q_smlist, list2(q_mlist, q_simp)) |> ignore // Simplified mlist header
  set(q_d_vect_coords, Nil) |> ignore // Used when differentiating w.r.t. a number
  set(q_d_coord, share_itensor__empty_ml()) |> ignore // Objects treated liked coordinates in diff
  set(q_d_allsym, Nil) |> ignore // If T then all indexed objects symmetric
  set(q_d_metricconvert, t) |> ignore // Flag used by $ic_convert
  set(q_d_iframe_flag, Nil) |> ignore
  set(q_d_itorsion_flag, Nil) |> ignore
  // KDELTA has special contraction property because it contracts with any
  // indexed object.
  putprop(q_d_kdelta, list1(cons(q_op_sp, q_op_sp)), q_contractions) |> ignore
  // So derivative will be zero
  meval(list3(list1(q_d_declare), q_p_kdelta, q_d_constant)) |> ignore
  meval(list3(list1(q_d_declare), q_d_kdelta, q_d_constant)) |> ignore
  meval(list3(list1(q_d_declare), q_p_levi_civita, q_d_constant)) |> ignore
  meval(list3(list1(q_d_declare), q_d_levi_civita, q_d_constant)) |> ignore
  set(q_d_dim, Fix(4L)) |> ignore
  set(q_d_contractions, share_itensor__empty_ml()) |> ignore
  // (deff $tenpr #'rpobj)
  defun(q_d_tenpr, args => rpobj(arg(args, 0)))
  // Christoffels contains all Christoffel-like symbols: i.e., symbols that
  // make sense only with certain index patterns. These symbols are excluded
  // from contractions, because those would produce illegal index
  // combinations (e.g., ichr1([a,b],[c])). However, special rules exist to
  // convert a covariant symbol into a mixed symbol and vice versa; for
  // instance, g^ad*ichr1_bcd will contract to ichr2_bc^a.
  set(
    q_christoffels1,
    list([
      q_d_ichr1, q_p_ichr1, q_d_icc1, q_p_icc1, q_d_ifc1, q_p_ifc1, q_d_inmc1, q_p_inmc1,
      q_d_ikt1, q_p_ikt1,
    ]),
  )
  |> ignore
  set(
    q_christoffels2,
    list([
      q_d_ichr2, q_p_ichr2, q_d_icc2, q_p_icc2, q_d_ifc2, q_p_ifc2, q_d_inmc2, q_p_inmc2,
      q_d_ikt2, q_p_ikt2,
    ]),
  )
  |> ignore
  set(
    q_christoffels,
    append_n([
      symval(q_christoffels1),
      symval(q_christoffels2),
      list([q_p_ifb, q_d_ifb, q_p_itr, q_d_itr]),
    ]),
  )
  |> ignore
  // $lc_l and $lc_u are rules (they return (values ans rule-hit))
  matcom__fset_mv(q_d_lc_l, args => d_lc_l(arg(args, 0)))
  matcom__fset_mv(q_d_lc_u, args => d_lc_u(arg(args, 0)))
  add2lnc(q_d_lc_l, symval(q_d_rules)) |> ignore
  add2lnc(q_d_lc_u, symval(q_d_rules)) |> ignore
  set(q_d_flipflag, Nil) |> ignore
  set(
    q_empty,
    list3(
      list2(q_mlist, q_simp),
      list1(list2(q_mlist, q_simp)),
      list1(list2(q_mlist, q_simp)),
    ),
  )
  |> ignore
  // The redefinitions of DERIV, SDIFF and I-$DEPENDENCIES replace the
  // comm.lisp functions for every caller, as loading the Lisp file does.
  comm__deriv_hook.val = Some(share_itensor__deriv)
  comm__sdiff_hook.val = Some(share_itensor__sdiff)
  comm__dependencies_hook.val = Some(share_itensor__i_dependencies)
  d_load(q_d_ex_calc) |> ignore
  d_load(q_d_lckdt) |> ignore
  d_load(q_d_iframe) |> ignore
  d_load(q_d_isimplify) |> ignore
}
