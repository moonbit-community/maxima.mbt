// Port of share/to_poly_solve/to_poly_solve_extra.lisp (Barton Willis,
// 2008): the non-short-circuited boolean operators %and and %or, %union,
// %if, %integerp, isnonnegative_p and subst_parallel.

///|
fn d_simp_inequality(e : Value) -> Value raise {
  let ee = standardize_inequality(e)
  if eq(ee, t) || ee is Nil {
    ee
  } else {
    e
  }
}

///|
/// Flatten and simplify each argument of the n-ary OP form E; arguments
/// standardized to true / false by standardize-inequality are replaced
/// (when STD).
fn share_to_poly_solve_extra__flatten(
  e : Value,
  z : Value,
  op : Value,
  std : Bool,
) -> Value raise {
  let mut acc : Value = Nil
  for ek0 in margs(e).iter() {
    let mut ek = simplifya(specrepcheck(ek0), z)
    if std {
      let b = standardize_inequality(ek)
      ek = if eq(b, t) || b is Nil { b } else { ek }
    }
    if op_equalp(ek, list1(op)).truthy() {
      acc = append(acc, margs(ek))
    } else {
      acc = cons(ek, acc)
    }
  }
  acc
}

///|
/// The set of the negations of the members of the set E.
fn share_to_poly_solve_extra__negations(e : Value) -> Value raise {
  opapply(q_d_set, mapcar(s => take(list1(q_mnot), [s]), margs(e)))
}

///|
fn simp__pctand(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  // flatten and simplify each argument
  let acc = share_to_poly_solve_extra__flatten(e, z, q_p_and, true)
  // setify and remove true
  let e = d_disjoin(t, opapply(q_d_set, acc))
  // logically negate each member of e
  let not_e = share_to_poly_solve_extra__negations(e)
  // simplifications:
  //  (1) if intersect(e, not(e)) # empty, return false,
  //  (2) if false in e, return false,
  //  (3) if e is empty, return true,
  //  (4) if e is a singleton set, return x.
  if !d_emptyp(d_intersection(e, list1(not_e))).truthy() {
    Nil
  } else if d_elementp(Nil, e).truthy() {
    Nil
  } else if d_emptyp(e).truthy() {
    t
  } else if cddr(e) is Nil {
    cadr(e)
  } else {
    cons(list2(q_p_and, q_simp), margs(e))
  }
}

///|
fn d_disjunction_p(e : Value) -> Value raise {
  op_equalp(e, list1(q_p_or))
}

///|
fn d_conjunction_p(e : Value) -> Value raise {
  op_equalp(e, list1(q_p_and))
}

///|
fn simp__pctor(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  // flatten and simplify each argument
  let acc = share_to_poly_solve_extra__flatten(e, z, q_p_or, true)
  // setify and remove false
  let e = d_disjoin(Nil, opapply(q_d_set, acc))
  // logically negate each member of e
  let not_e = share_to_poly_solve_extra__negations(e)
  // simplifications:
  //  (1) if intersect(e, not(e)) # empty, return true
  //  (2) if true e in e, return true,
  //  (3) if e is empty, return false,
  //  (4) if is a singleton set, return x.
  if !d_emptyp(d_intersection(e, list1(not_e))).truthy() {
    t
  } else if d_elementp(t, e).truthy() {
    t
  } else if d_emptyp(e).truthy() {
    Nil
  } else if cddr(e) is Nil {
    cadr(e)
  } else {
    cons(list2(q_p_or, q_simp), margs(e))
  }
}

///|
fn simp__pctunion(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  // flatten and simplify each argument
  let acc = share_to_poly_solve_extra__flatten(e, z, q_d__pctunion, false)
  // setify and remove $emptyset.
  let e = margs(d_disjoin(take(list1(q_d_set), []), opapply(q_d_set, acc)))
  cons(list2(q_d__pctunion, q_simp), e)
}

///|
fn simp__pctif(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let mut e = cdr(e) // remove ($%if simp)
  let b = bind(q_d_domain, q_d_complex)
  defer unbind(b)
  let mut cnd = if e is Nil {
    wna_err(q_d__pctif)
  } else {
    let x = car(e)
    e = cdr(e)
    simpcheck(x, z)
  }
  let mut a = if e is Nil {
    wna_err(q_d__pctif)
  } else {
    let x = car(e)
    e = cdr(e)
    x
  }
  let mut bb = if e is Nil {
    wna_err(q_d__pctif)
  } else {
    let x = car(e)
    e = cdr(e)
    x
  }
  if !(e is Nil) {
    wna_err(q_d__pctif) |> ignore
  }
  cnd = standardize_inequality(
    d_substitute(q_p_or, q_mor, expr=d_substitute(q_p_and, q_mand, expr=cnd)),
  )
  cnd = d_substitute(q_p_or, q_mor, expr=d_substitute(q_p_and, q_mand, expr=cnd))
  if eq(cnd, t) {
    simpcheck(a, z)
  } else if cnd is Nil {
    simpcheck(bb, z)
  } else {
    a = simpcheck(a, z)
    bb = simpcheck(bb, z)
    if like(a, bb).truthy() {
      a
    } else {
      list([list2(q_d__pctif, q_simp), cnd, a, bb])
    }
  }
}

///|
fn simp__pctintegerp(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  oneargcheck(e) |> ignore
  let e = simplifya(second(e), z)
  let sgn = d_compare(e, take(list1(q_d_floor), [e]))
  if equal(sgn, Str("=")) {
    t
  } else if equal(sgn, Str("<")) ||
    equal(sgn, Str(">")) ||
    equal(sgn, Str("#")) {
    Nil
  } else if symbolp(e) && d_featurep(e, q_d_noninteger).truthy() {
    Nil
  } else {
    list2(list2(q_d__pctintegerp, q_simp), e)
  }
}

///|
fn simp_isnonnegative_p(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  oneargcheck(e) |> ignore
  let b = bind(q_d_domain, q_d_complex)
  defer unbind(b)
  let e = simplifya(specrepcheck(cadr(e)), z)
  let is_real = take(list1(q_d_isreal_p), [e])
  if eq(t, is_real) {
    let sgn = csign(e)
    if memq(sgn, list([q_d_zero, q_d_pz, q_d_pos])).truthy() {
      t
    } else if eq(sgn, q_d_neg) {
      Nil
    } else {
      list2(list2(q_d_isnonnegative_p, q_simp), e)
    }
  } else if is_real is Nil {
    Nil
  } else {
    list2(list2(q_d_isnonnegative_p, q_simp), e)
  }
}

///|
/// (sublis alist tree :test #'alike), as SBCL implements it: the test is
/// called with the subtree first and the key second.
fn share_to_poly_solve_extra__sublis(alist : Value, tree : Value) -> Value raise {
  for pair in alist.iter() {
    if alike(tree, car(pair)).truthy() {
      return cdr(pair)
    }
  }
  match tree {
    Cons({ car: a, cdr: d }) => {
      let a1 = share_to_poly_solve_extra__sublis(alist, a)
      let d1 = share_to_poly_solve_extra__sublis(alist, d)
      if physical_equal_value(a1, a) && physical_equal_value(d1, d) {
        tree
      } else {
        cons(a1, d1)
      }
    }
    _ => tree
  }
}

///|
/// Similar to sublis, but allow for substitutions of nonatoms.
fn d_subst_parallel(l : Value, e : Value) -> Value raise {
  let mut alist : Value = Nil
  let is_a_rat = d_ratp(e)
  let l = if d_listp(l).truthy() { margs(l) } else { list1(l) }
  // Build an association list for the Common Lisp sublis function.
  for lk in l.iter() {
    if mequalp(lk).truthy() {
      let mut old = cadr(lk)
      let new_ = caddr(lk)
      old = if stringp(old) { amperchk(old) } else { old }
      alist = cons(cons(old, new_), alist)
    } else {
      merr("Each substitution must be an equation; found ~M", [lk]) |> ignore
    }
  }
  let e = resimplify(share_to_poly_solve_extra__sublis(alist, d_ratdisrep(e)))
  if is_a_rat.truthy() {
    d_rat(e, Nil)
  } else {
    e
  }
}

///|
fn init_share_to_poly_solve_extra() -> Unit raise {
  d_load(Str("fourier_elim")) |> ignore
  // non-short-circuited boolean operators and or.
  mfuncall(q_d_nary, list1(Str("%and"))) |> ignore
  putprop(q_p_and, share_to_poly_solve_extra__q_wxxml_nary, q_wxxml) |> ignore
  putprop(q_p_and, Str("<mspace/><fnm> %and </fnm><mspace/>"), share_to_poly_solve_extra__q_wxxmlsym)
  |> ignore
  putprop(q_p_and, Str("<fnm> %and </fnm>"), share_to_poly_solve_extra__q_wxxmlword) |> ignore
  putprop(q_p_and, Fix(120L), share_to_poly_solve_extra__q_wxxml_lbp) |> ignore
  putprop(q_p_and, Fix(120L), share_to_poly_solve_extra__q_wxxml_rbp) |> ignore
  displa_def(q_p_and, q_dimension_nary, list1(Str(" %and "))) |> ignore
  setf_get(q_p_and, q_grind, q_msize_nary) |> ignore
  putprop(q_p_and, q_tex_nary, q_tex) |> ignore
  putprop(q_p_and, list1(Str(" \\land ")), q_texsym) |> ignore
  setf_get(q_d__pctand, q_operators, q_simp__pctand) |> ignore
  setf_get(q_p_and, q_operators, q_simp__pctand) |> ignore
  // make op(a %and b) --> "%and" This allows things like if op(e) = "%and"
  // to work. With this disjunction_p and conjuction_p aren't needed.
  putprop(q_p_and, Str("%and"), q_op) |> ignore
  putprop(q_p_or, Str("%or"), q_op) |> ignore
  // Efficiency hack (see nset.lisp) -- this tells xreduce that %and is nary.
  def_nary(
    q_d__pctand,
    Nil,
    lfunc("nary-%and", args => simplify(cons(list1(q_p_and), arg(args, 0)))),
    t,
  )
  |> ignore
  mfuncall(q_d_nary, list1(Str("%or"))) |> ignore
  putprop(q_p_or, share_to_poly_solve_extra__q_wxxml_nary, q_wxxml) |> ignore
  putprop(q_p_or, Str("<mspace/><fnm> %or </fnm><mspace/>"), share_to_poly_solve_extra__q_wxxmlsym)
  |> ignore
  putprop(q_p_or, Str("<fnm> %or </fnm>"), share_to_poly_solve_extra__q_wxxmlword) |> ignore
  putprop(q_p_or, Fix(120L), share_to_poly_solve_extra__q_wxxml_lbp) |> ignore
  putprop(q_p_or, Fix(120L), share_to_poly_solve_extra__q_wxxml_rbp) |> ignore
  putprop(q_p_or, q_tex_nary, q_tex) |> ignore
  putprop(q_p_or, list1(Str(" \\lor ")), q_texsym) |> ignore
  displa_def(q_p_or, q_dimension_nary, list1(Str(" %or "))) |> ignore
  setf_get(q_p_or, q_grind, q_msize_nary) |> ignore
  setf_get(q_d__pctor, q_operators, q_simp__pctor) |> ignore
  setf_get(q_p_or, q_operators, q_simp__pctor) |> ignore
  // Efficiency hack (see nset.lisp) -- this tells xreduce that %or is nary.
  def_nary(
    q_d__pctor,
    Nil,
    lfunc("nary-%or", args => simplify(cons(list1(q_p_or), arg(args, 0)))),
    Nil,
  )
  |> ignore
  setf_get(q_d__pctunion, q_operators, q_simp__pctunion) |> ignore
  // TeX support
  putprop(q_d__pctunion, q_tex_nary, q_tex) |> ignore
  putprop(q_d__pctunion, list1(Str(" \\cup ")), q_texsym) |> ignore
  setf_get(q_d__pctif, q_operators, q_simp__pctif) |> ignore
  setf_get(q_d__pctintegerp, q_operators, q_simp__pctintegerp) |> ignore
  setf_get(q_d_isnonnegative_p, q_operators, q_simp_isnonnegative_p) |> ignore
}

///|
let share_to_poly_solve_extra__q_wxxml_lbp : Value = sym("wxxml-lbp")

///|
let share_to_poly_solve_extra__q_wxxml_nary : Value = sym("wxxml-nary")

///|
let share_to_poly_solve_extra__q_wxxml_rbp : Value = sym("wxxml-rbp")

///|
let share_to_poly_solve_extra__q_wxxmlsym : Value = sym("wxxmlsym")

///|
let share_to_poly_solve_extra__q_wxxmlword : Value = sym("wxxmlword")
