// Port of share/to_poly_solve/to_poly.lisp (Barton Willis, 2006-2022):
// to_poly, elim, elim_allbut, eliminate_using, parg, isreal_p,
// new_variable, nicedummies.

///|
/// The symbol S, the parameter of the lambda forms passed to
/// $polynomialp.
let share_to_poly__q_s : Value = sym("s")

///|
/// macro (opapply op args): `(simplify (cons (list ,op) ,args))
fn opapply(op : Value, args : Value) -> Value raise {
  simplify(cons(list1(op), args))
}

///|
/// The next three functions convert max and min to abs functions.
fn max_to_abs(e : Value) -> Value raise {
  reduce(
    (a, b) => div(
      add2(add2(a, b), take(list1(q_mabs), [sub(a, b)])),
      Fix(2L),
    ),
    e,
  )
}

///|
fn min_to_abs(e : Value) -> Value raise {
  reduce(
    (a, b) => div(sub(add2(a, b), take(list1(q_mabs), [sub(a, b)])), Fix(2L)),
    e,
  )
}

///|
fn convert_from_max_min_to_abs(e : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    e
  } else if op_equalp(e, list1(q_d_max)).truthy() {
    max_to_abs(mapcar(x => convert_from_max_min_to_abs(x), margs(e)))
  } else if op_equalp(e, list1(q_d_min)).truthy() {
    min_to_abs(mapcar(x => convert_from_max_min_to_abs(x), margs(e)))
  } else {
    opapply(mop(e), mapcar(x => convert_from_max_min_to_abs(x), margs(e)))
  }
}

///|
fn maxima_variable_p(e : Value) -> Value raise {
  if symbolp(e) {
    t
  } else {
    d_subvarp(e)
  }
}

///|
fn list_subst(l : Value, p : Value) -> Value raise {
  if l is Nil {
    p
  } else {
    list_subst(rest(l), d_substitute(first(l), p))
  }
}

///|
/// to_poly(p,vars) returns a polynomial in the variables 'vars' that has a
/// zero whenever p has a zero. When 1 is a member of vars, constant terms,
/// such as sqrt(5) also get converted to polynomial form. The value of
/// vars defaults to all variables including constants.
fn d_to_poly(p : Value, vars? : Value = q_convert_all_vars) -> Value raise {
  with_special(q_d_listconstvars, t, () => {
    let mut p = p
    let mut vars = vars
    let mut convert_cnst : Value = Nil
    if eq(vars, q_convert_all_vars) {
      vars = d_cons(Fix(1L), d_listofvars(p))
    }
    if !d_listp(vars).truthy() {
      merror(Str("The second argument to 'to_poly' must be a list"), Nil)
      |> ignore
    }
    if d_member(Fix(1L), vars).truthy() {
      convert_cnst = t
      vars = d_delete(Fix(1L), vars)
    }
    // If p is a list or a set, set p to the members in p; otherwise (list p)
    p = if d_listp(p).truthy() || d_setp(p).truthy() {
      margs(p)
    } else {
      list1(p)
    }
    // Convert each member of p that is an equation to a nonequation.
    // Thus transform a = b into a - b.
    p = mapcar(x => meqhk(x), p)
    // Extract the denominators of p and require them to not vanish.
    // Replace the list p by a list of the numerators.
    let q = mapcar(x => d_ratdenom(x), p)
    p = mapcar(x => d_ratnumer(x), p)
    let mut proviso = delete(t, mapcar(s => mnqp(s, Fix(0L)), q))
    proviso = mapcar(s => maxima_substitute(q_mnotequal, q_d_notequal, s), proviso)
    p = mapcar(x => sratsimp(x), p)
    p = non_algebraic_subst_list(p, vars).0
    let non_alg = funcall(q_d_second, [p])
    p = margs(d_first(p))
    // It's OK to send every expression through convert-from-max-min-to-abs.
    // The conditional skips the ratsimp for expressions that don't involve
    // max or min.
    let mut pp : Value = Nil
    let mut subs : Value = Nil
    for pk in p.iter() {
      let mut pk = if d_freeof(list3(q_d_max, q_d_min, pk)).truthy() {
        pk
      } else {
        sratsimp(convert_from_max_min_to_abs(pk))
      }
      pk = to_polynomial(pk, vars, convert_cnst)
      // After conversion, the members of pp can be rational expressions,
      // not polynomials. This happens, for example, when there is a
      // 2 cos(x) --> exp(%i x) + 1/exp(%i x) conversion. So we need to
      // extract numerators of the members of p.
      proviso = append(proviso, mapcar(x => sratsimp(x), third(pk)))
      subs = append(subs, mapcar(x => sratsimp(x), second(pk)))
      pk = sratsimp(first(pk))
      let qk = sratsimp(d_ratdenom(pk))
      if !eq(t, mnqp(qk, Fix(0L))) {
        proviso = cons(take(list1(q_mnotequal), [qk, Fix(0L)]), proviso)
      }
      pk = sratsimp(d_ratnumer(pk))
      pp = cons(pk, pp)
    }
    pp = append(pp, subs)
    pp = cons(list1(q_mlist), pp)
    proviso = cons(list1(q_mlist), proviso)
    list([list1(q_mlist), pp, proviso, non_alg])
  })
}

///|
fn to_polynomial(p : Value, vars : Value, convert_cnst : Value) -> Value raise {
  let mut p = p
  let mut vars = vars
  let mut subs : Value = Nil
  let mut inequal : Value = Nil
  let mut np_subs : Value = Nil
  if maxima_variable_p(p).truthy() ||
    mnump(p).truthy() ||
    (d_emptyp(vars).truthy() && !convert_cnst.truthy()) ||
    (!d_constantp(p).truthy() && d_lfreeof(vars, p).truthy()) ||
    (d_constantp(p).truthy() && !convert_cnst.truthy()) ||
    (
      op_equalp(p, list1(q_d_conjugate)).truthy() &&
      maxima_variable_p(second(p)).truthy()
    ) {
    list([p, Nil, Nil, Nil])
  } else if mexptp(p).truthy() {
    let mut n = nth(2, p)
    let mut b = nth(1, p)
    if integerp(n) && num_gt(n, Fix(0L)) {
      list([p, Nil, Nil, Nil])
    } else if d_ratnump(n).truthy() {
      b = to_polynomial(b, vars, convert_cnst)
      subs = second(b)
      inequal = third(b)
      np_subs = fourth(b)
      b = first(b)
      let nv = new_gentemp(q_general)
      if mgrp(n, Fix(0L)).truthy() || mnump(b).truthy() {
        subs = cons(
          ftake(q_mequal, [b, ftake(q_mexpt, [nv, d_denom(n)])]),
          subs,
        )
        let ph = ftake(q_d_parg, [nv])
        let angle = div(q_d__pctpi, d_denom(n))
        inequal = cons(ftake(q_mlessp, [neg(angle), ph]), inequal)
        inequal = cons(ftake(q_mleqp, [ph, angle]), inequal)
        np_subs = cons(ftake(q_mequal, [p, ftake(q_mexpt, [nv, d_num(n)])]), np_subs)
        list([ftake(q_mexpt, [nv, d_num(n)]), subs, inequal, np_subs])
      } else {
        n = neg(n)
        subs = cons(
          take(list1(q_mequal), [
            Fix(1L),
            mul2(power(nv, d_denom(n)), power(b, d_num(n))),
          ]),
          subs,
        )
        inequal = cons(
          take(list1(q_mlessp), [
            take(list1(q_d_parg), [nv]),
            mul2(n, q_d__pctpi),
          ]),
          inequal,
        )
        inequal = cons(
          take(list1(q_mleqp), [
            muln_([Fix(-1L), q_d__pctpi, n]),
            take(list1(q_d_parg), [nv]),
          ]),
          inequal,
        )
        inequal = cons(take(list1(q_mnotequal), [nv, Fix(0L)]), inequal)
        list([nv, subs, inequal, np_subs])
      }
    } else {
      merror(Str("Nonalgebraic argument given to 'to_poly'"), Nil)
    }
  } else if op_equalp(p, list1(q_mabs)).truthy() {
    let mut b = to_polynomial(first(margs(p)), vars, convert_cnst)
    let acc = second(b)
    inequal = third(b)
    np_subs = fourth(b)
    b = first(b)
    let nv = new_gentemp(q_d_general)
    inequal = cons(take(list1(q_d_isnonnegative_p), [nv]), inequal)
    list([
      nv,
      cons(
        take(list1(q_mequal), [
          mul2(b, take(list1(q_d_conjugate), [b])),
          mul2(nv, take(list1(q_d_conjugate), [nv])),
        ]),
        acc,
      ),
      inequal,
      np_subs,
    ])
  } else if mtimesp(p).truthy() {
    let mut acc : Value = Fix(1L)
    p = margs(p)
    while p.truthy() {
      let pk = first(p)
      p = rest(p)
      let q = to_polynomial(pk, vars, convert_cnst)
      acc = mul2(acc, first(q))
      subs = append(second(q), subs)
      inequal = append(inequal, third(q))
      np_subs = append(np_subs, fourth(q))
      vars = d_append(list2(vars, d_listofvars(cons(list1(q_mlist), subs))))
      let nps = np_subs
      p = mapcar(s => list_subst(nps, s), p)
    }
    list([acc, subs, inequal, np_subs])
  } else if mplusp(p).truthy() {
    let mut acc : Value = Fix(0L)
    p = margs(p)
    while p.truthy() {
      let pk = first(p)
      p = rest(p)
      let q = to_polynomial(pk, vars, convert_cnst)
      acc = add2(acc, first(q))
      subs = append(second(q), subs)
      inequal = append(third(q), inequal)
      np_subs = append(fourth(q), np_subs)
      vars = d_append(list2(vars, d_listofvars(cons(list1(q_mlist), subs))))
      let nps = np_subs
      p = mapcar(s => list_subst(nps, s), p)
    }
    list([acc, subs, inequal, np_subs])
  } else {
    merror(Str("Nonalgebraic argument given to 'to_poly'"), Nil)
  }
}

///|
fn require_maxima_variable(x : Value, context_string : Value) -> Value raise {
  let x = ratdisrep(x)
  if maxima_variable_p(x).truthy() {
    x
  } else {
    merror(
      Str("Function ~:M expects a symbol, instead found ~:M"),
      list2(context_string, x),
    )
  }
}

///|
/// Simplify a polynomial equation p = 0 by
///   (1) nonzero constant * p --> p,
///   (2) p^n --> p.
fn suppress_multiple_zeros(q : Value) -> Value raise {
  let q = d_sqfr(q)
  if mnump(q).truthy() {
    if zerop1(q).truthy() {
      Fix(0L)
    } else {
      Fix(1L)
    }
  } else if mtimesp(q).truthy() {
    muln(mapcar(x => suppress_multiple_zeros(x), margs(q)), t)
  } else if mexptp(q).truthy() && integerp(third(q)) && plusp(third(q)) {
    second(q)
  } else if d_constantp(q).truthy() {
    // takes care of things like (1 + sqrt(5)) * x --> x.
    Fix(1L)
  } else {
    q
  }
}

///|
/// `((lambda) ((mlist) s) ((,fn) ,x s))
fn share_to_poly__coeffp(fn_ : Value, x : Value) -> Value {
  list3(
    list1(q_lambda),
    list2(list1(q_mlist), share_to_poly__q_s),
    list3(list1(fn_), x, share_to_poly__q_s),
  )
}

///|
/// Using eq as the "pivot," eliminate x from the list or set of equations
/// eqs.
fn d_eliminate_using(eqs : Value, eq_ : Value, x : Value) -> Value raise {
  let mut eqs = eqs
  let mut eq_ = eq_
  if d_listp(eqs).truthy() || d_setp(eqs).truthy() {
    eqs = mapcar(s => d_ratexpand(meqhk(s)), margs(eqs))
    eqs = margs(opapply(q_d_set, eqs))
  } else {
    merror(
      Str("The first argument to 'eliminate_using' must be a list or a set"),
      Nil,
    )
    |> ignore
  }
  let x = require_maxima_variable(x, Str("$eliminate_using"))
  if !eqs
    .iter()
    .all(s => d_polynomialp(
        s,
        list2(list1(q_mlist), x),
        coeffp=share_to_poly__coeffp(q_d_freeof, x),
      ).truthy()) {
    merror(
      Str(
        "The first argument to 'eliminate_using' must be a set or list of polynomials",
      ),
      Nil,
    )
    |> ignore
  }
  eq_ = d_ratexpand(meqhk(eq_))
  if !d_polynomialp(
      eq_,
      list2(list1(q_mlist), x),
      coeffp=share_to_poly__coeffp(q_d_freeof, x),
    ).truthy() {
    merror(
      Str("The second argument to 'eliminate_using' must be a polynomial"),
      Nil,
    )
    |> ignore
  }
  eqs = mapcar(x => suppress_multiple_zeros(x), eqs)
  eq_ = suppress_multiple_zeros(eq_)
  opapply(q_d_set, eliminate_using(eqs, eq_, x))
}

///|
fn eliminate_using(eqs : Value, eq_ : Value, x : Value) -> Value raise {
  delete(
    Fix(0L),
    mapcar(s => suppress_multiple_zeros(d_resultant(s, eq_, x)), eqs),
  )
}

///|
/// Return an upper bound for the total degree of the polynomial p in the
/// variables vars. When p is fully expanded, the bound is exact.
fn degree_upper_bound(p : Value, vars : Value) -> Value raise {
  if maxima_variable_p(p).truthy() {
    if member_equal(p, vars).truthy() {
      Fix(1L)
    } else {
      Fix(0L)
    }
  } else if mnump(p).truthy() {
    Fix(0L)
  } else if mexptp(p).truthy() && integerp(third(p)) && plusp(third(p)) {
    num_mul(degree_upper_bound(nth(1, p), vars), nth(2, p))
  } else if mtimesp(p).truthy() {
    reduce(
      (a, b) => num_add(a, b),
      mapcar(s => degree_upper_bound(s, vars), margs(p)),
      initial=Fix(0L),
    )
  } else if mplusp(p).truthy() {
    simplify(
      cons(list1(q_d_max), mapcar(s => degree_upper_bound(s, vars), margs(p))),
    )
  } else if d_freeof(append(vars, list1(p))).truthy() {
    Fix(0L)
  } else {
    merror(Str("Nonpolynomial argument given to degree-upper-bound"), Nil)
  }
}

///|
fn unk_eliminate(eqs : Value, vars : Value, pivots? : Value = Nil) -> Value raise {
  with_special(q_d_ratfac, Nil, () => {
    let mut n_min : Value = Nil
    let mut xeqs = list1(list1(q_d_set))
    let mut pivot_var : Value = Nil
    let mut pivot_eq : Value = Nil
    let mut acc = list1(list1(q_d_set))
    if vars is Nil || eqs is Nil {
      return list2(eqs, pivots)
    }
    // The pivot is a nonconstant member of eqs with minimal total degree.
    // The constant members of eqs get adjoined into acc -- all other
    // members get adjoined into xeqs. Since each member of eqs has been
    // ratexpanded, the degree bound is exact.
    for ei in eqs.iter() {
      let ei = d_ratexpand(suppress_multiple_zeros(ei))
      let ni = degree_upper_bound(ei, vars)
      if (n_min is Nil || num_lt(ni, n_min)) && num_gt(ni, Fix(0L)) {
        n_min = ni
        pivot_eq = ei
      }
      if num_gt(ni, Fix(0L)) && !equal(Fix(0L), ei) {
        xeqs = d_adjoin(ei, xeqs)
      } else {
        acc = d_adjoin(ei, acc)
      }
    }
    xeqs = margs(xeqs)
    acc = margs(acc)
    // Now we'll decide which variable to eliminate. The pivot variable
    // is the variable that has the least (but nonzero) degree in pivot-eq.
    n_min = Nil
    for vi in vars.iter() {
      let ni = degree_upper_bound(pivot_eq, list1(vi))
      if (n_min is Nil || num_lt(ni, n_min)) && num_gt(ni, Fix(0L)) {
        pivot_var = vi
        n_min = ni
      }
    }
    if pivot_var is Nil {
      list2(eqs, pivots)
    } else {
      unk_eliminate(
        append(acc, eliminate_using(xeqs, pivot_eq, pivot_var)),
        delete(pivot_var, vars),
        pivots=cons(pivot_eq, pivots),
      )
    }
  })
}

///|
fn d_elim(eqs : Value, x : Value) -> Value raise {
  let mut eqs = eqs
  let mut x = x
  if d_listp(eqs).truthy() || d_setp(eqs).truthy() {
    eqs = mapcar(s => d_ratexpand(suppress_multiple_zeros(meqhk(s))), margs(eqs))
    eqs = margs(opapply(q_d_set, eqs))
  } else {
    merror(Str("The first argument to 'elim' must be a list or a set"), Nil)
    |> ignore
  }
  x = margs(
    if d_listp(x).truthy() {
      d_setify(x)
    } else if d_setp(x).truthy() {
      x
    } else {
      merror(Str("The second argument to 'elim' must be a list or a set"), Nil)
    },
  )
  x = mapcar(s => require_maxima_variable(s, Str("$elim")), x)
  x = opapply(q_mlist, x)
  let xx = x
  if !eqs
    .iter()
    .all(s => d_polynomialp(s, xx, coeffp=share_to_poly__coeffp(q_d_lfreeof, xx)).truthy()) {
    merror(
      Str("Each member of the first argument to 'elim' must be a polynomial"),
      Nil,
    )
    |> ignore
  }
  x = margs(x)
  opapply(q_mlist, mapcar(s => opapply(q_mlist, s), unk_eliminate(eqs, x)))
}

///|
fn d_elim_allbut(eqs : Value, x : Value) -> Value raise {
  with_special(q_d_listconstvars, Nil, () => {
    let mut v = d_listofvars(eqs)
    let x = if d_listp(x).truthy() {
      d_setify(x)
    } else if d_setp(x).truthy() {
      x
    } else {
      take(list1(q_d_set), [x])
    }
    v = d_setdifference(d_setify(v), x)
    d_elim(eqs, d_listify(v))
  })
}

///|
/// Return a list of the arguments to the operator op in the expression e.
/// This function only looks inside + and * and it doesn't recurse inside
/// + and *. So
///
///  gather-args(log(x) + log(a + log(b)), log) --> (x, a + log(b)),
///  gather-args(cos(log(x)), log) --> (),
///  gather-args(x^log(x) + log(s)^x, log) --> ().
fn gather_args(e : Value, op : Value, vars : Value) -> Value raise {
  if consp(e) && consp(car(e)) && eq(caar(e), q_mlist) {
    let mut acc : Value = Nil
    for l in mapcar(s => gather_args(s, op, vars), margs(e)).iter() {
      acc = append(acc, l)
    }
    acc
  } else if d_mapatom(e).truthy() {
    Nil
  } else if eq(mop(e), op) && !d_lfreeof(vars, e).truthy() {
    margs(e)
  } else if memq(mop(e), list2(q_mplus, q_mtimes)).truthy() {
    let mut acc : Value = Nil
    for ek in margs(e).iter() {
      acc = append(acc, gather_args(ek, op, vars))
    }
    acc
  } else {
    Nil
  }
}

///|
fn gather_nonrational_powers(e : Value, vars : Value) -> Value raise {
  if consp(e) && consp(car(e)) && eq(caar(e), q_mlist) {
    let mut acc : Value = Nil
    for l in mapcar(s => gather_nonrational_powers(s, vars), margs(e)).iter() {
      acc = append(acc, l)
    }
    acc
  } else if d_mapatom(e).truthy() {
    Nil
  } else if eq(mop(e), q_mexpt) &&
    memq(second(e), vars).truthy() &&
    !d_ratnump(third(e)).truthy() {
    list1(e)
  } else if memq(mop(e), list2(q_mplus, q_mtimes)).truthy() {
    mapcan(s => gather_nonrational_powers(s, vars), margs(e))
  } else {
    Nil
  }
}

///|
fn gather_exp_args(e : Value, vars : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    Nil
  } else if eq(mop(e), q_mexpt) {
    if eq(second(e), q_d__pcte) && !d_lfreeof(vars, third(e)).truthy() {
      list1(third(e))
    } else {
      gather_exp_args(second(e), vars)
    }
  } else {
    mapcan(s => gather_exp_args(s, vars), margs(e))
  }
}

///|
/// Return true iff the set {a,b} is linearly dependent. Thus return true
/// iff either a = 0 or b = 0, or a/b is a number.
fn d_linearly_dependent_p(a : Value, b : Value) -> Value raise {
  linearly_dependent_p(a, b)
}

///|
fn linearly_dependent_p(a : Value, b : Value) -> Value raise {
  if eq0(a) || eq0(b) || mnump(sratsimp(div(a, b))).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn exponentialize_if(e : Value, vars : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    e
  } else if trigp(mop(e)).truthy() && !d_lfreeof(vars, e).truthy() {
    d_exponentialize(e)
  } else {
    opapply(mop(e), mapcar(s => exponentialize_if(s, vars), margs(e)))
  }
}

///|
fn logarc_if(e : Value, vars : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    e
  } else if arcp(mop(e)).truthy() && !d_lfreeof(vars, e).truthy() {
    d_logarc(e)
  } else {
    opapply(mop(e), mapcar(s => logarc_if(s, vars), margs(e)))
  }
}

///|
/// The common part of NON-ALGEBRAIC-SUBST and NON-ALGEBRAIC-SUBST-LIST:
/// `e` has been ratexpanded (and is a Maxima list for the list version).
fn share_to_poly__non_algebraic_subst(
  e : Value,
  vars : Value,
) -> (Value, Value) raise {
  let mut e = e
  let mut na_subs : Value = Nil
  let mut g_vars : Value = Nil
  let log_args = margs(opapply(q_d_set, gather_args(e, q_p_log, vars)))
  let exp_args = opapply(q_d_set, gather_exp_args(e, vars))
  let s = margs(simplify(d_equiv_classes(exp_args, q_linearly_dependent_p)))
  for sk in s.iter() {
    let g = new_gentemp(q_d_general)
    g_vars = cons(g, g_vars)
    let sz = d_first(d_ezgcd(margs(sk)))
    let p = power(q_d__pcte, sz)
    na_subs = cons(take(list1(q_mequal), [g, p]), na_subs)
    for sl in margs(sk).iter() {
      let q = sratsimp(div(sl, sz))
      e = d_ratexpand(d_substitute(power(g, q), power(q_d__pcte, sl), expr=e))
    }
  }
  for sk in log_args.iter() {
    let g = new_gentemp(q_d_general)
    g_vars = cons(g, g_vars)
    let p = take(list1(q_p_log), [sk])
    e = d_substitute(g, p, expr=e)
    na_subs = cons(take(list1(q_mequal), [g, p]), na_subs)
  }
  // Attempt the substitution %g = x^a, where x is in vars and a is not a
  // rational number. Accept the substitution if it eliminates x from e and
  // it changes e, otherwise reject it.
  let mexpt_args = gather_nonrational_powers(e, margs(vars))
  for sk in mexpt_args.iter() {
    let g = new_gentemp(q_d_general)
    let ee = d_ratsubst(g, sk, e)
    if freeof(second(sk), ee).truthy() && !like(e, ee).truthy() {
      g_vars = cons(g, g_vars)
      e = ee
      na_subs = cons(take(list1(q_mequal), [g, sk]), na_subs)
    }
  }
  (list3(list1(q_mlist), e, cons(list1(q_mlist), na_subs)), g_vars)
}

///|
fn non_algebraic_subst(e : Value, vars : Value) -> (Value, Value) raise {
  let e = d_ratexpand(exponentialize_if(logarc_if(e, vars), vars))
  share_to_poly__non_algebraic_subst(e, vars)
}

///|
fn non_algebraic_subst_list(l : Value, vars : Value) -> (Value, Value) raise {
  let l = mapcar(
    s => d_ratexpand(exponentialize_if(logarc_if(s, vars), vars)),
    l,
  )
  share_to_poly__non_algebraic_subst(cons(list1(q_mlist), l), vars)
}

///|
/// A simplifying carg function.
fn simp_parg(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  with_special(q_d_domain, q_d_complex, () => {
    oneargcheck(e) |> ignore
    let mut e = simplifya(specrepcheck(cadr(e)), z)
    e = sratsimp(d_exponentialize(e))
    let mut sgn : Value = Nil
    let mut isgn : Value = Nil
    if zerop1(e).truthy() {
      // parg(0) = 0,parg(0.0) = 0.0, parg(0.0b0) = 0.0b0.
      return e
    }
    // For a complex number, use atan2
    if complex_number_p(e, ntypep=q_d_constantp).truthy() {
      return ftake(q_p_atan2, [d_imagpart(e), d_realpart(e)])
    }
    // off the negative real axis, parg(conjugate(x)) = -parg(x)
    if op_equalp(e, list1(q_d_conjugate)).truthy() &&
      off_negative_real_axisp(e).truthy() {
      return neg(take(list1(q_d_parg), [cadr(e)]))
    }
    // parg(a * x) = parg(x) provided a > 0.
    if mtimesp(e).truthy() && eq(t, mgrp(cadr(e), Fix(0L))) {
      return take(list1(q_d_parg), [reduce((a, b) => mul2(a, b), cddr(e))])
    }
    // parg exp(a + %i*b) = %pi-mod(%pi-b,2*%pi)
    if mexptp(e).truthy() &&
      eq(q_d__pcte, second(e)) &&
      linearp(third(e), q_d__pcti).truthy() {
      return sub(
        q_d__pctpi,
        take(list1(q_d_mod), [
          sub(q_d__pctpi, d_imagpart(third(e))),
          mul2(Fix(2L), q_d__pctpi),
        ]),
      )
    }
    // parg(x^number) = number * parg(x), provided number in (-1,1).
    if mexptp(e).truthy() &&
      d_numberp(caddr(e)).truthy() &&
      eq(t, mgrp(caddr(e), Fix(-1L))) &&
      eq(t, mgrp(Fix(1L), caddr(e))) {
      return mul2(caddr(e), take(list1(q_d_parg), [cadr(e)]))
    }
    // sign rules parg(x) = %pi, x < 0 and parg(x) = 0, x > 0
    sgn = d_csign(e)
    if eq(q_d_neg, sgn) {
      return q_d__pctpi
    }
    if eq(q_d_pos, sgn) {
      return Fix(0L)
    }
    // more sign rules parg(%i * x) = %pi /2, x > 0 and -%pi / 2, x < 0.
    if eq(q_d_imaginary, sgn) {
      isgn = d_csign(div(e, q_d__pcti))
      if isgn.truthy() && eq(q_d_pos, isgn) {
        return div(q_d__pctpi, Fix(2L))
      }
    }
    if eq(q_d_imaginary, sgn) && eq(q_d_neg, isgn) {
      return div(q_d__pctpi, Fix(-2L))
    }
    // nounform return
    list2(list2(q_d_parg, q_simp), e)
  })
}

///|
fn simp_isreal_p(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  oneargcheck(e) |> ignore
  with_special(q_d_domain, q_d_complex, () => {
    let mut e = simplifya(specrepcheck(cadr(e)), z)
    // Simplifications:
    //  (1) if r is real then isreal_p(r + x) --> isreal_p(x),
    //  (2) if r is real then isreal_p(r * x) --> isreal_p(x),
    //  (3) if e = conjugate(e) then true,
    //  (4) if is(notequal(e,conjugate(e))) then false.
    if mtimesp(e).truthy() {
      e = muln(
        mapcar(
          s => if eq(t, take(list1(q_d_isreal_p), [s])) { Fix(1L) } else { s },
          margs(e),
        ),
        t,
      )
    } else if mplusp(e).truthy() {
      e = addn(
        mapcar(
          s => if eq(t, take(list1(q_d_isreal_p), [s])) { Fix(0L) } else { s },
          margs(e),
        ),
        t,
      )
    }
    // If e is constant, apply rectform.
    if d_constantp(e).truthy() {
      e = d_rectform(e)
    }
    let ec = take(list1(q_d_conjugate), [e])
    if eq(t, meqp(e, ec)) {
      t
    } else if eq(t, mnqp(e, ec)) {
      Nil
    } else {
      list2(list2(q_d_isreal_p, q_simp), e)
    }
  })
}

///|
/// Return a new gentemp with a prefix that is determined by 'type.'
fn d_new_variable(type_ : Value) -> Value raise {
  new_gentemp(type_)
}

///|
/// (intern (symbol-name (gensym prefix)) :maxima). The prefixes are CL
/// symbol names ("$%G"); the port name of the symbol is their case
/// inversion ("$%g...").
fn share_to_poly__gentemp(prefix : Value) -> Value raise {
  let p = match prefix {
    Str(s) => s
    _ => princ_to_string(prefix)
  }
  Sym(intern(invert_case(symbol_name(gensym(prefix=p)))))
}

///|
/// (symbolconc prefix k) with a CL-name prefix (see above).
fn share_to_poly__symbolconc(prefix : Value, k : Int64) -> Value raise {
  let p = match prefix {
    Str(s) => s
    _ => princ_to_string(prefix)
  }
  Sym(intern(invert_case(p + k.to_string())))
}

///|
/// Return a new gentemp with a prefix that is determined by 'type.' Also
/// put an identifying tag on the symbol property of each new gentemp.
fn new_gentemp(type_ : Value) -> Value raise {
  let g = if eq(type_, q_d_integer) {
    let g = share_to_poly__gentemp(symval(q_ear_integer_gentemp_prefix))
    setf_get(g, q_integer_gentemp, t) |> ignore
    d_declare(list3(list1(q_d_declare), g, q_d_integer)) |> ignore
    g
  } else if eq(type_, q_d_natural_number) {
    let g = share_to_poly__gentemp(symval(q_ear_natural_gentemp_prefix))
    setf_get(g, q_natural_gentemp, t) |> ignore
    d_declare(list3(list1(q_d_declare), g, q_d_integer)) |> ignore
    d_assume(list2(list1(q_d_assume), take(list1(q_mgeqp), [g, Fix(0L)])))
    |> ignore
    g
  } else if eq(type_, q_d_real) {
    let g = share_to_poly__gentemp(symval(q_ear_real_gentemp_prefix))
    setf_get(g, q_real_gentemp, t) |> ignore
    g
  } else if eq(type_, q_d_complex) {
    let g = share_to_poly__gentemp(symval(q_ear_complex_gentemp_prefix))
    setf_get(g, q_complex_gentemp, t) |> ignore
    d_declare(list3(list1(q_d_declare), g, q_d_complex)) |> ignore
    g
  } else {
    let g = share_to_poly__gentemp(symval(q_ear_general_gentemp_prefix))
    setf_get(g, q_general_gentemp, t) |> ignore
    g
  }
  g
}

///|
/// Find all the new-gentemp variables in an expression e and re-index
/// them starting from 0.
fn d_nicedummies(e : Value) -> Value raise {
  with_special(q_d_listconstvars, Nil, () => {
    let mut z_vars : Value = Nil
    let mut z_k = 0L
    let mut n_vars : Value = Nil
    let mut n_k = 0L
    let mut r_vars : Value = Nil
    let mut r_k = 0L
    let mut c_vars : Value = Nil
    let mut c_k = 0L
    let mut g_vars : Value = Nil
    let mut g_k = 0L
    for s in margs(d_sort(d_listofvars(e))).iter() {
      if d_subvarp(s).truthy() {
        ()
      } else if get(s, q_integer_gentemp).truthy() {
        let a = share_to_poly__symbolconc(symval(q_ear_integer_gentemp_prefix), z_k)
        d_declare(list3(list1(q_d_declare), a, q_d_integer)) |> ignore
        z_k = z_k + 1L
        z_vars = cons(list3(list1(q_mequal), s, a), z_vars)
      } else if get(s, q_natural_gentemp).truthy() {
        let a = share_to_poly__symbolconc(symval(q_ear_natural_gentemp_prefix), n_k)
        d_declare(list3(list1(q_d_declare), a, q_d_integer)) |> ignore
        d_assume(list2(list1(q_d_assume), take(list1(q_mgeqp), [a, Fix(0L)])))
        |> ignore
        n_k = n_k + 1L
        n_vars = cons(list3(list1(q_mequal), s, a), n_vars)
      } else if get(s, q_real_gentemp).truthy() {
        let a = share_to_poly__symbolconc(symval(q_ear_real_gentemp_prefix), r_k)
        r_k = r_k + 1L
        r_vars = cons(list3(list1(q_mequal), s, a), r_vars)
      } else if get(s, q_complex_gentemp).truthy() {
        let a = share_to_poly__symbolconc(symval(q_ear_complex_gentemp_prefix), c_k)
        d_declare(list3(list1(q_d_declare), a, q_d_complex)) |> ignore
        c_k = c_k + 1L
        c_vars = cons(list3(list1(q_mequal), s, a), c_vars)
      } else if get(s, q_general_gentemp).truthy() {
        let a = share_to_poly__symbolconc(symval(q_ear_general_gentemp_prefix), g_k)
        g_k = g_k + 1L
        g_vars = cons(list3(list1(q_mequal), s, a), g_vars)
      }
    }
    z_vars = cons(list1(q_mlist), z_vars)
    n_vars = cons(list1(q_mlist), n_vars)
    r_vars = cons(list1(q_mlist), r_vars)
    c_vars = cons(list1(q_mlist), c_vars)
    g_vars = cons(list1(q_mlist), g_vars)
    d_sublis(
      g_vars,
      d_sublis(c_vars, d_sublis(r_vars, d_sublis(n_vars, d_sublis(z_vars, e)))),
    )
  })
}

///|
fn d_complex_number_p(e : Value) -> Value raise {
  complex_number_p(e, ntypep=q_d_numberp)
}

///|
fn init_share_to_poly() -> Unit raise {
  d_put(q_d_to_poly, Fix(2L), q_d_version) |> ignore
  setf_get(q_d_parg, q_operators, q_simp_parg) |> ignore
  setf_get(q_d_isreal_p, q_operators, q_simp_isreal_p) |> ignore
}
