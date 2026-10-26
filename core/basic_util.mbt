// Port of src/basic-util.lisp: basic utilities used by many routines.

///|
fn recur_apply(fun : Value, e : Value) -> Value raise {
  if eq(caar(e), q_bigfloat) {
    e
  } else if specrepp(e).truthy() {
    funcall(fun, [specdisrep(e)])
  } else {
    let newargs = mapcar(a => funcall(fun, [a]), cdr(e))
    if alike(newargs, cdr(e)).truthy() {
      e
    } else {
      simplifya(cons(cons(caar(e), memq(q_array, cdar(e))), newargs), Nil)
    }
  }
}

///|
/// Replace y with x in z, but leave z's second arg unchanged.
/// This is for cases like at(integrate(x, x, a, b), [x=3])
/// where second arg of integrate binds a new variable x,
/// and we do not wish to subst 3 for x inside integrand.
fn subst_except_second_arg(x : Value, y : Value, z : Value) -> Value raise {
  let op = caar(z)
  if memq(op, list([q_p_integrate, q_p_sum, q_p_product, q_p_limit, q_p_laplace])).truthy() {
    append(
      list([
        remove(q_simp, car(z)), // ensure resimplification after substitution
        if eq(y, third(z)) {
          second(z)
        } else {
          subst1(x, y, second(z))
        },
        third(z),
      ]),
      mapcar(z1 => subst1(x, y, z1), cdddr(z)),
    )
  } else if eq(op, q_p_at) {
    // similar considerations here, but different structure of expression.
    let at_eqn_or_eqns = third(z)
    let at_eqns_list = if eq(caar(at_eqn_or_eqns), q_mlist) {
      rest(at_eqn_or_eqns)
    } else {
      list1(at_eqn_or_eqns)
    }
    list([
      remove(q_simp, car(z)),
      if member(y, mapcar(e => second(e), at_eqns_list)).truthy() {
        second(z)
      } else {
        subst1(x, y, second(z))
      },
      cons(
        list1(q_mlist),
        mapcar(e => list([first(e), second(e), subst1(x, y, third(e))]), at_eqns_list),
      ),
    ])
  } else if eq(op, q_p_derivative) {
    // and again, with yet a different structure.
    let vars_and_degrees = rest(rest(z))
    let diff_vars = Collector::new()
    let mut p = vars_and_degrees
    while p is Cons({ car: v, .. }) {
      diff_vars.add(v)
      p = cddr(p)
    }
    let diff_degrees = Collector::new()
    p = rest(vars_and_degrees)
    while p is Cons({ car: n, .. }) {
      diff_degrees.add(n)
      p = cddr(p)
    }
    let diff_vars = diff_vars.result()
    let pairs = Collector::new()
    let mut v = diff_vars
    let mut n = diff_degrees.result()
    while v is Cons({ car: vv, cdr: vd }) && n is Cons({ car: nn, cdr: nd }) {
      pairs.append_list(list2(vv, subst1(x, y, nn)))
      v = vd
      n = nd
    }
    append(
      list2(
        remove(q_simp, car(z)), // ensure resimplification after substitution
        if member(y, diff_vars).truthy() {
          second(z)
        } else {
          subst1(x, y, second(z))
        },
      ),
      pairs.result(),
    )
  } else {
    z
  }
}

///|
fn subst0(new_ : Value, old : Value) -> Value raise {
  if atom(new_) {
    new_
  } else if alike(cdr(new_), cdr(old)).truthy() {
    if eq(caar(new_), caar(old)) {
      old
    } else {
      simplifya(cons(cons(caar(new_), memq(q_array, cdar(old))), cdr(old)), Nil)
    }
  } else if memq(q_array, cdar(old)).truthy() {
    simplifya(cons(cons(caar(new_), list1(q_array)), cdr(new_)), Nil)
  } else {
    simplifya(new_, Nil)
  }
}

///|
fn subst1(x : Value, y : Value, z : Value) -> Value raise {
  // Y is an atom
  if atom(z) {
    return if equal(y, z) { x } else { z }
  }
  if specrepp(z).truthy() {
    return subst1(x, y, specdisrep(z))
  }
  if eq(caar(z), q_bigfloat) {
    return z
  }
  if eq(caar(z), q_rat) && (equal(y, cadr(z)) || equal(y, caddr(z))) {
    return div(subst1(x, y, cadr(z)), subst1(x, y, caddr(z)))
  }
  if at_substp(z).truthy() {
    return subst_except_second_arg(x, y, z)
  }
  if eq(y, t) && eq(caar(z), q_mcond) {
    return list([
      cons(caar(z), Nil),
      subst1(x, y, cadr(z)),
      subst1(x, y, caddr(z)),
      cadddr(z),
      subst1(x, y, car(cddddr(z))),
    ])
  }
  let margs = mapcar(z1 => subst1(x, y, z1), cdr(z))
  let oprx = getopr(x)
  let opry = getopr(y)
  if symval(q_d_opsubst).truthy() &&
    (eq(opry, caar(z)) || (eq(caar(z), q_rat) && eq(opry, q_mquotient))) {
    if numberp(x) ||
      memq(x, list([t, Nil, q_d__pcte, q_d__pctpi, q_d__pcti])).truthy() ||
      (!atom(x) && !(eq(car(x), q_lambda) || eq(caar(x), q_lambda))) {
      if (memq(q_array, cdar(z)).truthy() &&
        (
          (mnump(x).truthy() && symval(q_d_subnumsimp).truthy()) ||
          (!mnump(x).truthy() && !atom(x))
        )) ||
        d_subvarp(x).truthy() {
        with_special(q_substp, q_mqapply, () => subst0(
          list_star([list1(q_mqapply), x, margs]),
          z,
        ))
      } else {
        merr("subst: cannot substitute ~M for operator ~M in expression ~M", [
          x, y, z,
        ])
      }
    } else {
      subst0(cons(cons(oprx, Nil), margs), z)
    }
  } else {
    subst0(cons(cons(caar(z), Nil), margs), z)
  }
}

///|
fn subst2(
  x : Value,
  y : Value,
  z : Value,
  negxpty : Value,
  timesp : Value,
) -> Value raise {
  let mut z = z
  if atom(z) {
    return z
  }
  if specrepp(z).truthy() {
    return subst2(x, y, specdisrep(z), negxpty, timesp)
  }
  if at_substp(z).truthy() {
    // IS SUBST-EXCEPT-SECOND-ARG APPROPRIATE HERE ?? !!
    return z
  }
  if alike1(y, z).truthy() {
    return x
  }
  if timesp.truthy() && eq(caar(z), q_mtimes) {
    z = nformat(z)
    if alike1(y, z).truthy() {
      return x
    }
  }
  if eq(caar(y), q_mexpt) &&
    eq(caar(z), q_mexpt) &&
    alike1(cadr(y), cadr(z)).truthy() {
    let newexpt : Value = if alike1(negxpty, caddr(z)).truthy() {
      Fix(-1L)
    } else if symval(q_d_exptsubst).truthy() {
      expthack(caddr(y), caddr(z))
    } else {
      Nil
    }
    if newexpt.truthy() {
      return list3(list1(q_mexpt), x, newexpt)
    }
  }
  if symval(q_d_derivsubst).truthy() &&
    eq(caar(y), q_p_derivative) &&
    eq(caar(z), q_p_derivative) &&
    alike1(cadr(y), cadr(z)).truthy() {
    let tail = subst_diff_match(cddr(y), cdr(z))
    return if tail is Nil {
      z
    } else {
      cons(cons(caar(z), Nil), cons(x, cdr(tail)))
    }
  }
  recur_apply(
    lfunc("subst2-lambda", args => subst2(x, y, arg(args, 0), negxpty, timesp)),
    z,
  )
}

///|
/// The args to SUBSTITUTE are assumed to be simplified.
fn maxima_substitute(x : Value, y : Value, z : Value) -> Value raise {
  // Prevent replacing dependent variable with constant in derivative
  if !atom(z) && eq(caar(z), q_p_derivative) && eq(cadr(z), y) && numberp(x) {
    return z
  }
  with_specials([(q_in_p, t), (q_substp, t)], () => {
    let mut x = x
    let mut y = y
    let mut z = z
    if mnump(y).truthy() && num_eq(signum1(y), Fix(1L)) {
      z = with_specials([(q_d_sqrtdispflag, Nil), (q_d_pfeformat, t)], () => nformat_all(
        z,
      ))
    }
    let e = if atom(y) {
      if equal(y, Fix(-1L)) {
        y = list2(list1(q_mminus), Fix(1L))
        // negxpty and timesp don't matter in this call since (caar y) != 'mexpt
        subst2(x, y, nformat_all(z), Nil, Nil)
      } else {
        if !symbolp(x) && functionp(x) {
          let tem = gensym()
          setf_get(tem, q_operators, q_application_operator) |> ignore
          match x {
            Func(f) => defun(tem, f.call)
            _ => ()
          }
          x = tem
        }
        subst1(x, y, z)
      }
    } else {
      let negxpty = if eq(caar(y), q_mexpt) &&
        num_eq(signum1(caddr(y)), Fix(1L)) {
        mul2(Fix(-1L), caddr(y))
      } else {
        Nil
      }
      let timesp = if eq(caar(y), q_mtimes) {
        y = nformat(y)
        y
      } else {
        Nil
      }
      subst2(x, y, z, negxpty, timesp)
    }
    simplifya(e, Nil)
  })
}

///|
/// l1 is a list of expressions.  l2 is a list of variables. For each
/// element in list l2, substitute corresponding element of l1 into e
fn substitutel(l1 : Value, l2 : Value, e : Value) -> Value raise {
  let mut l1 = l1
  let mut l2 = l2
  let mut e = e
  while l1 is Cons({ car: a, cdr: d }) {
    e = maxima_substitute(a, car(l2), e)
    l1 = d
    l2 = cdr(l2)
  }
  e
}

///|
fn union_star(a : Value, b : Value) -> Value raise {
  let mut x = b
  for e in a.iter() {
    if !memalike(e, b).truthy() {
      x = cons(e, x)
    }
  }
  x
}

///|
fn intersect_star(a : Value, b : Value) -> Value raise {
  let mut x : Value = Nil
  for e in a.iter() {
    if memalike(e, b).truthy() {
      x = cons(e, x)
    }
  }
  x
}

///|
fn nthelem(n : Value, e : Value) -> Value raise {
  car(nthcdr(to_int(n) - 1, e))
}

///|
fn d_listp(x : Value) -> Value raise {
  match x {
    Cons({ car: Cons({ car: op, .. }), .. }) => lbool(eq(op, q_mlist))
    _ => Nil
  }
}

///|
fn depends(e : Value, x : Value) -> Value raise {
  let e = specrepcheck(e)
  if alike1(e, x).truthy() {
    return t
  }
  if mnump(e).truthy() {
    return Nil
  }
  if symbolp(e) {
    let l = mget(e, q_depends)
    if l.truthy() {
      // Go recursively through the list of dependencies.
      // This code detects indirect dependencies like a(x) and x(t).
      return dependsl(l, x)
    }
  }
  if atom(e) {
    return Nil
  }
  let r = depends(caar(e), x)
  if r.truthy() {
    r
  } else {
    dependsl(cdr(e), x)
  }
}

///|
fn dependsl(l : Value, x : Value) -> Value raise {
  for u in l.iter() {
    if depends(u, x).truthy() {
      return t
    }
  }
  Nil
}
