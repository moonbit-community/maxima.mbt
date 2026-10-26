// Port of share/diffequations/pwilt.lisp (Mark H. Weaver, 2010-2011):
// inverse Laplace transforms for piecewise functions.

///|
/// (pop l) on a local list variable: returns the car and advances.
fn pwilt__pop(l : Ref[Value]) -> Value {
  let x = car(l.val)
  l.val = cdr(l.val)
  x
}

///|
fn pwilt_add_parts(a : Value, b : Value) -> Value raise {
  fn pwilt_merge(ap : Value, bp : Value) -> Value raise {
    cons(car(ap), add2(cdr(ap), cdr(bp)))
  }
  let a = Ref::new(a)
  let b = Ref::new(b)
  let mut r : Value = Nil
  while true {
    if a.val is Nil {
      return nreconc(r, b.val)
    } else if b.val is Nil {
      return nreconc(r, a.val)
    } else if alike1(caar(a.val), caar(b.val)).truthy() {
      let ap = pwilt__pop(a)
      let bp = pwilt__pop(b)
      r = cons(pwilt_merge(ap, bp), r)
    } else if great(caar(a.val), caar(b.val)).truthy() {
      r = cons(pwilt__pop(a), r)
    } else {
      r = cons(pwilt__pop(b), r)
    }
  }
  Nil
}

///|
/// (reduce fn list) with no initial value.
fn pwilt__reduce(
  f : (Value, Value) -> Value raise,
  l : Value,
) -> Value raise {
  if l is Nil {
    // (reduce f nil) calls f with no arguments; not reached here.
    return Nil
  }
  let mut acc = car(l)
  for x in cdr(l).iter() {
    acc = f(acc, x)
  }
  acc
}

///|
fn pwilt_mult_parts(a : Value, b : Value) -> Value raise {
  pwilt__reduce(
    (x, y) => pwilt_add_parts(x, y),
    mapcar(
      ap => mapcar(
        bp => cons(add2(car(ap), car(bp)), mul2(cdr(ap), cdr(bp))),
        b,
      ),
      a,
    ),
  )
}

///|
fn pwilt_parts(e : Value, s : Value) -> Value raise {
  let e = specrepcheck(e)
  if freeof(s, e).truthy() {
    list1(cons(Fix(0L), e))
  } else if mplusp(e).truthy() {
    pwilt__reduce(
      (x, y) => pwilt_add_parts(x, y),
      mapcar(e1 => pwilt_parts(e1, s), margs(e)),
    )
  } else if mtimesp(e).truthy() {
    pwilt__reduce(
      (x, y) => pwilt_mult_parts(x, y),
      mapcar(e1 => pwilt_parts(e1, s), margs(e)),
    )
  } else if mexptp(e).truthy() && eq(mexpt_base(e), q_d__pcte) {
    let l = islinear(mexpt_expt(e), s)
    if l.truthy() {
      list1(cons(car(l), power(q_d__pcte, cdr(l))))
    } else {
      list1(cons(Fix(0L), e))
    }
  } else if mexptp(e).truthy() && eql(mexpt_expt(e), Fix(-1L)) {
    let dp = pwilt_parts(mexpt_base(e), s)
    if length(dp) == 1 {
      list1(cons(neg(caar(dp)), inv(cdar(dp))))
    } else if length(dp) == 2 &&
      freeof(q_p_pwilt_periodic, car(first(dp))).truthy() &&
      freeof(q_p_pwilt_periodic, car(second(dp))).truthy() &&
      zerop1(add2(cdr(first(dp)), cdr(second(dp)))).truthy() {
      let mut offset = car(first(dp))
      let mut period = sub(offset, car(second(dp)))
      let mut scale = cdr(first(dp))
      let sg = asksign(period)
      if eq(sg, q_d_positive) {
        ()
      } else if eq(sg, q_d_negative) {
        offset = sub(offset, period)
        period = neg(period)
        scale = neg(scale)
      } else {
        return list1(cons(Fix(0L), e))
      }
      list1(
        cons(add2(offset, take(list1(q_p_pwilt_periodic), [period])), scale),
      )
    } else {
      list1(cons(Fix(0L), e))
    }
  } else {
    list1(cons(Fix(0L), e))
  }
}

///|
/// ($hstep x): the verb function DEF-SIMPLIFIER defines for hstep.
fn pwilt__hstep(x : Value) -> Value raise {
  ftake(q_p_hstep, [x])
}

///|
fn pwilt_one_part(p : Value, s : Value, x : Value, xtemp : Value) -> Value raise {
  let xnew = add2(x, car(p))
  let lexp = cdr(p)
  if freeof(s, lexp).truthy() {
    mul2(lexp, take(list1(q_d_delta), [xnew]))
  } else if symval(q_d_pwilt_hstep_all).truthy() || !zerop1(car(p)).truthy() {
    mul2(
      pwilt__hstep(xnew),
      maxima_substitute(xnew, xtemp, pwilt1(lexp, s, xtemp)),
    )
  } else {
    pwilt1(lexp, s, x)
  }
}

///|
fn pwilt_subst_periodic(e : Value) -> Value raise {
  let mut counter = 0
  fn recurse(e : Value) -> Value raise {
    if !atom(e) && eq(caar(e), q_p_pwilt_periodic) {
      counter = counter + 1
      muln_([Fix(-1L), q_d__pctk, cadr(e)])
    } else if mplusp(e).truthy() {
      addn(mapcar(x => recurse(x), cdr(e)), t)
    } else {
      e
    }
  }
  let result = recurse(e)
  if counter < 2 && freeof(q_p_pwilt_periodic, result).truthy() {
    result
  } else {
    Nil
  }
}

///|
/// Returns the degree of E in S, or NIL if E is not a polynomial in S.
/// (This does not expand or simplify, so it may overestimate the degree.)
fn pwilt_polynomial_degree(e : Value, s : Value) -> Value raise {
  // RETURN-FROM PWILT-POLYNOMIAL-DEGREE NIL is signalled with None.
  fn recurse(e : Value) -> Int? raise {
    let e = specrepcheck(e)
    if alike1(s, e).truthy() {
      Some(1)
    } else if freeof(s, e).truthy() {
      Some(0)
    } else if mplusp(e).truthy() {
      let mut m : Int? = None
      for x in cdr(e).iter() {
        match recurse(x) {
          None => return None
          Some(d) =>
            m = match m {
              None => Some(d)
              Some(v) => Some(if d > v { d } else { v })
            }
        }
      }
      m
    } else if mtimesp(e).truthy() {
      let mut sum = 0
      for x in cdr(e).iter() {
        match recurse(x) {
          None => return None
          Some(d) => sum = sum + d
        }
      }
      Some(sum)
    } else if mexptp(e).truthy() &&
      integerp(mexpt_expt(e)) &&
      num_ge(mexpt_expt(e), Fix(0L)) {
      match recurse(mexpt_base(e)) {
        None => None
        Some(d) => Some(to_int(mexpt_expt(e)) * d)
      }
    } else {
      None
    }
  }
  match recurse(e) {
    Some(d) => int(d)
    None => Nil
  }
}

///|
fn pwilt1(e : Value, s : Value, x : Value) -> Value raise {
  let e = specrepcheck(e)
  if mbagp(e).truthy() {
    cons(car(e), mapcar(ee => pwilt1(ee, s, x), cdr(e)))
  } else if freeof(s, e).truthy() {
    mul2(e, take(list1(q_d_delta), [x]))
  } else if mplusp(e).truthy() {
    addn(mapcar(ee => pwilt1(ee, s, x), cdr(e)), t)
  } else if !atom(e) && eq(caar(e), q_p_laplace) && eq(cadddr(e), s) {
    if eq(x, caddr(e)) {
      cadr(e)
    } else {
      subst(x, caddr(e), cadr(e))
    }
  } else {
    pwilt2(e, s, x)
  }
}

///|
/// Calculate the inverse laplace transform by the residue method.
///
/// This works only when e is of the form P(s)/Q(s), where P(s) and Q(s) are
/// polynomials in s, and where the degree of P(s) is less than the degree
/// of Q(s).
fn pwilt2(e : Value, s : Value, x : Value) -> Value raise {
  let fail = () => list4(list2(q_p_ilt, q_simp), e, s, x)
  let n = d_num(e)
  let d = d_denom(e)
  let n_deg = pwilt_polynomial_degree(n, s)
  let d_deg = pwilt_polynomial_degree(d, s)
  if !(n_deg.truthy() && d_deg.truthy() && num_lt(n_deg, d_deg)) {
    let e2 = d_partfrac(e, s)
    if alike1(e, e2).truthy() {
      return fail()
    } else {
      return pwilt1(e2, s, x)
    }
  }
  let b = bind(q_d_multiplicities, Nil)
  defer unbind(b)
  let solns = with_specials(
    [
      (q_d_breakup, Nil),
      (q_d_programmode, t),
      (q_d_globalsolve, Nil),
      (q_d_solvedecomposes, t),
      (q_d_solveexplicit, t),
      (q_d_solvefactors, t),
    ],
    () => d_solve(d, varl=s),
  )
  let b2 = bind(q_d_demoivre, t)
  defer unbind(b2)
  let mults = symval(q_d_multiplicities)
  if !(d_listp(solns).truthy() &&
    d_listp(mults).truthy() &&
    length(solns) == length(mults) &&
    {
      let mut sum : Value = Fix(0L)
      for m in cdr(mults).iter() {
        sum = num_add(sum, m)
      }
      num_eq(d_deg, sum)
    }) {
    return fail()
  }
  let terms = Collector::new()
  let mut sl = cdr(solns)
  let mut ml = cdr(mults)
  while sl is Cons(_) && ml is Cons(_) {
    let soln = car(sl)
    let m = car(ml)
    if !(mequalp(soln).truthy() && eq(s, mequal_lhs(soln))) {
      return fail()
    }
    terms.add(
      maxima_substitute(
        mequal_rhs(soln),
        s,
        d_diff(
          list([
            muln_([
              power(q_d__pcte, mul2(s, x)),
              div(n, d_diff(list([d, s, m]))),
              m,
            ]),
            s,
            num_sub(m, Fix(1L)),
          ]),
        ),
      ),
    )
    sl = cdr(sl)
    ml = cdr(ml)
  }
  addn(terms.result(), t)
}

///|
fn d_pwilt(e : Value, s : Value, x : Value) -> Value raise {
  let e = specrepcheck(e)
  if mbagp(e).truthy() {
    return cons(delsimp(car(e)), mapcar(ee => d_pwilt(ee, s, x), cdr(e)))
  }
  let xtemp = gensym()
  let mut periodic = false
  let parts = Collector::new()
  for p in pwilt_parts(e, s).iter() {
    if freeof(q_p_pwilt_periodic, car(p)).truthy() {
      parts.add(pwilt_one_part(p, s, x, xtemp))
    } else {
      let offset = pwilt_subst_periodic(car(p))
      if offset is Nil {
        return list4(list1(q_p_pwilt), e, s, x)
      }
      let p = cons(offset, cdr(p))
      periodic = true
      parts.add(pwilt_one_part(p, s, x, xtemp))
    }
  }
  let result = addn(parts.result(), t)
  if periodic {
    list([list2(q_p_sum, q_simp), result, q_d__pctk, Fix(0L), q_d_inf])
  } else {
    result
  }
}

///|
fn init_share_pwilt() -> Unit raise {
  d_put(q_d_pwilt, Fix(1L), q_d_version) |> ignore
  if !d_get(q_d_hstep, q_d_version).truthy() {
    d_load(q_d_hstep) |> ignore
  }
  // (defmvar $pwilt_hstep_all nil): set by init_vars_..._pwilt.
}
