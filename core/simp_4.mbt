// Port of src/simp.lisp, part 4: matrices, %i powers, the ordering
// predicate GREAT, expansion, n-th roots and CRE helpers.

///|
fn simpmatrix(x : Value, vestigial : Value, z : Value) -> Value raise {
  ignore(vestigial)
  let x = cons(car(x), simpmap(cdr(x), z))
  let smp = symval(q_d_scalarmatrixp)
  if cddr(x) is Nil &&
    smp.truthy() &&
    (eq(smp, q_d_all) || member(q_mult, cdar(x)).truthy()) &&
    d_listp(cadr(x)).truthy() &&
    cdadr(x).truthy() &&
    cddr(cadr(x)) is Nil {
    cadr(cadr(x))
  } else {
    let mut badp = false
    for row in cdr(x).iter() {
      if !d_listp(row).truthy() {
        badp = true
        break
      }
    }
    if !(cdr(x) is Nil) && !badp {
      matcheck(cdr(x)) |> ignore
    }
    cons(
      if badp {
        list2(q_p_matrix, q_simp)
      } else {
        list2(q_d_matrix, q_simp)
      },
      cdr(x),
    )
  }
}

///|
fn p_itopot(pot : Value) -> Value raise {
  if fixnump(pot) {
    let i = to_int(logand(pot, Fix(3L)))
    if i == 0 {
      Fix(1L)
    } else if i == 1 {
      q_d__pcti
    } else if i == 2 {
      Fix(-1L)
    } else {
      list3(list2(q_mtimes, q_simp), Fix(-1L), q_d__pcti)
    }
  } else {
    // %i^pot = (-1)^(pot/2), where %i = (-1)^(1/2) is a principal value
    let half = mk_simp(q_rat, [Fix(1L), Fix(2L)])
    let e = mul2(pot, half)
    if neg_real_root_p(Fix(-1L), half, e).truthy() {
      neg_principal_power(Fix(-1L), e)
    } else {
      power(Fix(-1L), e)
    }
  }
}

///|
fn mnlogp(pot : Value) -> Value raise {
  if eq(caar(pot), q_p_log) {
    simplifya(cadr(pot), Nil)
  } else if eq(caar(pot), q_mtimes) &&
    !atom(caddr(pot)) &&
    eq(caar(caddr(pot)), q_p_log) &&
    cdddr(pot) is Nil &&
    (
      maxima_integerp(cadr(pot)).truthy() ||
      (
        symval(q_d__pcte_to_numlog).truthy() &&
        d_numberp(cadr(pot)).truthy()
      )
    ) {
    power(cadr(caddr(pot)), cadr(pot))
  } else {
    Nil
  }
}

///|
fn mnlog(pot : Value) -> Value raise {
  let mut pot = pot
  let mut a : Value = Nil
  let mut c : Value = Nil
  while true {
    if pot is Nil {
      if a.truthy() {
        a = cons(list1(q_mtimes), a)
      }
      if c.truthy() {
        c = list3(list2(q_mexpt, q_simp), q_d__pcte, addn(c, Nil))
      }
      return if c is Nil {
        simptimes(a, Fix(1L), Nil)
      } else if a is Nil {
        c
      } else {
        simptimes(append(a, list1(c)), Fix(1L), Nil)
      }
    }
    let b = if among(q_p_log, car(pot)).truthy() {
      mnlogp(car(pot))
    } else {
      Nil
    }
    if b.truthy() {
      a = cons(b, a)
    } else {
      c = cons(car(pot), c)
    }
    pot = cdr(pot)
  }
  Nil
}

///|
fn p_etolog(pot : Value) -> Value raise {
  let r = mnlogp(pot)
  if r.truthy() {
    r
  } else if eq(caar(pot), q_mplus) {
    mnlog(cdr(pot))
  } else {
    list3(list2(q_mexpt, q_simp), q_d__pcte, pot)
  }
}

///|
fn zerores(r1 : Value, r2 : Value) -> Value raise {
  if d_bfloatp(r1).truthy() || d_bfloatp(r2).truthy() {
    symval(q_ear_bigfloatzero)
  } else if floatp(r1) || floatp(r2) {
    Flo(0.0)
  } else {
    Fix(0L)
  }
}

///|
fn evnump(n : Value) -> Value raise {
  lbool(
    (integerp(n) && evenp(n)) || (ratnump(n).truthy() && evenp(cadr(n))),
  )
}

///|
fn odnump(n : Value) -> Value raise {
  lbool((integerp(n) && oddp(n)) || (ratnump(n).truthy() && oddp(cadr(n))))
}

///|
fn simplexpon(e : Value) -> Value raise {
  let r = maxima_integerp(e)
  if r.truthy() {
    r
  } else {
    lbool(
      eq(symval(q_d_domain), q_d_real) &&
      ratnump(e).truthy() &&
      oddp(caddr(e)),
    )
  }
}

// With domain:real, b^(p/q) for a negative number b and odd q is the real
// root, as (-8)^(1/3) = -2, while for even q it is the principal value.
// Folding the exponents of such powers is only valid within one of the two
// readings.
//
// NEG-REAL-ROOT-P is true when folding exponents turns BASE^INNER, a
// principal value, into BASE^E that would be read as a real root.
// NEG-PRINCIPAL-POWER returns the principal value of BASE^E instead, as
// m1pbranch does for -1.

///|
fn neg_number_p(x : Value) -> Value raise {
  if integerp(x) || ratnump(x).truthy() {
    mnegp(x)
  } else {
    Nil
  }
}

///|
fn neg_real_root_p(base : Value, inner : Value, e : Value) -> Value raise {
  lbool(
    eq(symval(q_d_domain), q_d_real) &&
    neg_number_p(base).truthy() &&
    ratnump(inner).truthy() &&
    evenp(caddr(inner)) &&
    ratnump(e).truthy() &&
    oddp(caddr(e)),
  )
}

///|
fn neg_principal_power(base : Value, e : Value) -> Value raise {
  with_special(q_d__pctemode, t, () => mul2(
    power(neg(base), e),
    power_star(q_d__pcte, list([list1(q_mtimes), e, q_d__pctpi, q_d__pcti])),
  ))
}

///|
/// BASE^E1*BASE^E2 for a negative number BASE where adding the exponents
/// would mix up the two readings, else NIL.
fn neg_power_product(base : Value, e1 : Value, e2 : Value) -> Value raise {
  if eq(symval(q_d_domain), q_d_real) &&
    neg_number_p(base).truthy() &&
    ratnump(e1).truthy() &&
    ratnump(e2).truthy() {
    let e = add2(e1, e2)
    if evenp(caddr(e1)) && evenp(caddr(e2)) {
      if neg_real_root_p(base, e1, e).truthy() {
        neg_principal_power(base, e)
      } else {
        Nil
      }
    } else if evenp(caddr(e1)) {
      neg_power_product(base, e2, e1)
    } else if evenp(caddr(e2)) {
      muln_([
        if oddp(cadr(e1)) {
          Fix(-1L)
        } else {
          Fix(1L)
        },
        power(neg(base), e),
        power(Fix(-1L), e2),
      ])
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// This function is not called in Maxima core or share code.
fn noneg(p : Value) -> Value raise {
  let s = d_sign(p)
  lbool(
    free(p, q_d__pcti).truthy() &&
    (eq(s, q_d_pos) || eq(s, q_d_pz) || eq(s, q_d_zero)),
  )
}

///|
fn radmabs(e : Value) -> Value raise {
  if symval(q_limitp).truthy() && free(e, q_d__pcti).truthy() {
    asksign_p_or_n(e) |> ignore
  }
  simplifya(list2(list1(q_mabs), e), t)
}

///|
fn simpmqapply(exp_ : Value, y : Value, z : Value) -> Value raise {
  let simpfun = if !atom(cadr(exp_)) {
    safe_get(caaadr(exp_), q_specsimp)
  } else {
    Nil
  }
  if simpfun.truthy() {
    funcall(simpfun, [exp_, y, z])
  } else {
    let u = simpargs(exp_, z)
    if symbolp(cadr(u)) {
      simplifya(cons(cons(cadr(u), cdar(u)), cddr(u)), t)
    } else {
      u
    }
  }
}

///|
/// TRUE, if the symbol e is declared to be $complex or $imaginary.
fn decl_complexp(e : Value) -> Value raise {
  kindp(e, q_d_complex)
}

///|
/// TRUE, if the symbol e is declared to be $real, $rational, $irrational,
/// $integer, $even or $odd.
fn decl_realp(e : Value) -> Value raise {
  kindp(e, q_d_real)
}

///|
/// TRUE, if the symbol e is declared to be $imaginary.
fn decl_imaginaryp(e : Value) -> Value raise {
  kindp(e, q_d_imaginary)
}

///|
/// The ordering predicate of the simplifier.
///
/// WARNING:  Exercise extreme caution when modifying this function!
fn great(x : Value, y : Value) -> Value raise {
  if atom(x) {
    if atom(y) {
      if numberp(x) {
        if numberp(y) {
          // X is "greater" than Y if X > Y numerically; if X and Y are
          // numerically equal, X is "greater" if it is a float and Y is not.
          if num_gt(x, y) {
            t
          } else if num_lt(x, y) {
            Nil
          } else {
            lbool(floatp(x) && !floatp(y))
          }
        } else {
          Nil
        }
        // An atom belongs to the class of the first clause below that
        // applies to it: number, constant, scalar, mainvar, plain symbol.
        // In that order, the classes are increasingly "great".
      } else if constant(x).truthy() {
        if constant(y).truthy() {
          alphalessp(y, x)
        } else {
          lbool(numberp(y))
        }
      } else if mget(x, q_d_scalar).truthy() {
        if mget(y, q_d_scalar).truthy() {
          if constant(y).truthy() {
            t
          } else {
            alphalessp(y, x)
          }
        } else {
          maxima_constantp(y)
        }
      } else if mget(x, q_d_mainvar).truthy() {
        if mget(y, q_d_mainvar).truthy() {
          if mget(y, q_d_scalar).truthy() || constant(y).truthy() {
            t
          } else {
            alphalessp(y, x)
          }
        } else {
          t
        }
      } else {
        let r = maxima_constantp(y)
        if r.truthy() {
          return r
        }
        let r = mget(y, q_d_scalar)
        if r.truthy() {
          return r
        }
        lbool(!mget(y, q_d_mainvar).truthy() && alphalessp(y, x).truthy())
      }
    } else {
      lbool(!ordfna(y, x).truthy())
    }
  } else if atom(y) {
    ordfna(x, y)
  } else if eq(caar(x), q_rat) {
    if eq(caar(y), q_rat) {
      lbool(
        num_gt(num_mul(caddr(y), cadr(x)), num_mul(caddr(x), cadr(y))),
      )
    } else {
      Nil
    }
  } else if eq(caar(y), q_rat) {
    t
  } else if eq(caar(x), q_bigfloat) {
    // A bigfloat is "less" than every other non-atomic expression,
    // but "greater" than a rational number.
    if eq(caar(y), q_bigfloat) {
      ordbfloat(x, y)
    } else {
      Nil
    }
  } else if eq(caar(y), q_bigfloat) {
    t
  } else if simp__ordfn_op_p(caar(x)) || simp__ordfn_op_p(caar(y)) {
    ordfn(x, y)
  } else if eq(caar(x), q_mrat) || eq(caar(y), q_mrat) {
    raise LispError::SimpleError("GREAT: internal error: unexpected MRAT argument")
  } else {
    let mut x1 = margs(x)
    let mut y1 = margs(y)
    while true {
      if x1 is Nil {
        return if y1.truthy() {
          Nil
        } else if !alike1(mop(x), mop(y)).truthy() {
          great(mop(x), mop(y))
        } else if member(q_array, cdar(x)).truthy() {
          lbool(!member(q_array, cdar(y)).truthy())
        } else {
          Nil
        }
      } else if y1 is Nil {
        return t
      } else if !alike1(car(x1), car(y1)).truthy() {
        return great(car(x1), car(y1))
      }
      x1 = cdr(x1)
      y1 = cdr(y1)
    }
    Nil
  }
}

///|
/// `(member op '(mtimes mplus mexpt %del))`
fn simp__ordfn_op_p(op : Value) -> Bool {
  eq(op, q_mtimes) || eq(op, q_mplus) || eq(op, q_mexpt) || eq(op, q_p_del)
}

///|
fn maxima_declared_array_alike1(x : Value, y : Value) -> Value raise {
  lisp_array_alike1(
    get(mget(x, q_array), q_array),
    get(mget(y, q_array), q_array),
  )
}

///|
fn maxima_undeclared_array_alike1(x : Value, y : Value) -> Value raise {
  if alike1(
      mfuncall(q_d_arrayinfo, list1(x)),
      mfuncall(q_d_arrayinfo, list1(y)),
    ).truthy() {
    alike1(d_listarray(x), d_listarray(y))
  } else {
    Nil
  }
}

///|
/// A is an atom
fn ordfna(e : Value, a : Value) -> Value raise {
  let op = caar(e)
  if numberp(a) {
    // Compare exactly - CL comparisons of a rational against a float are
    // exact.
    lbool(!eq(op, q_rat) || num_gt(num_div(cadr(e), caddr(e)), a))
  } else if !(eq(op, q_mplus) || eq(op, q_mtimes) || eq(op, q_mexpt)) &&
    constant(a).truthy() {
    lbool(!(eq(op, q_rat) || eq(op, q_bigfloat)))
  } else if eq(op, q_mrat) {
    // all MRATs succeed all atoms
    t
  } else if margs(e) is Nil {
    Nil
  } else if eq(op, q_mexpt) {
    ordmexpt(e, a).0
  } else if eq(op, q_mplus) || eq(op, q_mtimes) {
    let u = car(last(e))
    if eq(u, a) {
      lbool(!ordhack(e).truthy())
    } else {
      great(u, a)
    }
  } else if eq(op, q_p_del) {
    t
  } else {
    // use first arg of e
    let e = car(margs(e))
    if !atom(e) && (eq(caar(e), q_mplus) || eq(caar(e), q_mtimes)) {
      // and compare using same procedure as above
      let u = car(last(e))
      if eq(u, a) {
        lbool(!ordhack(e).truthy())
      } else {
        great(u, a)
      }
    } else if eq(e, a) {
      t
    } else {
      great(e, a)
    }
  }
}

///|
/// compare lists a and b elementwise from back to front
fn ordlist(a : Value, b : Value, cx : Value, cy : Value) -> Value raise {
  let av = list_to_array(a)
  let bv = list_to_array(b)
  let mut l1 = av.length()
  let mut l2 = bv.length()
  while true {
    if l1 == 0 {
      // Both lists exhausted with all elements pairwise ALIKE1:
      // the expressions are alike, so neither is "greater".
      return if l2 == 0 {
        Nil
      } else if eq(cx, cy) && l2 == 1 {
        great(if eq(cx, q_mplus) { Fix(0L) } else { Fix(1L) }, car(b))
      } else {
        Nil
      }
    } else if l2 == 0 {
      return lbool(
        !(
          if eq(cx, cy) && l1 == 1 {
            great(if eq(cy, q_mplus) { Fix(0L) } else { Fix(1L) }, car(a))
          } else {
            Nil
          }
        ).truthy(),
      )
    }
    let c = av[l1 - 1]
    let d = bv[l2 - 1]
    if !alike1(c, d).truthy() {
      return great(c, d)
    }
    l1 -= 1
    l2 -= 1
  }
  Nil
}

///|
fn term_list(x : Value) -> Value raise {
  if mplusp(x).truthy() {
    cdr(x)
  } else {
    list1(x)
  }
}

///|
fn factor_list(x : Value) -> Value raise {
  if mtimesp(x).truthy() {
    cdr(x)
  } else {
    list1(x)
  }
}

///|
/// one of the exprs x or y should be one of: %del, mexpt, mplus, mtimes
fn ordfn(x : Value, y : Value) -> Value raise {
  let cx = caar(x)
  let cy = caar(y)
  if eq(cx, q_p_del) {
    if eq(cy, q_p_del) {
      great(cadr(x), cadr(y))
    } else {
      t
    }
  } else if eq(cy, q_p_del) {
    Nil
  } else if eq(cx, q_mtimes) || eq(cy, q_mtimes) {
    ordlist(factor_list(x), factor_list(y), q_mtimes, q_mtimes)
  } else if eq(cx, q_mplus) || eq(cy, q_mplus) {
    ordlist(term_list(x), term_list(y), q_mplus, q_mplus)
  } else if eq(cx, q_mexpt) {
    ordmexpt(x, y).0
  } else if eq(cy, q_mexpt) {
    lbool(!ordmexpt(y, x).0.truthy())
  } else {
    Nil
  }
}

///|
fn ordhack(x : Value) -> Value raise {
  if cddr(x).truthy() && cdddr(x) is Nil {
    great(if eq(caar(x), q_mplus) { Fix(0L) } else { Fix(1L) }, cadr(x))
  } else {
    Nil
  }
}

///|
/// Return great(x,y), where x is an `mexpt` expression and y is any Maxima
/// expression. (The Lisp function returns a single value; the second
/// component of the declared tuple is always NIL.)
fn ordmexpt(x : Value, y : Value) -> (Value, Value) raise {
  // Decompose both x & y as x = base-x^exp-x & y = base-y^exp-y.
  let base_x = second(x)
  let exp_x = third(x)
  let (base_y, exp_y) = if mexptp(y).truthy() {
    (second(y), third(y))
  } else {
    (y, Fix(1L))
  }
  let r = if alike1(base_x, base_y).truthy() {
    // bases are alike; compare exponents
    great(exp_x, exp_y)
  } else {
    // default: comparison between bases
    great(base_x, base_y)
  }
  (r, Nil)
}

///|
/// 'Greater than' predicate (in the expression ordering, not numerical
/// sense) for two bigfloats, which can differ in presence of a SIMP flag,
/// precision and presence of a DECIMAL flag (radix).
fn ordbfloat(x : Value, y : Value) -> Value raise {
  let mant_x = cadr(x)
  let mant_y = cadr(y)
  let sgn_mant_x = signum(mant_x)
  let sgn_mant_y = signum(mant_y)
  if num_eq(sgn_mant_x, sgn_mant_y) {
    // Equal mantissa signs, compare exponents next.
    let exp_x = caddr(x)
    let exp_y = caddr(y)
    if num_eq(exp_x, exp_y) {
      // Equal exponents, compare mantissas next.
      if num_eq(mant_x, mant_y) {
        // Equal mantissas, compare precisions next.
        // An optional SIMP flag must be ignored.
        let rest_x = if eq(q_simp, cadar(x)) { cddar(x) } else { cdar(x) }
        let rest_y = if eq(q_simp, cadar(y)) { cddar(y) } else { cdar(y) }
        let prec_x = car(rest_x)
        let prec_y = car(rest_y)
        if num_eq(prec_x, prec_y) {
          // Finally, let decimal bigfloats "win" over binary bigfloats.
          lbool(eq(q_decimal, cadr(rest_x)) && !eq(q_decimal, cadr(rest_y)))
        } else {
          // Different precisions, directly compare (greater "wins").
          lbool(num_gt(prec_x, prec_y))
        }
      } else {
        // Different mantissas, directly compare (greater "wins").
        lbool(num_gt(mant_x, mant_y))
      }
    } else if plusp(sgn_mant_x) {
      // Different exponents, directly compare.
      // For positive mantissas, the greater exponent "wins",
      // for negative mantissas, the smaller exponent "wins".
      lbool(num_gt(exp_x, exp_y))
    } else {
      lbool(num_lt(exp_x, exp_y))
    }
  } else {
    // Different mantissa signs, directly compare.
    lbool(num_gt(sgn_mant_x, sgn_mant_y))
  }
}

///|
/// EXPANDEXPT computes the expansion of (x1 + x2 + ... + xm)^n
/// taking a sum and integer power as arguments.
fn expandexpt(sum : Value, power : Value) -> Value raise {
  let expansion = exponentiate_sum(cdr(sum), num_abs(power))
  if plusp(power) {
    expansion
  } else {
    inv(expansion)
  }
}

///|
fn exponentiate_sum(terms : Value, rpower : Value) -> Value raise {
  if zerop(rpower) {
    Fix(1L)
  } else if cdr(terms) is Nil {
    power(car(terms), rpower)
  } else if num_eq(rpower, Fix(1L)) {
    cons(list2(q_mplus, q_simp), terms)
  } else {
    let mut i : Value = Fix(0L)
    let mut result : Value = Fix(0L)
    while !num_gt(i, rpower) {
      let r1 = add2(
        result,
        muln(
          list([
            combination(rpower, i),
            exponentiate_sum(cdr(terms), num_sub(rpower, i)),
            power(car(terms), i),
          ]),
          t,
        ),
      )
      i = one_plus(i)
      result = r1
    }
    result
  }
}

///|
/// Computes the combination of n elements taken m at a time.
fn combination(n : Value, m : Value) -> Value raise {
  if num_gt(m, num_truncate(n, b=Fix(2L)).0) {
    combination(n, num_sub(n, m))
  } else {
    let mut result : Value = Fix(1L)
    let mut n1 = n
    let mut m1 : Value = Fix(1L)
    while !num_gt(m1, m) {
      let r = num_truncate(num_mul(result, n1), b=m1).0
      n1 = one_minus(n1)
      m1 = one_plus(m1)
      result = r
    }
    result
  }
}

///|
fn expandsums(a : Value, b : Value) -> Value raise {
  let mut c : Value = Nil
  let mut a = fixexpand(a)
  let b = cdr(b)
  while !(a is Nil) {
    c = cons(expandterms(car(a), b), c)
    a = cdr(a)
  }
  addn(c, t)
}

///|
fn expandterms(a : Value, b : Value) -> Value raise {
  let mut c : Value = Nil
  let mut b = b
  while !(b is Nil) {
    c = cons(mul2(a, car(b)), c)
    b = cdr(b)
  }
  addn(c, t)
}

///|
fn expandtimes(a : Value) -> Value raise {
  let mut simp_prods : Value = Nil
  let mut simp_negprods : Value = Nil
  let mut simp_sums : Value = Nil
  let mut simp_negsums : Value = Nil
  // genexpands
  let mut l = a
  while true {
    l = cdr(l)
    if l is Nil {
      simp_prods = nreverse(simp_prods)
      simp_negprods = nreverse(simp_negprods)
      simp_sums = nreverse(simp_sums)
      simp_negsums = nreverse(simp_negsums)
      break
    }
    let f = car(l)
    if atom(f) {
      simp_prods = cons(f, simp_prods)
    } else if eq(caar(f), q_rat) {
      if !equal(cadr(f), Fix(1L)) {
        simp_prods = cons(cadr(f), simp_prods)
      }
      simp_negprods = cons(caddr(f), simp_negprods)
    } else if eq(caar(f), q_mplus) {
      simp_sums = cons(f, simp_sums)
    } else if eq(caar(f), q_mexpt) &&
      equal(caddr(f), Fix(-1L)) &&
      mplusp(cadr(f)).truthy() {
      simp_negsums = cons(cadr(f), simp_negsums)
    } else if eq(caar(f), q_mexpt) &&
      with_special(q_ear_expandp, t, () => mminusp(caddr(f))).truthy() {
      simp_negprods = cons(
        if equal(caddr(f), Fix(-1L)) {
          cadr(f)
        } else {
          list3(car(f), cadr(f), neg(caddr(f)))
        },
        simp_negprods,
      )
    } else {
      simp_prods = cons(f, simp_prods)
    }
  }
  simp_prods = if simp_prods is Nil {
    Fix(1L)
  } else if cdr(simp_prods) is Nil {
    car(simp_prods)
  } else {
    cons(list2(q_mtimes, q_simp), simp_prods)
  }
  simp_negprods = if simp_negprods is Nil {
    Fix(1L)
  } else if cdr(simp_negprods) is Nil {
    car(simp_negprods)
  } else {
    cons(list2(q_mtimes, q_simp), simp_negprods)
  }
  if !(simp_sums is Nil) {
    let mut expsums = car(simp_sums)
    for c in cdr(simp_sums).iter() {
      expsums = expandsums(expsums, c)
    }
    simp_prods = if equal(simp_prods, Fix(1L)) {
      expsums
    } else {
      expandterms(simp_prods, fixexpand(expsums))
    }
  }
  // down
  if simp_negsums is Nil {
    return if equal(Fix(1L), simp_negprods) {
      simp_prods
    } else if mplusp(simp_prods).truthy() {
      expandterms(power(simp_negprods, Fix(-1L)), cdr(simp_prods))
    } else {
      let sp = simp_prods
      let sn = simp_negprods
      with_special(q_ear_expandflag, t, () => mul2(sp, power(sn, Fix(-1L))))
    }
  }
  let mut expnegsums = car(simp_negsums)
  for c in cdr(simp_negsums).iter() {
    expnegsums = expandsums(expnegsums, c)
  }
  expnegsums = expandterms(simp_negprods, fixexpand(expnegsums))
  if mplusp(simp_prods).truthy() {
    expandterms(inv(expnegsums), cdr(simp_prods))
  } else {
    let sp = simp_prods
    let en = expnegsums
    with_special(q_ear_expandflag, t, () => mul2(sp, inv(en)))
  }
}

///|
fn expand1(exp_ : Value, d_expop : Value, d_expon : Value) -> Value raise {
  with_specials([(q_d_expop, d_expop), (q_d_expon, d_expon)], () => {
    if !(integerp(d_expop) && num_gt(d_expop, Fix(-1L))) {
      merr("expand: expop must be a nonnegative integer; found: ~M", [d_expop])
      |> ignore
    }
    if !(integerp(d_expon) && num_gt(d_expon, Fix(-1L))) {
      merr("expand: expon must be a nonnegative integer; found: ~M", [d_expon])
      |> ignore
    }
    resimplify(specrepcheck(exp_))
  })
}

///|
fn fixexpand(a : Value) -> Value raise {
  if !mplusp(a).truthy() {
    list1(a)
  } else {
    cdr(a)
  }
}

///|
/// Computes the NTH-ROOT of IN
fn simp__nrthk2(in_ : Value, nth_root : Value) -> Value raise {
  power_star(in_, list3(list1(q_rat), Fix(1L), nth_root))
}

///|
/// Computes the NTH-ROOT of -IN
fn simp__nrthk1(in_ : Value, nth_root : Value) -> Value raise {
  if symval(q_d_radexpand).truthy() {
    mul2(simp__nrthk2(in_, nth_root), nrthk(Fix(-1L), nth_root))
  } else {
    simp__nrthk2(mul2_star(Fix(-1L), in_), nth_root)
  }
}

///|
fn nrthk(in_ : Value, nth_root : Value) -> Value raise {
  if equal(in_, Fix(1L)) {
    Fix(1L)
  } else if equal(in_, Fix(-1L)) {
    if equal(nth_root, Fix(2L)) {
      q_d__pcti
    } else if eq(symval(q_d_domain), q_d_real) {
      if even(nth_root).truthy() {
        simp__nrthk2(Fix(-1L), nth_root)
      } else {
        Fix(-1L)
      }
    } else if symval(q_d_m1pbranch).truthy() {
      with_special(q_d__pctemode, t, () => power_star(
        q_d__pcte,
        list([
          list1(q_mtimes),
          list3(list1(q_rat), Fix(1L), nth_root),
          q_d__pctpi,
          q_d__pcti,
        ]),
      ))
    } else {
      simp__nrthk2(Fix(-1L), nth_root)
    }
  } else if (symval(q_wflag).truthy() && eq(d_asksign(in_), q_d_neg)) ||
    (mnump(in_).truthy() && equal(d_sign(in_), q_d_neg)) {
    simp__nrthk1(mul2_star(Fix(-1L), in_), nth_root)
  } else {
    simp__nrthk2(in_, nth_root)
  }
}

///|
/// `(quotient a b)` (CL QUOT): TRUNCATE for integers, / otherwise.
fn simp__quotient(a : Value, b : Value) -> Value raise {
  if integerp(a) && integerp(b) {
    num_truncate(a, b~).0
  } else {
    num_div(a, b)
  }
}

///|
/// Computes the NTH-ROOT of X
fn simpnrt(x : Value, nth_root : Value) -> Value raise {
  with_specials(
    [(q_varlist, Nil), (q_genvar, Nil), (q_d_factorflag, Nil), (q_d_dontfactor, Nil)],
    () => {
      let mut simp_in : Value = Nil
      let mut simp_out : Value = Nil
      set(q_d_factorflag, t) |> ignore
      newvar(x) |> ignore
      let x = ratrep_star(x)
      if equal(cadr(x), Fix(0L)) {
        return Fix(0L)
      }
      let x = ratfact(cdr(x), q_psqfr)
      // simpnrt1
      let mut x = mapcar(f => pdis(f), x)
      while !(x is Nil) {
        let y = num_gcd(cadr(x), nth_root)
        if !equal(Fix(1L), y) {
          simp_out = cons(
            simpnrt(
              list3(list1(q_mexpt), car(x), simp__quotient(cadr(x), y)),
              simp__quotient(nth_root, y),
            ),
            simp_out,
          )
        } else if equal(cadr(x), Fix(1L)) &&
          integerp(car(x)) &&
          plusp(car(x)) &&
          {
            let y = pnthrootp(car(x), nth_root)
            if y.truthy() {
              simp_out = cons(y, simp_out)
              true
            } else {
              false
            }
          } {
          ()
        } else {
          if !num_gt(nth_root, num_abs(cadr(x))) {
            simp_out = cons(
              list3(list1(q_mexpt), car(x), simp__quotient(cadr(x), nth_root)),
              simp_out,
            )
          }
          simp_in = cons(
            list3(list1(q_mexpt), car(x), num_rem(cadr(x), nth_root)),
            simp_in,
          )
        }
        x = cddr(x)
      }
      simp_out = if simp_out.truthy() { muln(simp_out, Nil) } else { Fix(1L) }
      simp_in = if simp_in.truthy() {
        simp_in = muln(simp_in, Nil)
        nrthk(simp_in, nth_root)
      } else {
        Fix(1L)
      }
      let si = simp_in
      let so = simp_out
      with_special(q_d__pctemode, t, () => simplifya(
        list3(list1(q_mtimes), si, so),
        lbool(
          !(
            atom(si) ||
            atom(cadr(si)) ||
            eq(caaadr(si), q_mplus) ||
            eq(caaadr(si), q_mtimes) ||
            eq(caaadr(si), q_rat)
          ),
        ),
      ))
    },
  )
}

///|
fn ratp(a : Value, ratp_var : Value) -> Value raise {
  if atom(a) {
    t
  } else if eq(caar(a), q_mplus) || eq(caar(a), q_mtimes) {
    for e in cdr(a).iter() {
      if !ratp(e, ratp_var).truthy() {
        return Nil
      }
    }
    t
  } else if eq(caar(a), q_mexpt) {
    if free(cadr(a), ratp_var).truthy() {
      free(caddr(a), ratp_var)
    } else {
      lbool(integerp(caddr(a)) && ratp(cadr(a), ratp_var).truthy())
    }
  } else {
    free(a, ratp_var)
  }
}

///|
fn ratnumerator(r : Value) -> Value raise {
  if atom(r) {
    r
  } else if atom(cdr(r)) {
    car(r)
  } else if numberp(cadr(r)) {
    r
  } else {
    car(r)
  }
}

///|
fn ratdenominator(r : Value) -> Value raise {
  if atom(r) {
    Fix(1L)
  } else if atom(cdr(r)) {
    cdr(r)
  } else if numberp(cadr(r)) {
    Fix(1L)
  } else {
    cdr(r)
  }
}

///|
/// (BPROG U V) returns A and B (as ((A1 . A2) B1 . B2) with A = A1/A2,
/// B = B1/B2) such that B/U + A/V = 1/(U*V).
fn bprog(r : Value, s : Value, bprog_var : Value) -> Value raise {
  let r = ratfix(r)
  let s = ratfix(s)
  let mut coef2r : Value = Fix(0L)
  let mut coef1s : Value = Fix(0L)
  let mut coef2s : Value = Fix(1L)
  let mut coef1r : Value = Fix(1L)
  let mut a : Value = Fix(1L)
  let mut egcd : Value = Fix(1L)
  let mut p1b = car(r)
  if !zerop(pdegree(p1b, bprog_var)) {
    egcd = pgcdexpon(p1b)
  }
  let mut p2b = car(s)
  if !(zerop(pdegree(p2b, bprog_var)) || num_eq(egcd, Fix(1L))) {
    egcd = num_gcd(egcd, pgcdexpon(p2b))
    p1b = pexpon_star_sl_sl(p1b, egcd, Nil)
    p2b = pexpon_star_sl_sl(p2b, egcd, Nil)
  }
  while true {
    // b1
    if num_lt(pdegree(p1b, bprog_var), pdegree(p2b, bprog_var)) {
      let t1 = p1b
      p1b = p2b
      p2b = t1
      let t2 = coef1r
      coef1r = coef2r
      coef2r = t2
      let t3 = coef1s
      coef1s = coef2s
      coef2s = t3
    }
    if zerop(pdegree(p2b, bprog_var)) {
      if !zerop(pdegree(coef2r, bprog_var)) {
        coef2r = pexpon_star_sl_sl(coef2r, egcd, t)
      }
      if !zerop(pdegree(coef2s, bprog_var)) {
        coef2s = pexpon_star_sl_sl(coef2s, egcd, t)
      }
      return cons(
        ratreduce(ptimes(cdr(r), coef2r), p2b),
        ratreduce(ptimes(cdr(s), coef2s), p2b),
      )
    }
    let mut f1 = psquorem1(cdr(p1b), cdr(p2b), t)
    let f1v = f1
    let (f2, p1b_new) = with_special(q_d_algebraic, Nil, () => (
      psimp(bprog_var, cadr(f1v)),
      psimp(bprog_var, caddr(f1v)),
    ))
    p1b = p1b_new
    p1b = pquotientchk(p1b, a)
    f1 = car(f1)
    coef1r = pquotientchk(pdifference(ptimes(f1, coef1r), ptimes(f2, coef2r)), a)
    coef1s = pquotientchk(pdifference(ptimes(f1, coef1s), ptimes(f2, coef2s)), a)
    a = f1
  }
  Nil
}

///|
fn ratdifference(a : Value, b : Value) -> Value raise {
  ratplus(a, ratminus(b))
}

///|
fn ratpl(a : Value, b : Value) -> Value raise {
  ratplus(ratfix(a), ratfix(b))
}

///|
fn ratti(a : Value, b : Value, c : Value) -> Value raise {
  rattimes(ratfix(a), ratfix(b), c)
}

///|
fn ratqu(a : Value, b : Value) -> Value raise {
  ratquotient(ratfix(a), ratfix(b))
}

///|
fn ratfix(a : Value) -> Value raise {
  if equal(a, ratnumerator(a)) {
    cons(a, Fix(1L))
  } else {
    a
  }
}

///|
fn ratdivide(f : Value, g : Value) -> Value raise {
  let ff = ratfix(f)
  let fnum = car(ff)
  let fden = cdr(ff)
  let gg = ratfix(g)
  let gnum = car(gg)
  let gden = cdr(gg)
  let qr = pdivide(fnum, gnum)
  let q = car(qr)
  let r = cadr(qr)
  cons(ratqu(ratti(q, gden, t), fden), ratqu(r, fden))
}

///|
fn polcoef(l : Value, n : Value, polcoef_var : Value) -> Value raise {
  if atom(l) || pointergp(polcoef_var, car(l)).truthy() {
    if equal(n, Fix(0L)) {
      l
    } else {
      Fix(0L)
    }
  } else {
    ptterm(cdr(l), n)
  }
}

///|
fn disrep(l : Value, disrep_ratform : Value) -> Value raise {
  if equal(ratnumerator(l), l) {
    d_ratdisrep(cons(disrep_ratform, cons(l, Fix(1L))))
  } else {
    d_ratdisrep(cons(disrep_ratform, l))
  }
}

///|
fn simpargs1(a : Value, vestigial : Value, c : Value) -> Value raise {
  ignore(vestigial)
  simpargs(a, c)
}

///|
fn coeff(e : Value, var_ : Value, pow : Value) -> Value raise {
  simplify(
    if alike1(e, var_).truthy() {
      if equal(pow, Fix(1L)) {
        Fix(1L)
      } else {
        Fix(0L)
      }
    } else if atom(e) {
      if equal(pow, Fix(0L)) {
        e
      } else {
        Fix(0L)
      }
    } else if eq(caar(e), q_mexpt) {
      if alike1(cadr(e), var_).truthy() {
        if equal(pow, Fix(0L)) || !alike1(caddr(e), pow).truthy() {
          Fix(0L)
        } else {
          Fix(1L)
        }
      } else if equal(pow, Fix(0L)) {
        e
      } else {
        Fix(0L)
      }
    } else if eq(caar(e), q_mplus) || mbagp(e).truthy() {
      cons(
        if eq(caar(e), q_mplus) {
          list1(q_mplus)
        } else {
          car(e)
        },
        mapcar(e1 => coeff(e1, var_, pow), cdr(e)),
      )
    } else if eq(caar(e), q_mrat) {
      ratcoeff(e, var_, pow)
    } else if equal(pow, Fix(0L)) {
      if coeff_contains_powers(e, var_).truthy() {
        Fix(0L)
      } else {
        e
      }
    } else if eq(caar(e), q_mtimes) {
      let term = if equal(pow, Fix(1L)) { var_ } else { power(var_, pow) }
      if memalike(term, cdr(e)).truthy() {
        d_delete(term, e, n=Fix(1L))
      } else {
        Fix(0L)
      }
    } else {
      Fix(0L)
    },
  )
}

///|
/// Turns -inf into minf and -minf into inf, leaves everything else alone.
fn canonicalize_plus_inf(expr : Value) -> Value raise {
  if alike1(expr, mk(q_mtimes, [Fix(-1L), q_d_inf])).truthy() {
    q_d_minf
  } else if alike1(expr, mk(q_mtimes, [Fix(-1L), q_d_minf])).truthy() {
    q_d_inf
  } else {
    expr
  }
}

///|
/// Drop an imaginary part of the CL complex Z that is exactly zero.
fn real_if_real(z : Value) -> Value raise {
  if complexp(z) && zerop(imagpart(z)) {
    realpart(z)
  } else {
    z
  }
}
