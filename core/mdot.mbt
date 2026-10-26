// Port of src/mdot.lisp: non-commutative product and exponentiation
// simplifier.  Written July 1978 by CWH.
//
// Flags to control simplification: $dotconstrules, $dot0simp,
// $dot0nscsimp, $dot1simp, $domxnctimes, $dotident (globals).

///|
fn mdot__sv(s : Value) -> Bool {
  symval(s).truthy()
}

///|
fn simpnct(exp_ : Value, vestigial : Value, simp_flag : Value) -> Value raise {
  ignore(vestigial)
  let mut exp_ = exp_
  let check = exp_
  let first_factor = simpcheck(cadr(exp_), simp_flag)
  let remainder = if cdddr(exp_).truthy() {
    ncmuln(cddr(exp_), simp_flag)
  } else {
    simpcheck(caddr(exp_), simp_flag)
  }
  if cdr(exp_) is Nil {
    symval(q_d_dotident)
  } else if cddr(exp_) is Nil {
    first_factor
    // This does (. sc m) --> (f* sc m)  and  (. (f* sc m1) m2) --> (f* sc
    // (. m1 m2)) and (. m1 (f* sc m2)) --> (f* sc (. m1 m2)) where sc can be
    // a scalar or constant, and m1 and m2 are non-constant, non-scalar
    // expressions.
  } else if commutative_productp(first_factor, remainder).truthy() {
    mul2(first_factor, remainder)
  } else if product_with_inner_scalarp(first_factor).truthy() {
    let p_p = partition_product(first_factor)
    outer_constant(car(p_p), cdr(p_p), remainder)
  } else if product_with_inner_scalarp(remainder).truthy() {
    let p_p = partition_product(remainder)
    outer_constant(car(p_p), first_factor, cdr(p_p))
    // This code does distribution when flags are set and when called by
    // $EXPAND.  The way we recognize if we are called by $EXPAND is to look
    // at the value of $EXPOP, but this is a kludge since $EXPOP has nothing
    // to do with expanding (. A (f+ B C)) --> (f+ (. A B) (. A C)).
  } else if mplusp(first_factor).truthy() &&
    (mdot__sv(q_d_dotdistrib) || !zerop(symval(q_d_expop))) {
    addn(mapcar(x => ncmul2(x, remainder), cdr(first_factor)), t)
  } else if mplusp(remainder).truthy() &&
    (mdot__sv(q_d_dotdistrib) || !zerop(symval(q_d_expop))) {
    addn(mapcar(x => ncmul2(first_factor, x), cdr(remainder)), t)
    // This code carries out matrix operations when flags are set.
  } else if matrix_matrix_productp(first_factor, remainder).truthy() {
    timex(first_factor, remainder)
  } else if scalar_matrix_productp(first_factor, remainder).truthy() ||
    scalar_matrix_productp(remainder, first_factor).truthy() {
    simplifya(outermap1(list3(q_mnctimes, first_factor, remainder)), t)
    // (. (^^ x n) (^^ x m)) --> (^^ x (f+ n m))
  } else if simpnct_alike(first_factor, remainder).truthy() &&
    mdot__sv(q_d_dotexptsimp) {
    simpnct_merge_factors(first_factor, remainder)
    // (. (. x y) z) --> (. x y z)
  } else if mnctimesp(first_factor).truthy() && mdot__sv(q_d_dotassoc) {
    ncmuln(
      append(
        cdr(first_factor),
        if mnctimesp(remainder).truthy() {
          cdr(remainder)
        } else {
          ncons(remainder)
        },
      ),
      t,
    )
    // (. (^^ (. x y) m) (^^ (. x y) n) z) --> (. (^^ (. x y) m+n) z)
    // (. (^^ (. x y) m) x y z) --> (. (^^ (. x y) m+1) z)
    // (. x y (^^ (. x y) m) z) --> (. (^^ (. x y) m+1) z)
    // (. x y x y z) --> (. (^^ (. x y) 2) z)
  } else if mnctimesp(remainder).truthy() &&
    mdot__sv(q_d_dotassoc) &&
    mdot__sv(q_d_dotexptsimp) {
    exp_ = simpnct_merge_product(first_factor, cdr(remainder))
    if mnctimesp(exp_).truthy() && mdot__sv(q_d_dotassoc) {
      simpnct_antisym_check(cdr(exp_), check)
    } else {
      eqtest(exp_, check)
    }
    // (. x (. y z)) --> (. x y z)
  } else if mnctimesp(remainder).truthy() && mdot__sv(q_d_dotassoc) {
    simpnct_antisym_check(cons(first_factor, cdr(remainder)), check)
  } else {
    eqtest(list3(list1(q_mnctimes), first_factor, remainder), check)
  }
}

// Predicate functions for simplifying a non-commutative product to a
// commutative one.  SIMPNCT-CONSTANTP actually determines if a term is a
// constant and is not a nonscalar, i.e. not declared nonscalar and not a
// constant list or matrix.  The function CONSTANTP determines if its
// argument is a number or a variable declared constant.

///|
fn commutative_productp(first_factor : Value, remainder : Value) -> Value raise {
  let v = simpnct_sc_or_const_p(first_factor)
  if v.truthy() {
    return v
  }
  let v = simpnct_sc_or_const_p(remainder)
  if v.truthy() {
    return v
  }
  let v = simpnct_onep(first_factor)
  if v.truthy() {
    return v
  }
  let v = simpnct_onep(remainder)
  if v.truthy() {
    return v
  }
  let v = zero_productp(first_factor, remainder)
  if v.truthy() {
    return v
  }
  zero_productp(remainder, first_factor)
}

///|
fn simpnct_sc_or_const_p(term : Value) -> Value raise {
  let v = simpnct_constantp(term)
  if v.truthy() {
    v
  } else {
    simpnct_assumescalarp(term)
  }
}

///|
fn simpnct_constantp(term : Value) -> Value raise {
  if mdot__sv(q_d_dotconstrules) {
    let v = mnump(term)
    if v.truthy() {
      v
    } else {
      consttermp(term)
    }
  } else {
    Nil
  }
}

///|
fn simpnct_assumescalarp(term : Value) -> Value raise {
  if mdot__sv(q_d_dotscrules) {
    scalar_or_constant_p(term, lbool(eq(symval(q_d_assumescalar), q_d_all)))
  } else {
    Nil
  }
}

///|
fn simpnct_onep(term : Value) -> Value raise {
  if mdot__sv(q_d_dot1simp) {
    onep1(term)
  } else {
    Nil
  }
}

///|
fn zero_productp(one_term : Value, other_term : Value) -> Value raise {
  if zerop1(one_term).truthy() && mdot__sv(q_d_dot0simp) {
    if mdot__sv(q_d_dot0nscsimp) {
      symval(q_d_dot0nscsimp)
    } else {
      lbool(d_nonscalarp(other_term) is Nil)
    }
  } else {
    Nil
  }
}

// This function takes a form and determines if it is a product containing
// a constant or a declared scalar.  Note that in the next three functions,
// the word "scalar" is used to refer to a constant or a declared scalar.

///|
fn product_with_inner_scalarp(product : Value) -> Value raise {
  if mtimesp(product).truthy() &&
    (mdot__sv(q_d_dotconstrules) || mdot__sv(q_d_dotscrules)) {
    for f in cdr(product).iter() {
      if simpnct_sc_or_const_p(f).truthy() {
        return t
      }
    }
    Nil
  } else {
    Nil
  }
}

///|
/// This function takes a commutative product and separates it into a
/// scalar part and a non-scalar part.
fn partition_product(product : Value) -> Value raise {
  let mut scalar_list : Value = Nil
  let mut nonscalar_list : Value = Nil
  for f in cdr(product).iter() {
    if simpnct_sc_or_const_p(f).truthy() {
      scalar_list = cons(f, scalar_list)
    } else {
      nonscalar_list = cons(f, nonscalar_list)
    }
  }
  cons(nreverse(scalar_list), muln(nreverse(nonscalar_list), t))
}

///|
/// This function takes a list of constants and scalars, and two nonscalar
/// expressions and forms a non-commutative product of the nonscalar
/// expressions, and a commutative product of the constants and scalars and
/// the non-commutative product.
fn outer_constant(
  constant : Value,
  nonscalar1 : Value,
  nonscalar2 : Value,
) -> Value raise {
  muln(nconc(constant, ncons(ncmul2(nonscalar1, nonscalar2))), t)
}

///|
fn simpnct_base(term : Value) -> Value raise {
  if mncexptp(term).truthy() {
    cadr(term)
  } else {
    term
  }
}

///|
fn simpnct_power(term : Value) -> Value raise {
  if mncexptp(term).truthy() {
    caddr(term)
  } else {
    Fix(1L)
  }
}

///|
fn simpnct_alike(term1 : Value, term2 : Value) -> Value raise {
  alike1(simpnct_base(term1), simpnct_base(term2))
}

///|
fn simpnct_merge_factors(term1 : Value, term2 : Value) -> Value raise {
  ncpower(simpnct_base(term1), add2(simpnct_power(term1), simpnct_power(term2)))
}

///|
fn matrix_matrix_productp(term1 : Value, term2 : Value) -> Value raise {
  if (
      mdot__sv(q_d_doallmxops) ||
      mdot__sv(q_d_domxmxops) ||
      mdot__sv(q_d_domxnctimes)
    ) &&
    mxorlistp1(term1).truthy() {
    mxorlistp1(term2)
  } else {
    Nil
  }
}

///|
fn scalar_matrix_productp(term1 : Value, term2 : Value) -> Value raise {
  if (mdot__sv(q_d_doallmxops) || mdot__sv(q_d_doscmxops)) &&
    mxorlistp1(term1).truthy() {
    scalar_or_constant_p(term2, lbool(eq(symval(q_d_assumescalar), q_d_all)))
  } else {
    Nil
  }
}

///|
fn simpncexpt(
  exp_ : Value,
  vestigial : Value,
  simp_flag : Value,
) -> Value raise {
  ignore(vestigial)
  let factor = simpcheck(cadr(exp_), simp_flag)
  let power_ = simpcheck(caddr(exp_), simp_flag)
  let check = exp_
  twoargcheck(exp_) |> ignore
  if zerop1(power_).truthy() {
    if zerop1(factor).truthy() {
      if symval(q_errorsw) is Nil {
        merr("noncommutative exponent: ~M is undefined.", [
          list3(list1(q_mncexpt), factor, power_),
        ])
        |> ignore
      } else {
        throw_tag(q_errorsw, t) |> ignore
      }
    }
    if mxorlistp1(factor).truthy() {
      identitymx(factor)
    } else {
      symval(q_d_dotident)
    }
  } else if onep1(power_).truthy() {
    factor
  } else if simpnct_sc_or_const_p(factor).truthy() &&
    simpnct_sc_or_const_p(power_).truthy() {
    power(factor, power_)
  } else if zerop1(factor).truthy() && mdot__sv(q_d_dot0simp) {
    factor
  } else if onep1(factor).truthy() && mdot__sv(q_d_dot1simp) {
    factor
  } else if (mdot__sv(q_d_doallmxops) || mdot__sv(q_d_domxmxops)) &&
    mxorlistp1(factor).truthy() &&
    fixnump(power_) {
    let smp = {
      let v = d_listp(factor)
      if v.truthy() {
        v
      } else {
        symval(q_d_scalarmatrixp)
      }
    }
    with_special(q_d_scalarmatrixp, smp, () => simplify(powerx(factor, power_)))
    // This does (A+B)^^2 --> A^^2 + A.B + B.A + B^^2
    // and (A.B)^^2 --> A.B.A.B
  } else if (mplusp(factor).truthy() || !mdot__sv(q_d_dotexptsimp)) &&
    fixnump(power_) &&
    !num_gt(power_, symval(q_d_expop)) &&
    plusp(power_) {
    ncmul2(factor, ncpower(factor, one_minus(power_)))
    // This does the same thing as above for (A+B)^^(-2) and (A.B)^^(-2).
    // Here the "-" operator does the trick for us.
  } else if (mplusp(factor).truthy() || !mdot__sv(q_d_dotexptsimp)) &&
    fixnump(power_) &&
    !num_gt(num_neg(power_), symval(q_d_expon)) &&
    num_lt(power_, Fix(-1L)) {
    with_special(q_d_expop, symval(q_d_expon), () => {
      ncpower(ncpower(factor, num_neg(power_)), Fix(-1L))
    })
  } else if product_with_inner_scalarp(factor).truthy() {
    let p_p = partition_product(factor)
    mul2(power(muln(car(p_p), t), power_), ncpower(cdr(p_p), power_))
  } else if mdot__sv(q_d_dotassoc) && mncexptp(factor).truthy() {
    ncpower(cadr(factor), mul2(caddr(factor), power_))
  } else {
    eqtest(list3(list1(q_mncexpt), factor, power_), check)
  }
}

///|
fn simpnct_invert(exp_ : Value) -> Value raise {
  if mnctimesp(exp_).truthy() {
    ncmuln(nreverse(mapcar(x => simpnct_invert(x), cdr(exp_))), t)
  } else if mncexptp(exp_).truthy() && integerp(caddr(exp_)) {
    ncpower(cadr(exp_), num_neg(caddr(exp_)))
  } else {
    list3(list2(q_mncexpt, q_simp), exp_, Fix(-1L))
  }
}

///|
fn identitymx(x : Value) -> Value raise {
  if d_listp(cadr(x)).truthy() && length(cdr(x)) == length(cdadr(x)) {
    simplifya(cons(car(x), cdr(d_ident(int(length(cdr(x)))))), t)
  } else {
    symval(q_d_dotident)
  }
}

///|
/// This function incorporates the hairy search which enables such
/// simplifications as (. a b a b) --> (^^ (. a b) 2).  It assumes that
/// FIRST-FACTOR is not a dot product and that REMAINDER is.  For the
/// product (. a b c d e), three basic types of comparisons are done:
///
///  1)  a <---> b              first-factor <---> inner-product
///      a <---> (. b c)
///      a <---> (. b c d)
///      a <---> (. b c d e)    (this case handled in SIMPNCT)
///
///  2) (. a b) <---> c         outer-product <---> (car rest)
///     (. a b c) <---> d
///     (. a b c d) <---> e
///
///  3) (. a b) <---> (. c d)   outer-product <---> (firstn rest)
///
/// Note that INNER-PRODUCT and OUTER-PRODUCT share list structure which is
/// clobbered as new terms are added.
fn simpnct_merge_product(
  first_factor : Value,
  remainder : Value,
) -> Value raise {
  let half_product_length = (length(remainder) + 1) >> 1
  let mut inner_product = car(remainder)
  let outer_product = list3(
    list2(q_mnctimes, q_simp),
    first_factor,
    car(remainder),
  )
  let mut merge_length = 2
  let mut rest = cdr(remainder)
  while rest.truthy() {
    if simpnct_alike(first_factor, inner_product).truthy() {
      return ncmuln(
        cons(simpnct_merge_factors(first_factor, inner_product), rest),
        t,
      )
    } else if simpnct_alike(outer_product, car(rest)).truthy() {
      return ncmuln(
        cons(simpnct_merge_factors(outer_product, car(rest)), cdr(rest)),
        t,
      )
    } else if !(merge_length > half_product_length) &&
      alike1(
        outer_product,
        cons(list2(q_mnctimes, q_simp), subseq(rest, 0, end=merge_length)),
      ).truthy() {
      return ncmuln(
        cons(ncpower(outer_product, Fix(2L)), nthcdr(merge_length, rest)),
        t,
      )
    } else if merge_length == 2 {
      inner_product = cons(list2(q_mnctimes, q_simp), cddr(outer_product))
    }
    rplacd(last(inner_product), ncons(car(rest))) |> ignore
    merge_length += 1
    rest = cdr(rest)
  }
  outer_product
}

///|
fn simpnct_antisym_check(l : Value, check : Value) -> Value raise {
  if get(q_mnctimes, q_d_antisymmetric).truthy() && cddr(l).truthy() {
    let (l, antisym_sign) = bbsort1(l)
    if equal(l, Fix(0L)) {
      Fix(0L)
    } else {
      let l = eqtest(cons(list1(q_mnctimes), l), check)
      if antisym_sign is Nil {
        l
      } else {
        neg(l)
      }
    }
  } else {
    eqtest(cons(list1(q_mnctimes), l), check)
  }
}

///|
fn init_mdot() -> Unit raise {
  // The operators "." and "^^" distribute over equations.
  putprop(q_mnctimes, list1(q_mequal), q_distribute_u_over) |> ignore
  putprop(q_mncexpt, list1(q_mequal), q_distribute_u_over) |> ignore
}
