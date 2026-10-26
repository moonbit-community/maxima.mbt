// Port of src/simp.lisp, part 1: SIMPLIFYA, EQTEST, number arithmetic
// (ADDK, TIMESK, *RED, EXPTB), SIMPLUS/PLS/PLUSIN and matrix addition.

///|
/// macro WHILE (cond &rest body): a `do` loop. The Lisp macro takes
/// unevaluated forms; here COND is a function of no arguments and BODY a
/// list of such functions.
fn while_(cond : Value, body : Value) -> Value raise {
  while funcall(cond, []).truthy() {
    for f in body.iter() {
      funcall(f, []) |> ignore
    }
  }
  Nil
}

///|
/// This function behaves like (MEMBER M L :TEST #'EQ).
fn member_eq(m : Value, l : Value) -> Value raise {
  let mut l = l
  while l is Cons({ car: a, cdr: d }) {
    if eq(m, a) {
      return l
    }
    l = d
  }
  Nil
}

///|
let simp__lit_simp : Value = list1(q_simp)

///|
let simp__lit_simp_array : Value = list2(q_simp, q_array)

///|
fn sratsimp(e : Value) -> Value raise {
  simplifya(d_ratsimp(e, Nil), Nil)
}

///|
fn simpcheck(e : Value, flag : Value) -> Value raise {
  let e = if flag.truthy() { e } else { simplifya(e, Nil) }
  if specrepp(e).truthy() {
    specdisrep(e)
  } else {
    e
  }
}

///|
fn mratcheck(e : Value) -> Value raise {
  if d_ratp(e).truthy() {
    ratdisrep(e)
  } else {
    e
  }
}

///|
// Note that the following two functions are carefully coupled.
fn specrepp(e : Value) -> Value raise {
  match e {
    Cons({ car: Cons({ car: op, .. }), .. }) =>
      lbool(eq(op, q_mrat) || eq(op, q_mpois))
    _ => Nil
  }
}

///|
fn constant(x : Value) -> Value raise {
  if symbolp(x) {
    let v = get(x, q_sysconst)
    if v.truthy() {
      v
    } else {
      kindp(x, q_d_constant)
    }
  } else if d_subvarp(x).truthy() {
    if kindp(caar(x), q_d_constant).truthy() {
      for a in cdr(x).iter() {
        if !d_constantp(a).truthy() {
          return Nil
        }
      }
      t
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn maxima_constantp(x : Value) -> Value raise {
  if numberp(x) {
    return t
  }
  if symbolp(x) {
    let v = get(x, q_sysconst)
    if v.truthy() {
      v
    } else {
      kindp(x, q_d_constant)
    }
  } else {
    Nil
  }
}

///|
fn scalar_or_constant_p(x : Value, flag : Value) -> Value raise {
  if flag.truthy() {
    lbool(!d_nonscalarp(x).truthy())
  } else {
    d_scalarp(x)
  }
}

///|
fn consttermp(x : Value, constant? : Value = Nil) -> Value raise {
  lbool(
    (constant.truthy() || d_constantp(x).truthy()) &&
    !eq(scalarclass(x, constant=t), q_d_nonscalar),
  )
}

///|
/// The optional argument CONSTANT, if T, says that ($CONSTANTP EXP) is known
/// to be true. Then the arguments of EXP are constant too, so CONSTTERMP need
/// not check them again.  Returns $SCALAR, $NONSCALAR, or NIL (unknown).
fn scalarclass(exp_ : Value, constant? : Value = Nil) -> Value raise {
  if mnump(exp_).truthy() {
    // Maxima numbers are scalar.
    return q_d_scalar
  }
  if atom(exp_) {
    if mget(exp_, q_d_nonscalar).truthy() ||
      (
        !mget(exp_, q_d_scalar).truthy() &&
        // Arrays are nonscalar, but not if declared scalar.
        (arrayp(exp_) || d_member(exp_, symval(q_d_arrays)).truthy())
      ) {
      return q_d_nonscalar
    }
    if mget(exp_, q_d_scalar).truthy() ||
      // Include constant atoms which are not declared nonscalar.
      constant.truthy() ||
      d_constantp(exp_).truthy() {
      return q_d_scalar
    }
    return Nil
  }
  if member(q_array, car(exp_)).truthy() {
    return if mget(caar(exp_), q_d_scalar).truthy() {
      q_d_scalar
    } else if mget(caar(exp_), q_d_nonscalar).truthy() {
      q_d_nonscalar
    } else {
      Nil
    }
  }
  if specrepp(exp_).truthy() {
    return scalarclass(specdisrep(exp_), constant~)
  }
  // If the function is declared scalar or nonscalar, then return. If it
  // isn't explicitly declared, then try to be intelligent by looking at
  // the arguments to the function.
  let sc = scalarclass(caar(exp_))
  if sc.truthy() {
    return sc
  }
  // <number> + <scalar> is SCALARP because that seems to be useful.
  if eq(caar(exp_), q_mplus) || eq(caar(exp_), q_mtimes) {
    let mut l = cdr(exp_)
    while l is Cons({ car: a, cdr: d }) {
      if !consttermp(a, constant~).truthy() {
        return scalarclass_list(l, constant~)
      }
      l = d
    }
    return q_d_scalar
  }
  if eq(caar(exp_), q_mqapply) {
    let sc = scalarclass(cadr(exp_))
    if sc.truthy() {
      return sc
    }
  }
  if mxorlistp(exp_).truthy() {
    return q_d_nonscalar
  }
  // If we can't find out anything about the operator, then look at the
  // arguments to the operator.
  let mut l = list1(Fix(1L))
  for a in cdr(exp_).iter() {
    if !consttermp(a, constant~).truthy() {
      l = cons(a, l)
    }
  }
  scalarclass_list(l, constant~)
}

///|
/// SCALARCLASS-LIST takes a list of expressions as its argument.  If their
/// scalarclasses all agree, then that scalarclass is returned.
fn scalarclass_list(llist : Value, constant? : Value = Nil) -> Value raise {
  if llist is Nil {
    Nil
  } else if cdr(llist) is Nil {
    scalarclass(car(llist), constant~)
  } else {
    let sc_car = scalarclass(car(llist), constant~)
    let sc_cdr = scalarclass_list(cdr(llist), constant~)
    if eq(sc_car, q_d_nonscalar) || eq(sc_cdr, q_d_nonscalar) {
      q_d_nonscalar
    } else if eq(sc_car, q_d_scalar) && eq(sc_cdr, q_d_scalar) {
      q_d_scalar
    } else {
      Nil
    }
  }
}

///|
fn constmx(const_ : Value, x : Value) -> Value raise {
  simplifya(fmapl1(lfunc("constmx-lambda", _ => const_), list1(x)), t)
}

///|
/// ISINOP returns the complete subexpression with the operator OP, when the
/// operator OP is found in EXPR.
fn isinop(expr : Value, op : Value) -> Value raise {
  if atom(expr) {
    Nil
  } else if eq(caar(expr), op) && !member(q_array, cdar(expr)).truthy() {
    expr
  } else {
    for e in cdr(expr).iter() {
      let res = isinop(e, op)
      if res.truthy() {
        return res
      }
    }
    Nil
  }
}

///|
fn free(exp_ : Value, free_var : Value) -> Value raise {
  if alike1(exp_, free_var).truthy() {
    Nil
  } else if atom(exp_) {
    t
  } else {
    lbool(
      listp(car(exp_)) &&
      free(caar(exp_), free_var).truthy() &&
      freel(cdr(exp_), free_var).truthy(),
    )
  }
}

///|
fn freel(l : Value, free_var : Value) -> Value raise {
  let mut l = l
  while !(l is Nil) {
    match l {
      Cons({ car: a, cdr: d }) => {
        if !free(a, free_var).truthy() {
          return Nil
        }
        l = d
      }
      // second element of a pair
      _ => return free(l, free_var)
    }
  }
  t
}

///|
/// Return the last factor of X, if X is a product, otherwise X itself.
fn last_factor(x : Value) -> Value raise {
  if mtimesp(x).truthy() {
    car(last(x))
  } else {
    x
  }
}

///|
/// Is X - Y an integer? If possible, avoid going through the simplifier.
fn integer_difference_p(x : Value, y : Value) -> Value raise {
  if integerp(x) {
    lbool(integerp(y))
  } else if ratnump(x).truthy() {
    lbool(
      ratnump(y).truthy() &&
      integerp(
        num_sub(num_div(cadr(x), caddr(x)), num_div(cadr(y), caddr(y))),
      ),
    )
  } else {
    lbool(
      !integerp(y) && !ratnump(y).truthy() && integerp(sub(x, y)),
    )
  }
}

///|
fn simplifya(x : Value, y : Value) -> Value raise {
  let (head, args) = match x {
    Cons({ car, cdr }) => (car, cdr)
    _ => return x
  }
  if !symval(q_d_simp).truthy() {
    return x
  }
  let (op, flags) = match head {
    Cons({ car, cdr }) => (car, cdr)
    _ =>
      if !(args is Nil) && atom(args) {
        return merr("simplifya: malformed expression (atomic cdr).", [])
      } else if get(head, q_lisp_no_simp).truthy() {
        // this feature is to be used with care. it is meant to be
        // used to implement data objects with minimum of consing.
        return x
      } else {
        return cons(head, mapcar(a => simplifya(a, y), args))
      }
  }
  if eq(op, q_rat) {
    return n_starred1(x)
  }
  if symval(q_dosimp).truthy() {
    // Enforced resimplification: Reset dosimp and strip 'simp tags from x.
    return with_special(q_dosimp, Nil, () => simplifya(unsimplify(x), Nil))
  }
  if member_eq(q_simp, flags).truthy() {
    return x
  }
  if eq(op, q_mrat) {
    return x
  }
  if op is Str(_) {
    return simplifya(cons(cons(d_verbify(op), flags), args), y)
  }
  if !atom(op) {
    if eq(caaar(x), q_lambda) ||
      (!atom(caaar(x)) && eq(car(caaar(x)), q_lambda)) {
      return mapply1(op, args, op, x)
    } else {
      return merr(
        "simplifya: operator is neither an atom nor a lambda expression: ~S",
        [x],
      )
    }
  }
  if symval(q_d_distribute_over).truthy() &&
    get(op, q_distribute_over).truthy() {
    // A function with the property 'distribute_h_over.
    let r = distribute_h_over(x, y)
    if r.truthy() {
      return r
    }
  }
  if get(op, q_opers).truthy() {
    return with_special(q_opers_list, symval(q_n_staropers_list), () => oper_apply(
      x, y,
    ))
  }
  if eq(op, q_mqapply) &&
    (
      atom(cadr(x)) ||
      (
        eq(symval(q_substp), q_mqapply) &&
        (eq(car(cadr(x)), q_lambda) || eq(caar(cadr(x)), q_lambda))
      )
    ) {
    if symbolp(cadr(x)) || !atom(cadr(x)) {
      return simplifya(cons(cons(cadr(x), flags), cddr(x)), y)
    } else if !member_eq(q_array, flags).truthy() ||
      !symval(q_d_subnumsimp).truthy() {
      return merr(
        "simplifya: I don't know how to simplify this operator: ~M",
        [x],
      )
    } else {
      return cadr(x)
    }
  }
  let w = get(op, q_operators)
  if w.truthy() &&
    (!member_eq(q_array, flags).truthy() || rulechk(op).truthy()) {
    funcall(w, [x, Fix(1L), y])
  } else {
    simpargs(x, y)
  }
}

///|
/// EQTEST returns an expression which is the same as X
/// except that it is marked with SIMP and maybe other flags from CHECK.
///
/// (1) if X is already marked with SIMP flag or doesn't need it: return X.
/// (2) if X is pretty much the same as CHECK (same operator and same
///     arguments), then return CHECK after marking it with SIMP flag.
/// (3) if operator of X has the MSIMPIND property, replace it
///     with value of MSIMPIND (something like '(MPLUS SIMP)) and return X.
/// (4) if X or CHECK is an array expression, return X after marking it with
///     SIMP and ARRAY flags.
/// (5) otherwise, return X after marking it with SIMP flag.
fn eqtest(x : Value, check : Value) -> Value raise {
  if atom(x) ||
    eq(caar(x), q_rat) ||
    eq(caar(x), q_mrat) ||
    member_eq(q_simp, cdar(x)).truthy() {
    return x
  }
  if eq(caar(x), caar(check)) && equal(cdr(x), cdr(check)) {
    if cdar(check) is Nil {
      let y = get(caar(check), q_msimpind)
      if y.truthy() {
        return cons(y, cdr(check))
      }
    }
    if member_eq(q_simp, cdar(check)).truthy() {
      return check
    }
    return cons(
      cons(
        caar(check),
        if cdar(check).truthy() {
          cons(q_simp, cdar(check))
        } else {
          simp__lit_simp
        },
      ),
      cdr(check),
    )
  }
  let y = get(caar(x), q_msimpind)
  if y.truthy() {
    return rplaca(x, y)
  }
  if member_eq(q_array, cdar(x)).truthy() ||
    (eq(caar(x), caar(check)) && member_eq(q_array, cdar(check)).truthy()) {
    rplaca(x, cons(caar(x), simp__lit_simp_array))
  } else {
    rplaca(x, cons(caar(x), simp__lit_simp))
  }
}

///|
/// A function which distributes over bags like a list, matrix, or equation,
/// or any other operator.
fn distribute_h_over(expr : Value, args_simped : Value) -> Value raise {
  if length(cdr(expr)) == 1 {
    // Distribute over for a function with one argument.
    if !atom(cadr(expr)) &&
      memq(caaadr(expr), get(caar(expr), q_distribute_over)).truthy() {
      simplifya(
        cons(
          caadr(expr),
          mapcar(u => simplifya(list2(car(expr), u), args_simped), cdadr(expr)),
        ),
        t,
      )
    } else {
      Nil
    }
  } else {
    // A function with more than one argument.
    let mut args = cdr(expr)
    let mut first_args : Value = Nil
    while args is Cons({ car: a, cdr: rest_args }) {
      if !atom(a) &&
        memq(caar(a), get(caar(expr), q_distribute_over)).truthy() {
        // Distribute the function over the arguments and simplify again.
        let fa = first_args
        return simplifya(
          cons(
            list1(caar(a)),
            mapcar(
              u => simplifya(
                append(
                  append(cons(list1(caar(expr)), reverse(fa)), list1(u)),
                  rest_args,
                ),
                args_simped,
              ),
              cdr(a),
            ),
          ),
          t,
        )
      }
      first_args = cons(a, first_args)
      args = rest_args
    }
    Nil
  }
}

///|
fn rulechk(x : Value) -> Value raise {
  let v = mget(x, q_oldrules)
  if v.truthy() {
    v
  } else {
    get(x, q_rules)
  }
}

///|
fn resimplify(x : Value) -> Value raise {
  with_special(q_dosimp, t, () => simplifya(x, Nil))
}

///|
/// `(remove 'simp l :count 1)`
fn simp__remove_simp1(l : Value) -> Value {
  let c = Collector::new()
  let mut p = l
  let mut done = false
  while p is Cons({ car: a, cdr: d }) {
    if !done && eq(a, q_simp) {
      done = true
    } else {
      c.add(a)
    }
    p = d
  }
  c.result()
}

///|
fn unsimplify(x : Value) -> Value raise {
  if atom(x) || specrepp(x).truthy() {
    x
  } else {
    cons(simp__remove_simp1(car(x)), mapcar(a => unsimplify(a), cdr(x)))
  }
}

///|
fn simpargs(x : Value, y : Value) -> Value raise {
  let op = caar(x)
  if (
      eq(get(op, q_dimension), q_dimension_infix) &&
      !getl(op, list2(q_d_lassociative, q_d_rassociative)).truthy()
    ) ||
    get(op, q_binary).truthy() {
    twoargcheck(x) |> ignore
  }
  if member(q_array, cdar(x)).truthy() && margs(x) is Nil {
    merr("SIMPARGS: subscripted variable found with no subscripts.", []) |> ignore
  }
  eqtest(
    if eq(op, q_mlist) || eq(op, q_mequal) {
      // MLIST or MEQUAL: Arguments will not be converted from special
      // representations to the general form.
      if y.truthy() {
        // Arguments are already simplified - nothing to do here.
        x
      } else {
        // Arguments are not simplified. Strip any flags from the header,
        // and simplify arguments.
        cons(list1(op), mapcar(a => simplify(a), cdr(x)))
      }
    } else {
      // Not MLIST or MEQUAL. Strip any flags from the header, and call
      // SIMPMAP, which will convert special representations to general
      // form and simplify, if necessary (depending on flag Y).
      cons(list1(op), simpmap(cdr(x), y))
    },
    x,
  )
}

///|
/// ADDK adds two Maxima numbers and returns a simplified Maxima number.
/// The precision of a bigfloat result depends on $FPPREC. If $FLOAT is T,
/// a Maxima rational result is converted to a float number.
fn addk(x : Value, y : Value) -> Value raise {
  if eql(x, Fix(0L)) {
    return y
  }
  if eql(y, Fix(0L)) {
    return x
  }
  if numberp(x) && numberp(y) {
    return num_add(x, y)
  }
  if d_bfloatp(x).truthy() || d_bfloatp(y).truthy() {
    return d_bfloat(mk(q_mplus, [x, y]))
  }
  let mut x = x
  let mut y = y
  if numberp(x) {
    if floatp(x) {
      return num_add(x, fpcofrat(y))
    } else {
      x = list3(list1(q_rat), x, Fix(1L))
    }
  } else if numberp(y) {
    if floatp(y) {
      return num_add(y, fpcofrat(x))
    } else {
      y = list3(list1(q_rat), y, Fix(1L))
    }
  }
  let g = num_gcd(caddr(x), caddr(y))
  let a = num_truncate(caddr(x), b=g).0
  let b = num_truncate(caddr(y), b=g).0
  timeskl(
    list3(list1(q_rat), Fix(1L), g),
    list3(
      list1(q_rat),
      num_add(num_mul(cadr(x), b), num_mul(cadr(y), a)),
      num_mul(a, b),
    ),
  )
}

///|
/// *RED1 is called from SIMPLIFYA to reduce and simplify a Maxima rational
/// number.
fn n_starred1(x : Value) -> Value raise {
  if member(q_simp, cdar(x)).truthy() {
    if symval(q_d_float).truthy() {
      fpcofrat(x)
    } else {
      x
    }
  } else {
    n_starred(cadr(x), caddr(x))
  }
}

///|
/// *RED reduces the numerator N and the denominator D and returns a
/// simplified Maxima rational number.
fn n_starred(n : Value, d : Value) -> Value raise {
  if zerop(n) {
    Fix(0L)
  } else if equal(d, Fix(1L)) {
    n
  } else {
    let u = num_gcd(n, d)
    let mut n = num_truncate(n, b=u).0
    let mut d = num_truncate(d, b=u).0
    if minusp(d) {
      n = num_neg(n)
      d = num_neg(d)
    }
    if equal(d, Fix(1L)) {
      n
    } else if symval(q_d_float).truthy() {
      fpcofrat1(n, d)
    } else {
      list3(list2(q_rat, q_simp), n, d)
    }
  }
}

///|
fn num1(a : Value) -> Value raise {
  if numberp(a) {
    a
  } else {
    cadr(a)
  }
}

///|
fn denom1(a : Value) -> Value raise {
  if numberp(a) {
    Fix(1L)
  } else {
    caddr(a)
  }
}

///|
/// TIMESK multiplies two Maxima numbers and returns a simplified Maxima
/// number. X and Y are assumed to be already reduced.
fn timesk(x : Value, y : Value) -> Value raise {
  if equal(x, Fix(1L)) {
    y
  } else if equal(y, Fix(1L)) {
    x
  } else if numberp(x) && numberp(y) {
    num_mul(x, y)
  } else if d_bfloatp(x).truthy() || d_bfloatp(y).truthy() {
    d_bfloat(mk(q_mtimes, [x, y]))
  } else if floatp(x) {
    num_mul(x, fpcofrat(y))
  } else if floatp(y) {
    num_mul(y, fpcofrat(x))
  } else {
    timeskl(x, y)
  }
}

///|
/// TIMESKL takes one or two Maxima rational numbers, one argument can be an
/// integer number.
fn timeskl(x : Value, y : Value) -> Value raise {
  let u = n_starred(num1(x), denom1(y))
  let v = n_starred(num1(y), denom1(x))
  let g : Value = if equal(u, Fix(0L)) || equal(v, Fix(0L)) {
    Fix(0L)
  } else if equal(v, Fix(1L)) {
    u
  } else if numberp(u) && numberp(v) {
    num_mul(u, v)
  } else {
    list3(
      list2(q_rat, q_simp),
      num_mul(num1(u), num1(v)),
      num_mul(denom1(u), denom1(v)),
    )
  }
  if numberp(g) {
    g
  } else if equal(caddr(g), Fix(1L)) {
    cadr(g)
  } else if symval(q_d_float).truthy() {
    fpcofrat(g)
  } else {
    g
  }
}

///|
/// Floating Point Conversion OF RATional number routine.
fn fpcofrat(ratno : Value) -> Value raise {
  fpcofrat1(cadr(ratno), caddr(ratno))
}

///|
fn fpcofrat1(nu : Value, d : Value) -> Value raise {
  lfloat(num_div(nu, d))
}

///|
/// Computes X^Y, where X is Maxima number and Y an integer.
fn expta(x : Value, y : Value) -> Value raise {
  if equal(y, Fix(1L)) {
    x
  } else if numberp(x) {
    exptb(x, num1(y))
  } else if d_bfloatp(x).truthy() {
    d_bfloat(mk(q_mexpt, [x, y]))
  } else if minusp(num1(y)) {
    n_starred(
      exptb(caddr(x), num_neg(num1(y))),
      exptb(cadr(x), num_neg(num1(y))),
    )
  } else {
    n_starred(exptb(cadr(x), num1(y)), exptb(caddr(x), num1(y)))
  }
}

///|
fn simp__float_overflow() -> LispError {
  LispError::Condition(
    intern("floating-point-overflow"),
    "arithmetic error FLOATING-POINT-OVERFLOW signalled",
    Nil,
  )
}

///|
/// Is E a CL ARITHMETIC-ERROR condition?
fn simp__arithmetic_error_p(e : Error) -> Bool {
  match e {
    LispError::Condition(s, _, _) =>
      s.name == "division-by-zero" ||
      s.name == "floating-point-overflow" ||
      s.name == "floating-point-underflow" ||
      s.name == "floating-point-inexact" ||
      s.name == "floating-point-invalid-operation" ||
      s.name == "arithmetic-error"
    _ => false
  }
}

///|
/// Computes A^B, where A is a float or an integer number and B is an
/// integer number.
fn exptb(a : Value, b : Value) -> Value raise {
  let result = if equal(a, symval(q_p_e_val)) {
    // Make B a float so we'll get double-precision result.
    lexp(lfloat(b))
  } else if floatp(a) || !minusp(b) {
    expt(a, b)
  } else {
    n_starred(Fix(1L), expt(a, num_neg(b)))
  }
  if float_inf_p(result).truthy() {
    // needed for gcl and sbcl - (sometimes) no trap of overflow
    raise simp__float_overflow()
  }
  result
}

///|
/// Implementation of the simplifier for the "+" operator.
fn simplus(x : Value, w : Value, z : Value) -> Value raise {
  if cdr(x) is Nil {
    return Fix(0L)
  }
  let check = x
  let mut x = x
  let mut w = w
  let mut res : Value = Nil
  let mut eqnflag : Value = Nil
  let mut matrixflag : Value = Nil
  let mut sumflag : Value = Nil
  while true {
    // start
    x = cdr(x)
    if x is Nil {
      break
    }
    w = if z.truthy() { car(x) } else { simplifya(car(x), Nil) }
    let mut add_it = true
    while true {
      // st1
      if atom(w) {
        ()
      } else if eq(caar(w), q_mrat) {
        if eqnflag.truthy() ||
          matrixflag.truthy() ||
          (sumflag.truthy() && !member(q_trunc, cdar(w)).truthy()) ||
          spsimpcases(cdr(x), w).truthy() {
          w = ratdisrep(w)
          continue
        } else {
          // Bind VARLIST and GENVAR so kernels from this
          // conversion don't accumulate in the global table.
          // The MRAT returned carries its own copies.
          let w1 = w
          let x1 = x
          let res1 = res
          return with_specials(
            [(q_varlist, symval(q_varlist)), (q_genvar, symval(q_genvar))],
            () => ratf(
              cons(
                list1(q_mplus),
                nconc(mapcar(a => simplify(a), cons(w1, cdr(x1))), cdr(res1)),
              ),
            ),
          )
        }
      } else if eq(caar(w), q_mequal) {
        eqnflag = if !eqnflag.truthy() {
          w
        } else {
          list3(
            car(eqnflag),
            add2(cadr(eqnflag), cadr(w)),
            add2(caddr(eqnflag), caddr(w)),
          )
        }
        add_it = false
      } else if eq(caar(w), q_mlist) || eq(caar(w), q_d_matrix) {
        matrixflag = if !matrixflag.truthy() {
          w
        } else if (
            symval(q_d_doallmxops).truthy() ||
            symval(q_d_domxmxops).truthy() ||
            symval(q_d_domxplus).truthy() ||
            (eq(caar(w), q_mlist) && d_listp(matrixflag).truthy())
          ) &&
          (!eq(caar(w), q_mlist) || symval(q_d_listarith).truthy()) {
          addmx(matrixflag, w)
        } else {
          res = pls(w, res)
          matrixflag
        }
        add_it = false
      } else if eq(caar(w), q_p_sum) {
        sumflag = t
        res = sumpls(w, res)
        w = car(res)
        res = cdr(res)
      }
      break
    }
    if add_it {
      res = pls(w, res)
    }
  }
  // end
  res = testp(res)
  if matrixflag.truthy() {
    res = if (
        d_listp(matrixflag).truthy() ||
        symval(q_d_doallmxops).truthy() ||
        symval(q_d_doscmxplus).truthy() ||
        symval(q_d_doscmxops).truthy()
      ) &&
      (!d_listp(matrixflag).truthy() || symval(q_d_listarith).truthy()) {
      mxplusc(res, matrixflag)
    } else {
      testp(pls(matrixflag, pls(res, Nil)))
    }
  }
  res = eqtest(res, check)
  if eqnflag.truthy() {
    list3(car(eqnflag), add2(cadr(eqnflag), res), add2(caddr(eqnflag), res))
  } else {
    res
  }
}

///|
/// TESTP checks the result of PLS to get a valid Maxima mplus-expression.
fn testp(x : Value) -> Value raise {
  if atom(x) {
    Fix(0L)
  } else if cddr(x) is Nil {
    cadr(x)
  } else if zerop1(cadr(x)).truthy() {
    if cdddr(x) is Nil {
      caddr(x)
    } else {
      rplacd(x, cddr(x))
    }
  } else {
    x
  }
}

///|
/// PLS adds the argument X into the form OUT. If OUT is NIL a form
/// ((mplus) 0 X) is initialized, if X is an expression or a symbol,
/// or ((mplus) X), if X is a number. Numbers are added to the first
/// term <number> of the form. Any other symbol or expression is added
/// into the canonical ordered list of arguments.
fn pls(x : Value, out : Value) -> Value raise {
  let b = bind(q_ear_plusflag, Nil)
  defer unbind(b)
  let mut x = x
  if mtimesp(x).truthy() {
    x = testtneg(x)
  }
  if out is Nil {
    // Initialize a form like ((mplus) <number> expr)
    return cons(
      list1(q_mplus),
      if mnump(x).truthy() {
        list1(x)
      } else if !mplusp(x).truthy() {
        list2(Fix(0L), if atom(x) { x } else { copy_list(x) })
      } else if mnump(cadr(x)).truthy() {
        copy_list(cdr(x))
      } else {
        cons(Fix(0L), copy_list(cdr(x)))
      },
    )
  }
  if mnump(x).truthy() {
    // Add a number into the first term of the list out.
    return cons(
      list1(q_mplus),
      if mnump(cadr(out)).truthy() {
        cons(addk(cadr(out), x), cddr(out))
      } else {
        cons(x, cdr(out))
      },
    )
  }
  if !mplusp(x).truthy() {
    plusin(x, cdr(out)) |> ignore
  } else {
    // At this point we have a mplus expression as argument x. The following
    // code assumes that the argument x is already simplified and the terms
    // are in a canonical order.
    // First we add the number to the first term of the list out.
    let n = if mnump(cadr(x)).truthy() {
      x = cdr(x)
      car(x)
    } else {
      Fix(0L)
    }
    rplaca(
      cdr(out),
      addk(if mnump(cadr(out)).truthy() { cadr(out) } else { Fix(0L) }, n),
    )
    |> ignore
    // Initialize fm with the list of terms and start the loop to add the
    // terms of an mplus expression into the list out.
    let mut fm = cdr(out)
    while true {
      x = cdr(x)
      if x is Nil {
        break
      }
      // The return value of PLUSIN is a list, where the first element is
      // the added argument and the rest are the terms which follow the
      // added argument.
      fm = plusin(car(x), fm)
    }
  }
  // end
  if !symval(q_ear_plusflag).truthy() {
    return out
  }
  set(q_ear_plusflag, Nil) |> ignore // handles e.g. a+b+3*(a+b)-2*(a+b)
  // *PLUSFLAG* is set by PLUSIN to indicate that a mplus expression is
  // part of the result. For this case go again through the terms of the
  // result and add any term of the mplus expression into the list out.
  let mut fm = cdr(out) // a
  while true {
    // loop
    if mplusp(cadr(fm)).truthy() {
      x = cadr(fm)
      rplacd(fm, cddr(fm)) |> ignore
      pls(x, out) |> ignore
      fm = cdr(out) // go a
      continue
    }
    fm = cdr(fm)
    if cdr(fm) is Nil {
      return out
    }
  }
  out
}

///|
priv enum SimpPlusinLbl {
  Start
  Gr
  Equ
  Del
  Equt
  Equtm
  Equt2
  Check
}

///|
/// Adds X into running list of additive terms FM. The routine modifies
/// the argument FM destructively; the return value is a part of the list FM,
/// which starts at the place where the calling routine (PLS) can safely
/// resume scanning to insert subsequent, canonically sorted terms.
fn plusin(x : Value, fm : Value) -> Value raise {
  let mut x = x
  let mut fm = fm
  let mut x1 : Value = Nil
  let mut x2 : Value = Nil
  let mut flag : Value = Nil
  let mut check : Value = Nil
  let mut v : Value = Fix(1L)
  let mut w : Value = Fix(1L)
  let mut xnew : Value = Nil
  let mut a : Value = Nil
  let mut merged : Value = Nil
  let mut in_cluster_p = false
  let mut canonical_insert_fm : Value = Nil
  let mut cluster_start_fm : Value = Nil
  if mtimesp(x).truthy() {
    check = x
    if mnump(cadr(x)).truthy() {
      w = cadr(x)
      x = cddr(x)
    } else {
      x = cdr(x)
    }
  } else {
    x = list1(x)
  }
  x1 = if cdr(x) is Nil { car(x) } else { cons(list1(q_mtimes), x) }
  xnew = list_star([list1(q_mtimes), w, x])
  // Remember whether X1 is an MEXPT with an integer base.
  // In that case, it can potentially merge with an already existing
  // term in such a way that the resulting term needs to be moved to a
  // different place to maintain canonical ordering.
  let int_base_expt_p = mexptp(x1).truthy() && integerp(cadr(x1))
  // Remember the base of the power at the end of X, if it is an integer.
  // All terms of the sum which end in a power of that base form one
  // uninterrupted cluster, because GREAT compares products by their last
  // factor (ORDLIST) and powers of different bases by their bases alone
  // (ORDMEXPT).
  let cluster_base : Value = {
    let f = last_factor(x1)
    if mexptp(f).truthy() && integerp(cadr(f)) {
      cadr(f)
    } else {
      Nil
    }
  }
  // `or cluster-start-fm X`
  fn ret(cs : Value, y : Value) -> Value {
    if cs.truthy() {
      cs
    } else {
      y
    }
  }

  let mut lbl = SimpPlusinLbl::Start
  while true {
    match lbl {
      Start => {
        // A nested MPLUS expression is a term which PLS still has to add
        // into the sum again (see EQUT and EQUTM). Step over it.
        if !(cdr(fm) is Nil) && mplusp(cadr(fm)).truthy() {
          fm = cdr(fm)
          continue
        }
        in_cluster_p = cluster_base.truthy() &&
          !(cdr(fm) is Nil) && {
            let f = last_factor(cadr(fm))
            mexptp(f).truthy() && equal(cadr(f), cluster_base)
          }
        if in_cluster_p && cluster_start_fm is Nil {
          cluster_start_fm = fm
        }
        if cdr(fm) is Nil {
          ()
        } else if cdr(x) is Nil &&
          alike1(x1, cadr(fm)).truthy() &&
          !int_base_expt_p {
          // A power of an integer is left to the merge below.
          lbl = Equ
          continue
        } else if int_base_expt_p &&
          (
            {
              x2 = cadr(fm)
              mexptp(x2).truthy() && {
                v = Fix(1L)
                true
              }
            } ||
            (
              mtimesp(x2).truthy() &&
              cadddr(x2) is Nil &&
              {
                v = cadr(x2)
                mnump(v).truthy()
              } &&
              {
                x2 = caddr(x2)
                mexptp(x2).truthy()
              }
            )
          ) &&
          {
            a = cadr(x2)
            equal(a, cadr(x1))
          } &&
          integer_difference_p(caddr(x2), caddr(x1)).truthy() &&
          {
            merged = merge_power_terms(v, caddr(x2), w, caddr(x1), a)
            merged.truthy()
          } {
          // Implement the simplification of
          //   v*a^(c+n)+w*a^(c+m) -> (v*a^n+w*a^m)*a^c
          // where a and (n-m) are integers and v and w are numbers.
          x1 = merged
          lbl = Equtm
          continue
        } else if mtimesp(cadr(fm)).truthy() {
          if !(cdr(x) is Nil) && alike1(x1, cadr(fm)).truthy() {
            lbl = Equt
            continue
          } else if mnump(cadadr(fm)).truthy() &&
            alike(x, cddr(cadr(fm))).truthy() {
            flag = t // found common factor
            lbl = Equt
            continue
          } else if great(xnew, cadr(fm)).truthy() {
            lbl = Gr
            continue
          }
        } else if great(x1, cadr(fm)).truthy() {
          lbl = Gr
          continue
        }
        // This is the place where X belongs in the canonically ordered sum,
        // but X can still merge with a power further down in the same
        // cluster. Remember this place and pass them by.
        if int_base_expt_p && in_cluster_p {
          if canonical_insert_fm is Nil {
            canonical_insert_fm = fm
          }
          fm = cdr(fm)
          continue
        }
        xnew = eqtest(testt(xnew), if check.truthy() {
          check
        } else {
          list1(list1(q_foo))
        })
        if canonical_insert_fm.truthy() {
          fm = canonical_insert_fm
        }
        fm = cdr(rplacd(fm, cons(xnew, cdr(fm))))
        return ret(cluster_start_fm, fm)
      }
      Gr => {
        fm = cdr(fm)
        lbl = Start
      }
      Equ => {
        if equal(w, Fix(-1L)) {
          x1 = list_star([list2(q_mtimes, q_simp), Fix(0L), x])
          lbl = Equt2
          continue
        }
        // Call muln to get a simplified product.
        x1 = muln(cons(addk(Fix(1L), w), x), t)
        if mtimesp(x1).truthy() {
          x1 = testtneg(x1)
        }
        lbl = Equtm
      }
      Del => {
        if !mtimesp(cadr(fm)).truthy() {
          lbl = Check
          continue
        } else if onep(cadadr(fm)).truthy() {
          // Do this simplification for an integer 1, not for 1.0 and 1.0b0
          rplacd(cadr(fm), cddr(cadr(fm))) |> ignore
          return ret(cluster_start_fm, cdr(fm))
        } else if !zerop1(cadadr(fm)).truthy() {
          return ret(cluster_start_fm, cdr(fm))
        } else if (
            !symval(q_d_listarith).truthy() || !symval(q_d_doallmxops).truthy()
          ) &&
          mxorlistp(caddr(cadr(fm))).truthy() {
          // Handle the multiplication with a zero.
          rplacd(fm, cons(constmx(Fix(0L), caddr(cadr(fm))), cddr(fm)))
          |> ignore
          return ret(cluster_start_fm, fm)
        }
        // (cadadr fm) is zero. If the first term of fm is a number,
        // add it to preserve the type.
        if mnump(car(fm)).truthy() {
          rplaca(fm, addk(car(fm), cadadr(fm))) |> ignore
        }
        rplacd(fm, cddr(fm)) |> ignore
        return ret(cluster_start_fm, fm)
      }
      Equt => {
        // Call muln to get a simplified product.
        x1 = muln(
          cons(addk(w, if flag.truthy() { cadadr(fm) } else { Fix(1L) }), x),
          t,
        )
        // Make a mplus expression to guarantee that x1 is added again into
        // the sum
        x1 = list2(list1(q_mplus), x1)
        lbl = Equt2
      }
      Equtm => {
        // A merged power of an integer can be structurally different from
        // the term it replaces. Make an MPLUS expression of it, so that it
        // is added into the sum again from the start.
        if int_base_expt_p &&
          !zerop1(x1).truthy() &&
          !alike1(last_factor(x1), last_factor(cadr(fm))).truthy() {
          x1 = list2(list1(q_mplus), x1)
        }
        lbl = Equt2
      }
      Equt2 => {
        x1 = if zerop1(x1).truthy() {
          list_star([list1(q_mtimes), x1, x])
        } else if mtimesp(x1).truthy() {
          testtneg(x1)
        } else {
          x1
        }
        rplaca(cdr(fm), x1) |> ignore
        if !mtimesp(cadr(fm)).truthy() {
          lbl = Check
          continue
        }
        if onep(cadadr(fm)).truthy() && flag.truthy() && cdddr(cadr(fm)) is Nil {
          // Do this simplification for an integer 1, not for 1.0 and 1.0b0
          rplaca(cdr(fm), caddr(cadr(fm))) |> ignore
          lbl = Check
          continue
        }
        lbl = Del
      }
      Check => {
        if mplusp(cadr(fm)).truthy() {
          set(q_ear_plusflag, t) |> ignore // A nested mplus expression
        }
        return ret(cluster_start_fm, cdr(fm))
      }
    }
  }
  Nil
}

///|
/// Implements the simplification
///   v*a^(c+n)+w*a^(c+m) -> (v*a^n+w*a^m)*a^c
/// for PLUSIN. The exponents are split into an integer part and a
/// remainder; the remainder stays in the power. The result is NIL if the
/// arithmetic ran out of range.
fn merge_power_terms(
  v : Value,
  e1 : Value,
  w : Value,
  e2 : Value,
  a : Value,
) -> Value raise {
  let n = if mplusp(e1).truthy() && mnump(cadr(e1)).truthy() {
    cadr(e1)
  } else if mnump(e1).truthy() {
    e1
  } else {
    Fix(0L)
  }
  let m = if mplusp(e2).truthy() && mnump(cadr(e2)).truthy() {
    cadr(e2)
  } else if mnump(e2).truthy() {
    e2
  } else {
    Fix(0L)
  }
  let c0 = sub(e1, n)
  let body = () => {
    let mut c = c0
    if integerp(n) {
      // The simple case:
      // n and m are integers and the result is (v*a^n+w*a^m)*a^c.
      mul2(addk(timesk(v, exptb(a, n)), timesk(w, exptb(a, m))), power(a, c))
    } else {
      let (n1_, d1) = num_truncate(num1(n), b=denom1(n))
      let (n2_, d2) = num_truncate(num1(m), b=denom1(m))
      let mut n1 = n1_
      let mut n2 = n2_
      if equal(d1, d2) {
        // Case I: -> (v*a^n1+w*a^n2)*a^(c+d1/r)
        c = add2(c, div(d1, denom1(n)))
      } else if minusp(d2) {
        // Case II: d2 is negative, adjust n1.
        n1 = add2(n1, div(sub(d1, d2), denom1(n)))
        c = add2(c, div(d2, denom1(n)))
      } else if minusp(d1) {
        // Case II: d1 is negative, adjust n2.
        n2 = add2(n2, div(sub(d2, d1), denom1(n)))
        c = add2(c, div(d1, denom1(n)))
      } else {
        // This clause should never be reached.
        merr("Internal error in simplus.", []) |> ignore
      }
      mul2(addk(timesk(v, exptb(a, n1)), timesk(w, exptb(a, n2))), power(a, c))
    }
  }
  body() catch {
    e => if simp__arithmetic_error_p(e) { Nil } else { raise e }
  }
}

// Routines to add matrices

///|
fn mxplusc(sc : Value, mx : Value) -> Value raise {
  if mplusp(sc).truthy() {
    let sc = partition_ns(cdr(sc))
    if car(sc) is Nil {
      cons(list1(q_mplus), cons(mx, cadr(sc)))
    } else if !(cadr(sc) is Nil) {
      cons(
        list1(q_mplus),
        cons(
          simplify(outermap1(list([q_mplus, cons(list1(q_mplus), car(sc)), mx]))),
          cadr(sc),
        ),
      )
    } else {
      simplify(outermap1(list([q_mplus, cons(list1(q_mplus), car(sc)), mx])))
    }
  } else if !scalar_or_constant_p(sc, symval(q_d_assumescalar)).truthy() {
    testp(pls(mx, pls(sc, Nil)))
  } else {
    simplify(outermap1(list([q_mplus, sc, mx])))
  }
}

///|
fn partition_ns(x : Value) -> Value raise {
  // SP = scalar part, NSP = nonscalar part
  let mut sp : Value = Nil
  let mut nsp : Value = Nil
  for z in x.iter() {
    if scalar_or_constant_p(z, symval(q_d_assumescalar)).truthy() {
      sp = cons(z, sp)
    } else {
      nsp = cons(z, nsp)
    }
  }
  list2(nreverse(sp), nreverse(nsp))
}

///|
fn conformable_matrices_p(x1 : Value, x2 : Value) -> Value raise {
  lbool(
    length(x1) == length(x2) &&
    (
      (rest(x1) is Nil && rest(x2) is Nil) ||
      length(second(x1)) == length(second(x2))
    ),
  )
}

///|
fn addmx(x1 : Value, x2 : Value) -> Value raise {
  // When maperror = true, ensure that arguments are conformable, in the
  // sense of not causing an error in fullmap.
  if symval(q_d_maperror).truthy() {
    let ok = if d_listp(x1).truthy() && d_listp(x2).truthy() {
      length(x1) == length(x2)
    } else if d_matrixp(x1).truthy() && d_matrixp(x2).truthy() {
      conformable_matrices_p(x1, x2).truthy()
    } else {
      // One argument is a list and the other is a matrix.
      // Test for (length of list) = (number of rows of matrix).
      length(x1) == length(x2)
    }
    if !ok {
      merr("addition: non-conformable list or matrix arguments.", []) |> ignore
    }
  }
  with_specials(
    [(q_d_doscmxops, t), (q_d_domxmxops, t), (q_d_listarith, t)],
    () => simplify(fmapl1(q_mplus, list2(x1, x2))),
  )
}

///|
fn init_simp() -> Unit raise {
  putprop(q_d_lognegint, t, q_evflag) |> ignore
  set(q_machine_mantissa_precision, Fix(53L)) |> ignore
  putprop(q_mnctimes, t, q_associative) |> ignore
  putprop(q_lambda, t, q_lisp_no_simp) |> ignore
  for x in [q_mplus, q_mtimes, q_mnctimes, q_mexpt, q_mncexpt, q_p_sum] {
    setf_get(x, q_msimpind, cons(x, list1(q_simp))) |> ignore
  }
  // operators properties
  let ops = [
    (q_mplus, q_simplus),
    (q_mtimes, q_simptimes),
    (q_mncexpt, q_simpncexpt),
    (q_mminus, q_simpmin),
    (q_mfactorial, q_simpfact),
    (q_mnctimes, q_simpnct),
    (q_mquotient, q_simpquot),
    (q_mexpt, q_simpexpt),
    (q_p_derivative, q_simpderiv),
    (q_p_signum, q_simpsignum),
    (q_p_integrate, q_simpinteg),
    (q_p_limit, q_simp_limit),
    (q_bigfloat, q_simpbigfloat),
    (q_lambda, q_simplambda),
    (q_mdefine, q_simpmdef),
    (q_mqapply, q_simpmqapply),
    (q_p_sum, q_simpsum),
    (q_p_product, q_simpprod),
    (q_d_matrix, q_simpmatrix),
    (q_p_matrix, q_simpmatrix),
  ]
  for p in ops {
    setf_get(p.0, q_operators, p.1) |> ignore
  }
  putprop(q_d_equal, t, q_binary) |> ignore
  putprop(q_d_notequal, t, q_binary) |> ignore
  // The log function distributes over lists, matrices, and equations
  putprop(q_p_log, list([q_mlist, q_d_matrix, q_mequal]), q_distribute_over)
  |> ignore
  // def-simplifier log: its properties are installed by the registry.
  // Implementation of the Square root function
  putprop(q_d_sqrt, q_p_sqrt, q_verb) |> ignore
  putprop(q_d_sqrt, q_p_sqrt, q_alias) |> ignore
  putprop(q_p_sqrt, q_d_sqrt, q_noun) |> ignore
  putprop(q_p_sqrt, q_d_sqrt, q_reversealias) |> ignore
  putprop(q_p_sqrt, q_simp_sqrt, q_operators) |> ignore
  // Implementation of the abs function.
  putprop(q_d_abs, q_mabs, q_alias) |> ignore
  putprop(q_d_abs, q_mabs, q_verb) |> ignore
  putprop(q_mabs, q_d_abs, q_reversealias) |> ignore
  putprop(q_mabs, q_d_abs, q_noun) |> ignore
  putprop(q_mabs, list([q_mlist, q_d_matrix, q_mequal]), q_distribute_over)
  |> ignore
  putprop(q_mabs, q_simpabs, q_operators) |> ignore
  putprop(q_mabs, list2(list1(q_x), q_abs_integral), q_integral) |> ignore
  // Implementation of the Exp function.
  putprop(q_d_exp, q_p_exp, q_verb) |> ignore
  putprop(q_d_exp, q_p_exp, q_alias) |> ignore
  putprop(q_p_exp, q_d_exp, q_noun) |> ignore
  putprop(q_p_exp, q_d_exp, q_reversealias) |> ignore
  putprop(q_p_exp, q_simp_exp, q_operators) |> ignore
  putprop(q_p_signum, list([q_mlist, q_d_matrix, q_mequal]), q_distribute_over)
  |> ignore
  // def-simplifier signum (later in simp.lisp) replaces the SIMPSIGNUM
  // operators property set above.
  putprop(q_p_signum, q_simp__pctsignum, q_operators) |> ignore
}
