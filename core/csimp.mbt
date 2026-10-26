// Port of src/csimp.lisp: $demoivre, $partition, NUMDEN, FMT, $rhs/$lhs,
// %ESPECIAL (exp of rational multiples of %i*%pi) and related helpers.

///|
fn d_demoivre(exp_ : Value) -> Value raise {
  with_special(q_d_exponentialize, Nil, () => {
    if atom(exp_) {
      return exp_
    }
    if eq(caar(exp_), q_mexpt) && eq(cadr(exp_), q_d__pcte) {
      let nexp = demoivre(caddr(exp_))
      if nexp.truthy() {
        return nexp
      }
    }
    recur_apply(q_d_demoivre, exp_)
  })
}

///|
fn demoivre(l0 : Value) -> Value raise {
  if symval(q_d_exponentialize).truthy() {
    merr(
      "demoivre: 'demoivre' and 'exponentialize' cannot both be true.",
      [],
    )
  } else {
    let l = islinear(l0, q_d__pcti)
    if l.truthy() && !equal(car(l), Fix(0L)) {
      m_star(
        list2(
          m_hat(q_d__pcte, cdr(l)),
          m_plus(
            list2(
              list2(list1(q_p_cos), car(l)),
              m_star(list2(q_d__pcti, list2(list1(q_p_sin), car(l)))),
            ),
          ),
        ),
      )
    } else {
      Nil
    }
  }
}

///|
/// If expr is of the form a*var1+b where a is freeof var1 then (a . b) is
/// returned else nil.
fn islinear(expr : Value, var1 : Value) -> Value raise {
  let a = with_special(q_ear_islinp, t, () => sdiff(expr, var1))
  if freeof(var1, a).truthy() {
    let b = no_err_sub_var(Fix(0L), expr, var1)
    if eq(b, t) {
      Nil
    } else {
      cons(a, b)
    }
  } else {
    Nil
  }
}

///|
fn d_partition(e : Value, var1 : Value) -> Value raise {
  let e = mratcheck(e)
  let var1 = getopr(var1)
  if d_listp(e).truthy() {
    let mut l1 = Value::Nil
    let mut l2 = Value::Nil
    for y in cdr(e).iter() {
      let x = mratcheck(y)
      if free(x, var1).truthy() {
        l1 = cons(x, l1)
      } else {
        l2 = cons(x, l2)
      }
    }
    list([
      list2(q_mlist, q_simp),
      cons(list2(q_mlist, q_simp), nreverse(l1)),
      cons(list2(q_mlist, q_simp), nreverse(l2)),
    ])
  } else if mplusp(e).truthy() {
    let cv = partition(e, var1, Fix(0L))
    list([list2(q_mlist, q_simp), car(cv), cdr(cv)])
  } else if mtimesp(e).truthy() {
    let cv = partition(e, var1, Fix(1L))
    list([list2(q_mlist, q_simp), car(cv), cdr(cv)])
  } else {
    merr(
      "partition: first argument must be a list or '+' or '*' expression; found ~M",
      [e],
    )
  }
}

///|
/// Apply PREDICATE to each element in the sequence SEQ and return
///   (VALUES YES NO),
/// where YES and NO are lists consisting of elements for which PREDICATE is
/// true or false, respectively. The order of elements is reversed compared
/// to SEQ.
fn partition_by(predicate : Value, seq : Value) -> (Value, Value) raise {
  let mut yes = Value::Nil
  let mut no = Value::Nil
  for x in seq.iter() {
    if funcall(predicate, [x]).truthy() {
      yes = cons(x, yes)
    } else {
      no = cons(x, no)
    }
  }
  (yes, no)
}

///|
/// Partition an expression, EXP, into terms that contain VAR1 and terms
/// that don't contain VAR1. EXP is either considered as a product or a sum
/// (for which you should pass K = 1 or 0, respectively).
fn partition(exp_ : Value, var1 : Value, k : Value) -> Value raise {
  let op = if num_eq(k, Fix(0L)) { q_mplus } else { q_mtimes }
  let exp_op : Value = if atom(exp_) { Nil } else { caar(exp_) }
  if alike1(exp_, var1).truthy() {
    // Exit immediately if exp = var1
    cons(k, exp_)
  } else if !eq(exp_op, op) {
    // If we have the wrong operation then the expression is either entirely
    // constant or entirely variable.
    if freeof(var1, exp_).truthy() {
      cons(exp_, k)
    } else {
      cons(k, exp_)
    }
  } else {
    // Otherwise, we want to partition the arguments into constant and
    // variable.
    let (constant, variable) = partition_by(
      lfunc("partition-lambda", args => freeof(var1, arg(args, 0))),
      cdr(exp_),
    )
    let header = if memq(q_simp, cdar(exp_)).truthy() {
      get(op, q_msimpind)
    } else {
      list1(op)
    }
    cons(
      if constant is Nil {
        k
      } else if cdr(constant) is Nil {
        car(constant)
      } else {
        cons(header, nreverse(constant))
      },
      if variable is Nil {
        k
      } else if cdr(variable) is Nil {
        car(variable)
      } else {
        cons(header, nreverse(variable))
      },
    )
  }
}

///|
fn numden(e0 : Value) -> (Value, Value) raise {
  with_special(q_varlist, list1(symval(q_var)), () => {
    let e = fmt(e0)
    newvar(e) |> ignore
    let e = cdr(ratrep_star(e))
    set(q_dn_star, simplifya(pdis(ratdenominator(e)), Nil)) |> ignore
    set(q_nn_star, simplifya(pdis(ratnumerator(e)), Nil)) |> ignore
  })
  (symval(q_nn_star), symval(q_dn_star))
}

///|
/// Like NUMDEN but dependency on VAR is explicit.  Use this instead of
/// NUMDEN if possible.  Also, we do not set the special variables DN* and
/// NN*.  The callers are responsible for doing that, now.
fn numden_var(e0 : Value, var1 : Value) -> (Value, Value) raise {
  with_special(q_varlist, list1(var1), () => {
    let e = fmt(e0)
    newvar(e) |> ignore
    let e = cdr(ratrep_star(e))
    let dn = simplifya(pdis(ratdenominator(e)), Nil)
    let nn = simplifya(pdis(ratnumerator(e)), Nil)
    (nn, dn)
  })
}

///|
fn fmt(exp_ : Value) -> Value raise {
  with_special(q_nn_star, Nil, () => if atom(exp_) {
    exp_
  } else if mnump(exp_).truthy() {
    exp_
  } else if eq(caar(exp_), q_mexpt) {
    if mnump(caddr(exp_)).truthy() && eq(d_sign(caddr(exp_)), q_d_neg) {
      list([
        list1(q_mquotient),
        Fix(1L),
        if equal(caddr(exp_), Fix(-1L)) {
          fmt(cadr(exp_))
        } else {
          list([
            list1(caar(exp_)),
            fmt(cadr(exp_)),
            timesk(Fix(-1L), caddr(exp_)),
          ])
        },
      ])
    } else if atom(caddr(exp_)) {
      list([list1(caar(exp_)), fmt(cadr(exp_)), caddr(exp_)])
    } else if {
        set(q_nn_star, sratsimp(caddr(exp_))) |> ignore
        let nn = symval(q_nn_star)
        mtimesp(nn).truthy() &&
        mnump(cadr(nn)).truthy() &&
        eq(d_sign(cadr(nn)), q_d_neg)
      } {
      let nn = symval(q_nn_star)
      list([
        list1(q_mquotient),
        Fix(1L),
        list([
          list1(caar(exp_)),
          fmt(cadr(exp_)),
          if equal(cadr(nn), Fix(-1L)) {
            cons(list1(q_mtimes), cddr(nn))
          } else {
            neg(nn)
          },
        ]),
      ])
    } else if eq(caar(symval(q_nn_star)), q_mplus) {
      fmt(spexp(cdr(symval(q_nn_star)), cadr(exp_)))
    } else {
      cons(ncons(caar(exp_)), mapcar(x => fmt(x), cdr(exp_)))
    }
  } else {
    cons(delsimp(car(exp_)), mapcar(x => fmt(x), cdr(exp_)))
  })
}

///|
fn spexp(expl : Value, dn_star : Value) -> Value raise {
  cons(list1(q_mtimes), mapcar(e => list([list1(q_mexpt), dn_star, e]), expl))
}

///|
fn subin(y : Value, x : Value) -> Value raise {
  if among(symval(q_var), x) is Nil {
    x
  } else {
    maxima_substitute(y, symval(q_var), x)
  }
}

///|
/// Like SUBIN but dependency on VAR is explicit.  Use this instead when
/// possible.
fn subin_var(y : Value, x : Value, ivar : Value) -> Value raise {
  if among(ivar, x) is Nil {
    x
  } else {
    maxima_substitute(y, ivar, x)
  }
}

// Right-hand side (rhs) and left-hand side (lhs) of binary infix
// expressions.  These are unambiguous for relational operators, some other
// built-in infix operators, and user-defined infix operators (declared by
// the infix function).

///|
fn csimp__infix_op_p(op : Value) -> Bool raise {
  let ops = [
    // < <= = # equal notequal >= >
    "mlessp", "mleqp", "mequal", "mnotequal", "$equal", "$notequal", "mgeqp", "mgreaterp",
    "%mlessp", "%mleqp", "%mequal", "%mnotequal", "%equal", "%notequal", "%mgeqp",
    "%mgreaterp",
    // := ::= : :: ->
    "mdefine", "mdefmacro", "msetq", "mset", "marrow", "%mdefine", "%mdefmacro",
    "%msetq", "%mset", "%marrow",
  ]
  for o in ops {
    if eq(op, sym(o)) {
      return true
    }
  }
  // This test catches user-defined infix operators.
  eq(get(op, q_led), q_parse_infix)
}

///|
/// defmfun $rhs (defined inside a LET in csimp.lisp).
fn d_rhs(rel : Value) -> Value raise {
  if atom(rel) {
    Fix(0L)
  } else if csimp__infix_op_p(caar(rel)) {
    caddr(rel)
  } else {
    Fix(0L)
  }
}

///|
/// defmfun $lhs (defined inside a LET in csimp.lisp).
fn d_lhs(rel : Value) -> Value raise {
  if atom(rel) {
    rel
  } else if csimp__infix_op_p(caar(rel)) {
    cadr(rel)
  } else {
    rel
  }
}

///|
fn ratgreaterp(x : Value, y : Value) -> Value raise {
  if ratnump(x).truthy() && ratnump(y).truthy() {
    great(x, y)
  } else {
    lbool(equal(d_asksign(m_(x, a2=y)), q_d_pos))
  }
}

///|
/// Simplify the exponential function of the type exp(p/q*%i*%pi+x) using
/// the periodicity of the exponential function and special values for
/// rational numbers with a denominator q = 2, 3, 4, or 6. e is the argument
/// of the exponential function. For float and bigfloat numbers in the
/// argument e only simplify for an integer representation or a half
/// integral value.  The result is an exponential function with a
/// simplified argument.
fn p_especial(e : Value) -> Value raise {
  with_specials(
    [
      (q_varlist, Nil),
      (q_d__pctemode, Nil),
      (q_d_ratprint, Nil),
      (q_genvar, Nil),
    ],
    () => {
      let mut y = Value::Nil
      let mut k = Value::Nil
      let mut kk = Value::Nil
      let mut j = Value::Nil
      let mut ans = Value::Nil
      let early = with_specials([(q_d_keepfloat, Nil), (q_d_float, Nil)], () => {
        y = pip(d_ratcoef(e, q_d__pcti))
        if y is Nil {
          return true
        }
        // Subtract the term y*%i*%pi from the expression e.
        k = d_expand(
          add2(e, muln_([Fix(-1L), q_d__pctpi, q_d__pcti, y])),
          expop=Fix(1L),
        )
        // This is a workaround to get the type (integer, float, or
        // bigfloat) of the expression. kk must evaluate to 1, 1.0, or
        // 1.0b0.  Furthermore, if e is nonlinear, kk does not simplify to a
        // number ONE.
        kk = div(sub(d_expand(e), k), muln_([q_d__pcti, q_d__pctpi, y]))
        // Return if kk is not an integer or kk is ONE, but y not an integer
        // or a half integral value.
        if !(
            integerp(kk) || (onep1(kk).truthy() && integerp(add2(y, y)))
          ) {
          return true
        }
        j = trigred(y)
        ans = spang1(j, t)
        false
      })
      if early {
        return Nil
      }
      if among(q_p_sin, ans).truthy() {
        if equal(y, j) {
          return Nil
        } else if zerop1(k).truthy() {
          // To preverse the type we add k into the result.
          return power(q_d__pcte, muln_([q_d__pctpi, q_d__pcti, add2(k, j)]))
        } else {
          // To preserve the type we multiply kk into the result.
          return power(
            q_d__pcte,
            add2(mul2(kk, k), muln_([kk, q_d__pctpi, q_d__pcti, j])),
          )
        }
      }
      y = spang1(j, Nil)
      // To preserve the type we multiply kk into the result.
      mul2(power(q_d__pcte, mul2(kk, k)), add2(y, mul2(q_d__pcti, ans)))
    },
  )
}

///|
fn trigred(r : Value) -> Value raise {
  if numberp(r) {
    return if even(r).truthy() { Fix(0L) } else { Fix(1L) }
  }
  let mut m = cadr(r)
  let mut flag = false
  let mut eo = false
  if minusp(m) {
    m = num_neg(m)
    flag = true
  }
  let n = caddr(r)
  while num_gt(m, n) {
    m = num_sub(m, n)
    eo = !eo
  }
  let m = mk_simp(q_rat, [if flag { num_neg(m) } else { m }, n])
  if eo {
    addk(m, if flag { Fix(1L) } else { Fix(-1L) })
  } else {
    m
  }
}

///|
fn polyinx(exp_ : Value, x0 : Value, ind : Value) -> Value raise {
  with_specials(
    [
      (q_genvar, Nil),
      (q_varlist, Nil),
      (q_var, Nil),
      (q_d_ratfac, Nil),
    ],
    () => {
      set(q_var, x0) |> ignore
      if numberp(exp_) {
        return t
      } else if polyp(exp_).truthy() {
        if !ind.truthy() {
          return t
        }
      } else {
        return Nil
      }
      // on
      set(q_genvar, Nil) |> ignore
      set(q_varlist, list1(x0)) |> ignore
      newvar(exp_) |> ignore
      let exp = cdr(ratrep_star(exp_))
      if numberp(cdr(exp)) || !eq(car(last(symval(q_genvar))), cadr(exp)) {
        let x = pdis(cdr(exp))
        if eq(ind, q_leadcoef) {
          div_star(pdis(caddr(car(exp))), x)
        } else {
          let exp = car(exp)
          div_star(
            if atom(exp) {
              exp
            } else {
              pdis(list([car(exp), cadr(exp), caddr(exp)]))
            },
            x,
          )
        }
      } else {
        Nil
      }
    },
  )
}

///|
fn polyp(a : Value) -> Value raise {
  if atom(a) {
    t
  } else if memq(caar(a), list2(q_mplus, q_mtimes)).truthy() {
    for x in cdr(a).iter() {
      if !polyp(x).truthy() {
        return Nil
      }
    }
    t
  } else if eq(caar(a), q_mexpt) {
    if free(cadr(a), symval(q_var)).truthy() {
      free(caddr(a), symval(q_var))
    } else if integerp(caddr(a)) && plusp(caddr(a)) {
      polyp(cadr(a))
    } else {
      Nil
    }
  } else {
    andmapcar(
      lfunc("polyp-lambda", args => free(arg(args, 0), symval(q_var))),
      cdr(a),
    )
  }
}

///|
/// Like polyp but takes an extra arg for the variable.
fn polyp_var(a : Value, var2 : Value) -> Value raise {
  if atom(a) {
    t
  } else if memq(caar(a), list2(q_mplus, q_mtimes)).truthy() {
    for x in cdr(a).iter() {
      if !polyp_var(x, var2).truthy() {
        return Nil
      }
    }
    t
  } else if eq(caar(a), q_mexpt) {
    if free(cadr(a), var2).truthy() {
      free(caddr(a), var2)
    } else if integerp(caddr(a)) && plusp(caddr(a)) {
      polyp_var(cadr(a), var2)
    } else {
      Nil
    }
  } else {
    andmapcar(
      lfunc("polyp-var-lambda", args => free(arg(args, 0), var2)),
      cdr(a),
    )
  }
}

///|
fn pip(e0 : Value) -> Value raise {
  with_special(q_varlist, Nil, () => {
    let mut e = e0
    newvar(e) |> ignore
    if memq(q_d__pctpi, symval(q_varlist)) is Nil {
      return Nil
    }
    set(q_varlist, list1(q_d__pctpi)) |> ignore
    newvar(e) |> ignore
    // non-nil $ratfac changes form of CRE
    e = with_special(q_d_ratfac, Nil, () => cdr(ratrep_star(e)))
    let d = cdr(e)
    let mut c = Value::Nil
    if !atom(d) {
      return Nil
    } else if equal(e, cons(Fix(0L), Fix(1L))) {
      c = Fix(0L)
    } else {
      // to protect from the case where $pi disappears from the expression
      // (fix by Michel Talon)
      let genpairs = mapcar2(
        (x, y) => cons(y, x),
        symval(q_varlist),
        symval(q_genvar),
      )
      if !eq(assolike(caar(e), genpairs), q_d__pctpi) {
        return Nil
      }
      c = ptterm(cdar(e), Fix(1L))
    }
    // loop
    while true {
      if atom(c) {
        return if equal(c, Fix(0L)) {
          Nil
        } else if equal(Fix(1L), d) {
          c
        } else {
          div(c, d)
        }
      }
      c = ptterm(cdr(c), Fix(0L))
    }
    Nil
  })
}

///|
fn spang1(j0 : Value, ind : Value) -> Value raise {
  with_specials(
    [(q_d_exponentialize, Nil), (q_d_float, Nil), (q_d_keepfloat, Nil)],
    () => {
      let mut j = j0
      let mut ep = false
      if floatp(j) {
        j = maxima_rationalize(j)
        j = mk_simp(q_rat, [car(j), cdr(j)])
      }
      let mut ang = j
      if ind.truthy() {
        ()
      } else if numberp(j) {
        return if zerop(j) { Fix(1L) } else { Fix(-1L) }
      } else {
        j = trigred(
          add2_star(
            mk_simp(q_rat, [Fix(1L), Fix(2L)]),
            list([car(j), num_neg(cadr(j)), caddr(j)]),
          ),
        )
      }
      if numberp(j) {
        return Fix(0L)
      } else if mnump(j).truthy() {
        j = cdr(j)
      }
      let jis = fn(a : Int64, b : Int64) -> Bool {
        equal(j, list2(Fix(a), Fix(b)))
      }
      if jis(1L, 2L) {
        Fix(1L)
      } else if jis(-1L, 2L) {
        Fix(-1L)
      } else if jis(1L, 3L) || jis(2L, 3L) {
        div(d_sqrt(Fix(3L)), Fix(2L))
      } else if jis(-1L, 3L) || jis(-2L, 3L) {
        div(d_sqrt(Fix(3L)), Fix(-2L))
      } else if jis(1L, 6L) || jis(5L, 6L) {
        mk_simp(q_rat, [Fix(1L), Fix(2L)])
      } else if jis(-1L, 6L) || jis(-5L, 6L) {
        mk_simp(q_rat, [Fix(-1L), Fix(2L)])
      } else if jis(1L, 4L) || jis(3L, 4L) {
        div(Fix(1L), d_sqrt(Fix(2L)))
      } else if jis(-1L, 4L) || jis(-3L, 4L) {
        div(Fix(-1L), d_sqrt(Fix(2L)))
      } else {
        if mnegp(ang).truthy() {
          ang = timesk(Fix(-1L), ang)
          ep = true
        }
        ang = mk_simp(q_mtimes, [ang, q_d__pctpi])
        if ind.truthy() {
          if ep {
            mk_simp(q_mtimes, [Fix(-1L), mk_simp(q_p_sin, [ang])])
          } else {
            mk_simp(q_p_sin, [ang])
          }
        } else {
          mk_simp(q_p_cos, [ang])
        }
      }
    },
  )
}

///|
fn archk(a : Value, b : Value, v : Value) -> Value raise {
  simplify(
    if equal(a, Fix(1L)) && equal(b, Fix(1L)) {
      v
    } else if equal(b, Fix(-1L)) && equal(Fix(1L), a) {
      mk(q_mtimes, [Fix(-1L), v])
    } else if equal(Fix(1L), b) {
      mk(q_mplus, [q_d__pctpi, mk(q_mtimes, [Fix(-1L), v])])
    } else {
      mk(q_mplus, [v, mk(q_mtimes, [Fix(-1L), q_d__pctpi])])
    },
  )
}

///|
/// finds gensym coresponding to v h
fn genfind(h : Value, v : Value) -> Value raise {
  let mut varl = caddr(h)
  let mut genl = cadddr(h)
  // is car of rat form
  while !eq(car(varl), v) {
    varl = cdr(varl)
    genl = cdr(genl)
  }
  car(genl)
}

///|
fn init_csimp() -> Unit raise {
  let pairs = [
    (q_p_sin, q_p_asin),
    (q_p_cos, q_p_acos),
    (q_p_tan, q_p_atan),
    (q_p_cot, q_p_acot),
    (q_p_sec, q_p_asec),
    (q_p_csc, q_p_acsc),
    (q_p_sinh, q_p_asinh),
    (q_p_cosh, q_p_acosh),
    (q_p_tanh, q_p_atanh),
    (q_p_coth, q_p_acoth),
    (q_p_sech, q_p_asech),
    (q_p_csch, q_p_acsch),
  ]
  for p in pairs {
    putprop(p.0, p.1, q_d_inverse) |> ignore
    putprop(p.1, p.0, q_d_inverse) |> ignore
  }
  set(q_var, make_symbol("foo")) |> ignore
  // $rhs and $lhs are defmfuns that the generated registry does not know.
  defun(q_d_rhs, args => {
    check_arity("$rhs", args, 1)
    d_rhs(args[0])
  })
  defun(q_d_lhs, args => {
    check_arity("$lhs", args, 1)
    d_lhs(args[0])
  })
}
