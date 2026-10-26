// Port of src/solve.lisp: SOLVE, LINSOLVE and their helpers.
//
// The lists *roots and *failures are special variables to which SOLVE
// prepends solutions and their multiplicities in that order: *roots contains
// explicit solutions of the form <var>=<function of independent variables>,
// and *failures contains equations which if solved would yield additional
// solutions.  `mult`, `*var`, `*myvar`, `*g`, `*power`, `*varb`, `*flg`,
// `*has*var`, `equations` and `broken-not-freeof` are special variables.

///|
fn solve__var() -> Value {
  symval(q_n_starvar)
}

///|
fn solve__mult() -> Value {
  symval(q_mult)
}

///|
fn solve__push(s : Value, v : Value) -> Value {
  set(s, cons(v, symval(s)))
}

///|
/// `(map2c f l)` with a MoonBit closure: apply F to successive pairs of L,
/// collecting the results in reverse order.
fn solve__map2c(f : (Value, Value) -> Value raise, l : Value) -> Value raise {
  let mut llt = l
  let mut lans : Value = Nil
  while !(llt is Nil) {
    lans = cons(f(car(llt), cadr(llt)), lans)
    llt = cddr(llt)
  }
  lans
}

///|
/// Message text of a caught Lisp error (`princ-to-string` of the condition).
fn solve__error_string(e : Error) -> String {
  match e {
    LispError::SimpleError(m) => m
    LispError::Condition(_, m, _) => m
    _ => "error"
  }
}

///|
/// Lisp macro ERRCATCH (errset.lisp): `(value)` on success, nil if a Maxima
/// or Lisp error was signalled.  Throws to ERRORSW, MACSYMA-QUIT and RAT-ERR
/// are turned into Maxima errors.
fn solve__errcatch(f : () -> Value raise) -> Value raise {
  let ec = cons(symval(q_bindlist), symval(q_loclist))
  with_specials([(q_errcatch, ec), (q_ear_mdebug, Nil)], () => {
    let body = () => {
      // WITH-ERRCATCH-TAG-$ERRORS
      let mut result : Value? = None
      catch_tag(q_macsyma_quit, () => catch_tag(q_errorsw, () => {
        // RAT-ERROR-TO-MERROR
        let mut error_p = true
        let error_args = catch_tag(q_rat_err, () => {
          result = Some(f())
          error_p = false
          Nil
        })
        if error_p {
          merror(car(error_args), cdr(error_args)) |> ignore
        }
        Nil
      }))
      |> ignore
      match result {
        Some(v) => list1(v)
        None =>
          with_special(q_ear_merror_signals__dolerror_p, t, () => merr(
            "An error was caught by errcatch.",
            [],
          ))
      }
    }
    body() catch {
      LispError::Throw(_, _) as e => raise e
      LispError::ReturnFrom(_, _) as e => raise e
      LispError::Go(_) as e => raise e
      e =>
        if is_maxima_error(e) {
          errlfun1(ec) |> ignore
          Nil
        } else {
          set(
            q_d_error,
            list2(list2(q_mlist, q_simp), Str(solve__error_string(e))),
          )
          |> ignore
          if symval(q_d_errormsg).truthy() {
            d_errormsg() |> ignore
          }
          errlfun1(ec) |> ignore
          Nil
        }
    }
  })
}

///|
/// This is only called on a variable.
fn allroot(exp_ : Value) -> Value raise {
  set(
    q_n_starfailures,
    list_star([mk_simp(q_mequal, [exp_, exp_]), Fix(1L), symval(q_n_starfailures)]),
  )
}

///|
/// Finds variables, changes equations into expressions without MEQUAL.
/// Checks for consistency between the number of unknowns and equations.
/// Calls SOLVEX for simultaneous equations and SSOLVE for a single equation.
fn d_solve(n_stareql : Value, varl? : Value) -> Value raise {
  set(q_d_multiplicities, list1(list1(q_mlist))) |> ignore
  let varl_p = varl is Some(_)
  let mut varl = match varl {
    Some(v) => v
    None => Nil
  }
  with_specials(
    [
      (q_d_keepfloat, Nil),
      (q_d_ratfac, Nil),
      (q_n_starroots, Nil),
      (q_n_starfailures, Nil),
      (q_broken_not_freeof, Nil),
    ],
    () => {
      // Create the equation list (this is a lisp list, not 'MLIST)
      let mut eql = if atom(n_stareql) {
        list1(n_stareql)
      } else if eq(caar(n_stareql), q_mlist) {
        // If we have a list of equations, move everything over
        // to one side, so x=5 -> x-5=0.
        mapcar(x => meqhk(x), cdr(n_stareql))
      } else if memq(
          caar(n_stareql),
          list([q_mnotequal, q_mgreaterp, q_mlessp, q_mgeqp, q_mleqp]),
        ).truthy() {
        // We can't solve inequalities
        merr("solve: cannot solve inequalities.", [])
      } else {
        list1(meqhk(n_stareql))
      }
      if !varl_p {
        // If the variable list wasn't supplied we have to supply it
        // ourselves. Also remove constants like $%pi from the list.
        varl = with_special(q_d_listconstvars, Nil, () => cdr(
          d_listofvars(n_stareql),
        ))
        if varl.truthy() {
          varl = remc(varl)
        }
      } else {
        // If VARL is a list of variables, filter out duplicates.
        // Otherwise, just cons it.
        varl = if d_listp(varl).truthy() {
          remove_duplicates(cdr(varl), pred2=(a, b) => equal(a, b))
        } else {
          list1(varl)
        }
      }
      // Some sanity checks and warning messages.
      if varl is Nil && symval(q_d_solvenullwarn).truthy() {
        mtell(
          list1(Str("~&solve: variable list is empty, continuing anyway.~%")),
        )
        |> ignore
      }
      if eql is Nil && symval(q_d_solvenullwarn).truthy() {
        mtell(
          list1(Str("~&solve: equation list is empty, continuing anyway.~%")),
        )
        |> ignore
      }
      if some(x => mnump(x).truthy(), varl) {
        merr("solve: all variables must not be numbers.", []) |> ignore
      }
      // Deal with special cases.
      if equal(eql, list1(Fix(0L))) {
        // Trivially true equations for any set of variables.
        return q_d_all
      } else if varl is Nil || eql is Nil {
        // Trivially false equations: return []
        return list1(list2(q_mlist, q_simp))
      } else if cdr(varl) is Nil && cdr(eql) is Nil {
        // One equation in one variable: SSOLVE
        return ssolve(car(eql), car(varl))
      } else if varl_p || length(varl) == length(eql) {
        // We were given a variable list, or there are same # of eqns
        // as unknowns: SOLVEX.
        eql = solvex(
          eql,
          varl,
          lbool(!symval(q_d_programmode).truthy()),
          t,
        )
        return if cdr(eql).truthy() && !d_listp(cadr(eql)).truthy() {
          list2(list1(q_mlist), eql)
        } else {
          eql
        }
      }
      // We don't know what to do, so complain.
      let u = cons(list1(q_mlist), varl)
      let e = if d_listp(n_stareql).truthy() {
        n_stareql
      } else {
        list2(list1(q_mlist), n_stareql)
      }
      if length(varl) > length(eql) {
        merr(
          "solve: more unknowns than equations.~\n\t\t  ~%Unknowns given :  ~%~M~\n\t\t  ~%Equations given:  ~%~M",
          [u, e],
        )
      } else {
        merr(
          "solve: more equations than unknowns.~\n\t\t  ~%Unknowns given :  ~%~M~\n\t\t  ~%Equations given:  ~%~M",
          [u, e],
        )
      }
    },
  )
}

///|
/// Removes anything from its list arg which solve considers not to be a
/// variable, i.e.  constants, functions or subscripted variables without
/// numeric args.
fn remc(lst : Value) -> Value raise {
  let mut vl : Value = Nil
  for fl in lst.iter() {
    if atom(fl) {
      if !maxima_constantp(fl).truthy() {
        vl = cons(fl, vl)
      }
    } else if every(x => d_constantp(x).truthy(), cdr(fl)) {
      vl = cons(fl, vl)
    }
  }
  vl
}

///|
/// Solve a single equation for a single unknown.
/// Obtains roots via solve and prints them.
fn ssolve(exp_ : Value, n_starvar : Value) -> Value raise {
  with_specials(
    [
      (q_n_starvar, n_starvar),
      (q_d_solvetrigwarn, symval(q_d_solvetrigwarn)),
      (q_equations, Nil),
    ],
    () => {
      let mut multi : Value = Nil
      if n_starvar is Nil {
        q_d_all
      } else {
        solve(exp_, n_starvar, Fix(1L)) |> ignore
        let roots = symval(q_n_starroots)
        let failures = symval(q_n_starfailures)
        if !(roots.truthy() || failures.truthy()) {
          list1(list1(q_mlist))
        } else if symval(q_d_programmode).truthy() {
          let l = if symval(q_d_solveexplicit).truthy() {
            roots
          } else {
            nconc(roots, failures)
          }
          let res = cons(
            list1(q_mlist),
            nreverse(
              solve__map2c(
                (eqn, mult) => {
                  multi = cons(mult, multi)
                  eqn
                },
                l,
              ),
            ),
          )
          set(q_d_multiplicities, cons(list1(q_mlist), nreverse(multi)))
          |> ignore
          res
        } else {
          if failures.truthy() && !symval(q_d_solveexplicit).truthy() {
            if symval(q_d_dispflag).truthy() {
              mtell(list1(Str("solve: the roots of:~%"))) |> ignore
            }
            set(
              q_equations,
              solve2(symval(q_n_starfailures), symval(q_equations)).1,
            )
            |> ignore
          }
          if symval(q_n_starroots).truthy() {
            if symval(q_d_dispflag).truthy() {
              mtell(list1(Str("solve: solution:~%"))) |> ignore
            }
            set(
              q_equations,
              solve2(symval(q_n_starroots), symval(q_equations)).1,
            )
            |> ignore
          }
          cons(list1(q_mlist), symval(q_equations))
        }
      }
    },
  )
}

///|
/// Solve takes three arguments, the expression to solve for zero, the
/// variable to solve for, and what multiplicity this solution is assumed to
/// have (from higher-level Solve's).  Solve returns NIL.  The solutions are
/// prepended to *roots and *failures.
///
/// Factors expression and reduces exponents by their gcd (via solventhp)
fn solve(n_starexp : Value, n_starvar : Value, mult : Value) -> Value raise {
  let bs = bind_all([
    (q_n_starexp, n_starexp),
    (q_n_starvar, n_starvar),
    (q_mult, mult),
    (q_genvar, Nil),
    (q_d_derivsubst, Nil),
  ])
  defer unbind_all(bs)
  let mut exp_ = float2rat(mratcheck(n_starexp))
  let bs2 = bind_all([
    (q_n_starmyvar, solve__var()),
    (q_d_savefactors, t),
    (q_n_starhas_starvar, Nil),
    (q_d_dontfactor, Nil),
    (q_n_starg, Nil),
    (q_ear_checkfactors, Nil),
    (q_varlist, Nil),
    (q_expsumsplit, Nil),
  ])
  defer unbind_all(bs2)
  let mut temp : Value = Nil
  let mut symbol : Value = Nil
  exp_ = with_special(q_d_ratfac, t, () => ratdisrep(ratf(exp_)))
  // Cancel out any simple (non-algebraic) common factors in numerator and
  // denominator without altering the structure of the expression too much.
  while true {
    // a
    if atom(exp_) {
      if eq(exp_, solve__var()) {
        solve3(Fix(0L), solve__mult()) |> ignore
      } else if equal(exp_, Fix(0L)) {
        allroot(solve__var()) |> ignore
      }
      break
    }
    exp_ = meqhk(exp_)
    if equal(exp_, list1(Fix(0L))) {
      return allroot(solve__var())
    } else if free(exp_, solve__var()).truthy() {
      return Nil
    }
    if !atom(solve__var()) {
      symbol = gensym()
      exp_ = maxima_substitute(symbol, solve__var(), exp_)
      temp = solve__var()
      set(q_n_starvar, symbol) |> ignore
      set(q_n_starmyvar, solve__var()) |> ignore // keep *MYVAR up-to-date
    }
    if symval(q_d_solveradcan).truthy() {
      exp_ = radcan1(exp_, solve__var())
      if atom(exp_) {
        continue
      }
    }
    if easy_cases(exp_, solve__var(), solve__mult()).truthy() {
      if symbol.truthy() {
        set(q_n_starroots, subst(temp, solve__var(), symval(q_n_starroots)))
        |> ignore
        set(
          q_n_starfailures,
          subst(temp, solve__var(), symval(q_n_starfailures)),
        )
        |> ignore
      }
      rootsort(symval(q_n_starroots)) |> ignore
      rootsort(symval(q_n_starfailures)) |> ignore
      return Nil
    }
    let factors = first_order_p(exp_, solve__var())
    if factors.truthy() {
      solve3(
        ratdisrep(
          ratf(mk(q_mtimes, [Fix(-1L), div_star(cdr(factors), car(factors))])),
        ),
        solve__mult(),
      )
      |> ignore
    } else {
      set(q_varlist, list1(solve__var())) |> ignore
      fnewvar(exp_) |> ignore
      set(q_varlist, varsort(symval(q_varlist))) |> ignore
      let mut vartemp : Value = Nil
      let ratnumer = mrat_numer(ratrep_star(exp_))
      let numer_varlist = symval(q_varlist)
      let subst_list = trig_subst_p(symval(q_varlist))
      set(q_varlist, list1(solve__var())) |> ignore
      if subst_list.truthy() {
        exp_ = trig_subst(exp_, subst_list)
        fnewvar(exp_) |> ignore
        set(q_varlist, varsort(symval(q_varlist))) |> ignore
        exp_ = mrat_numer(ratrep_star(exp_))
        vartemp = symval(q_varlist)
      } else {
        vartemp = numer_varlist
        exp_ = ratnumer
      }
      set(q_varlist, vartemp) |> ignore
      if atom(exp_) {
        continue
      } else if of_form_a_starf_ltx_gt_hatn_plusb(exp_).truthy() {
        solve1a(exp_, solve__mult()) |> ignore
      } else if !pcoefp(exp_).truthy() &&
        cddr(exp_).truthy() &&
        {
          set(q_n_starg, solventhp(cdddr(exp_), cadr(exp_))) |> ignore
          !equal(Fix(1L), symval(q_n_starg))
        } &&
        solventh_p(exp_, symval(q_n_starg)).truthy() {
        ()
      } else if symval(q_d_solvefactors).truthy() {
        solve__map2c(
          (x, y) => solve1a(x, muln_star([solve__mult(), y])),
          pfactor(exp_),
        )
        |> ignore
      } else {
        solve1a(exp_, solve__mult()) |> ignore
      }
    }
    break
  }
  if symbol.truthy() {
    set(q_n_starroots, subst(temp, solve__var(), symval(q_n_starroots)))
    |> ignore
    set(q_n_starfailures, subst(temp, solve__var(), symval(q_n_starfailures)))
    |> ignore
  }
  rootsort(symval(q_n_starroots)) |> ignore
  rootsort(symval(q_n_starfailures)) |> ignore
  Nil
}

///|
fn float2rat(exp_ : Value) -> Value raise {
  if floatp(exp_) {
    let e = prep1(exp_)
    mk_simp(q_rat, [car(e), cdr(e)])
  } else if atom(exp_) || specrepp(exp_).truthy() {
    exp_
  } else {
    recur_apply(q_float2rat, exp_)
  }
}

///|
/// The following takes care of cases where the expression is already in
/// factored form. This can introduce spurious roots if one of the factors
/// is an expression that can be undefined or infinity for certain values of
/// the variable in question.
/// Passes multiplicity to recursive calls to solve.
fn easy_cases(n_starexp : Value, n_starvar : Value, mult : Value) -> Value raise {
  with_specials(
    [(q_n_starexp, n_starexp), (q_n_starvar, n_starvar), (q_mult, mult)],
    () => if atom(n_starexp) || atom(car(n_starexp)) {
      Nil
    } else if eq(caar(n_starexp), q_mtimes) {
      for term in cdr(n_starexp).iter() {
        solve(term, n_starvar, mult) |> ignore
      }
      q_mtimes
    } else if memq(caar(n_starexp), list2(q_mabs, q_p_signum)).truthy() {
      // abs(x) = 0, signum(x) = 0  <=>  x = 0
      solve(cadr(n_starexp), n_starvar, mult) |> ignore
      caar(n_starexp)
    } else if eq(caar(n_starexp), q_mexpt) {
      if freeof(n_starvar, cadr(n_starexp)).truthy() &&
        !zerop1(cadr(n_starexp)).truthy() {
        // no solutions: c^x is never zero
        q_mexpt
      } else if integerp(caddr(n_starexp)) && plusp(caddr(n_starexp)) {
        solve(cadr(n_starexp), n_starvar, muln_star([mult, caddr(n_starexp)]))
        |> ignore
        q_mexprat
      } else {
        Nil
      }
    } else {
      Nil
    },
  )
}

///|
/// Predicate to test for presence of troublesome trig functions to be
/// canonicalized.
fn trig_subst_p(vlist : Value) -> Value raise {
  if trig_not_subst_p(vlist).truthy() {
    return Nil
  }
  let mut subst_list : Value = Nil
  let mut vl = vlist
  while true {
    let var_ = car(vl)
    vl = cdr(vl)
    if var_ is Nil {
      break
    }
    if !atom(var_) &&
      trig_cannon(caar(var_)).truthy() &&
      !free(var_, solve__var()).truthy() {
      subst_list = cons(var_, subst_list)
    }
  }
  subst_list
}

///|
/// Predicate to see when obviously not to substitute for trigs.
/// The "measure" of the expression is the total number of different kinds
/// of trig functions in the expression.
fn trig_not_subst_p(vlist : Value) -> Value raise {
  let trigs = list([q_p_sin, q_p_cos, q_p_tan, q_p_cot, q_p_csc, q_p_sec])
  lbool(
    num_lt(
      measure(q_sign_gjc, operator_frequency_table(vlist, trigs), trigs),
      Fix(2L),
    ),
  )
}

///|
/// To get the total "value" of things in a table, this case an assoc list.
fn measure(f : Value, alist : Value, set_ : Value) -> Value raise {
  let mut sum : Value = Fix(0L)
  for element in set_.iter() {
    let v = cdr(assq(element, alist))
    let r = if eq(f, q_sign_gjc) { sign_gjc(v) } else { funcall(f, [v]) }
    sum = num_add(sum, r)
  }
  sum
}

///|
/// Named for uniqueness only
fn sign_gjc(x : Value) -> Value raise {
  if x is Nil || num_eq(x, Fix(0L)) {
    Fix(0L)
  } else if num_lt(Fix(0L), x) {
    Fix(1L)
  } else {
    Fix(-1L)
  }
}

///|
/// A function that can EXTEND a function over two association lists.
fn extend_(f : Value, l1 : Value, l2 : Value, s : Value) -> Value raise {
  let mut value : Value = Nil
  let n = length(s)
  for j in 0..<n {
    let a = cdr(assoc_equal(nth(j, s), l1))
    let b = cdr(assoc_equal(nth(j, s), l2))
    let r = if eq(f, q_n_plusmset) { n_plusmset(a, b) } else { funcall(f, [a, b]) }
    value = cons(cons(nth(j, s), r), value)
  }
  value
}

///|
/// For the case where the value of assoc is NIL, we will need a special "+"
fn n_plusmset(a : Value, b : Value) -> Value raise {
  num_add(if a.truthy() { a } else { Fix(0L) }, if b.truthy() {
    b
  } else {
    Fix(0L)
  })
}

///|
/// Recursively looks through a list structure (the VLIST) for members of
/// the SET appearing in the MACSYMA functional position (caar list).
/// Returning an assoc. list of appearance frequencies.
fn operator_frequency_table(vlist : Value, set_ : Value) -> Value raise {
  let mut assl : Value = Nil
  let ns = length(set_)
  for k in 0..<ns {
    assl = cons(cons(nth(k, set_), Fix(0L)), assl)
  }
  let nv = length(vlist)
  for j in 0..<nv {
    let it = nth(j, vlist)
    if !atom(it) {
      assl = extend_(q_n_plusmset, list1(cons(caar(it), Fix(1L))), assl, set_)
      assl = extend_(
        q_n_plusmset,
        assl,
        operator_frequency_table(cdr(it), set_),
        set_,
      )
    }
  }
  assl
}

///|
fn trig_subst(exp_ : Value, sub_list : Value) -> Value raise {
  let mut exp_ = exp_
  let mut sl = sub_list
  while true {
    let var_ = car(sl)
    sl = cdr(sl)
    if var_ is Nil {
      break
    }
    exp_ = maxima_substitute(
      funcall(trig_cannon(caar(var_)), [cons(list1(q_mlist), cdr(var_))]),
      var_,
      exp_,
    )
  }
  exp_
}

// Here are the canonical trig substitutions.

///|
fn solve__p_sec_trig_cannon(x : Value) -> Value raise {
  inv_star(mk(q_p_cos, [cadr(x)]))
}

///|
fn solve__p_csc_trig_cannon(x : Value) -> Value raise {
  inv_star(mk(q_p_sin, [cadr(x)]))
}

///|
fn solve__p_tan_trig_cannon(x : Value) -> Value raise {
  div_star(mk(q_p_sin, [cadr(x)]), mk(q_p_cos, [cadr(x)]))
}

///|
fn solve__p_cot_trig_cannon(x : Value) -> Value raise {
  div_star(mk(q_p_cos, [cadr(x)]), mk(q_p_sin, [cadr(x)]))
}

///|
fn solve__p_sech_trig_cannon(x : Value) -> Value raise {
  inv_star(mk(q_p_cosh, [cadr(x)]))
}

///|
fn solve__p_csch_trig_cannon(x : Value) -> Value raise {
  inv_star(mk(q_p_sinh, [cadr(x)]))
}

///|
fn solve__p_tanh_trig_cannon(x : Value) -> Value raise {
  div_star(mk(q_p_sinh, [cadr(x)]), mk(q_p_cosh, [cadr(x)]))
}

///|
fn solve__p_coth_trig_cannon(x : Value) -> Value raise {
  div_star(mk(q_p_cosh, [cadr(x)]), mk(q_p_sinh, [cadr(x)]))
}

///|
/// Predicate to replace ISLINEAR....Returns NIL if not of for A*X+B, A and B
/// freeof X, else returns (A . B)
fn first_order_p(exp_ : Value, var_ : Value) -> Value raise {
  // Expand the expression at one level, i.e. distribute products
  // over sums, but leave exponentiations alone.
  let exp_ = expand1(exp_, Fix(1L), Fix(1L))
  if atom(exp_) {
    return Nil
  }
  let op = caar(exp_)
  if eq(op, q_mtimes) {
    let temp = linear_term_p(exp_, var_)
    if temp.truthy() {
      cons(temp, Fix(0L))
    } else {
      Nil
    }
  } else if eq(op, q_mplus) {
    let mut linear_term_list : Value = Nil
    let mut constant_term_list : Value = Nil
    let mut rest_ = cdr(exp_)
    while true {
      let arg = car(rest_)
      rest_ = cdr(rest_)
      if arg is Nil {
        break
      }
      let temp = linear_term_p(arg, var_)
      if temp.truthy() {
        linear_term_list = cons(temp, linear_term_list)
      } else if broken_freeof(var_, arg).truthy() {
        constant_term_list = cons(arg, constant_term_list)
      } else {
        return Nil
      }
    }
    if linear_term_list.truthy() {
      cons(
        cons(list1(q_mplus), linear_term_list),
        if constant_term_list.truthy() {
          cons(list1(q_mplus), constant_term_list)
        } else {
          Fix(0L)
        },
      )
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// Function to test if a term from an expanded expression is a linear term
/// check and see that exactly one item in the product is the main var and
/// all others are free of the main var.  Returns NIL or a G-REP expression.
fn linear_term_p(exp_ : Value, var_ : Value) -> Value raise {
  if atom(exp_) {
    if eq(exp_, var_) {
      Fix(1L)
    } else {
      Nil
    }
  } else if eq(caar(exp_), q_mtimes) {
    let mut main_var_p = false
    let mut list_of_factors : Value = Nil
    let mut rest_ = cdr(exp_)
    while true {
      let factor = car(rest_)
      rest_ = cdr(rest_)
      if factor is Nil {
        break
      }
      if eq(factor, var_) {
        main_var_p = true
      } else if broken_freeof(var_, factor).truthy() {
        list_of_factors = cons(factor, list_of_factors)
      } else {
        return Nil
      }
    }
    if main_var_p {
      cons(list1(q_mtimes), list_of_factors)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// DISPATCHING FUNCTION ON DEGREE OF EXPRESSION.
/// EXP here is a polynomial in MRAT form.  All of this works by side
/// effect.
fn solve1a(exp_ : Value, mult : Value) -> Value raise {
  with_specials(
    [(q_mult, mult), (q_n_starmyvar, symval(q_n_starmyvar)), (q_n_starg, Nil)],
    () => {
      if atom(exp_) {
        return Nil
      }
      set(q_n_starmyvar, simplify(pdis(list3(car(exp_), Fix(1L), Fix(1L)))))
      |> ignore
      if !memalike(symval(q_n_starmyvar), symval(q_n_starhas_starvar)).truthy() {
        Nil
      } else if equal(cadr(exp_), Fix(1L)) {
        solvelin(exp_)
      } else if of_form_a_starf_ltx_gt_hatn_plusb(exp_).truthy() {
        solve_a_starf_ltx_gt_hatn_plusb(exp_, t)
      } else if equal(cadr(exp_), Fix(2L)) {
        solvequad(exp_)
      } else if {
          set(q_n_starg, solventhp(cdddr(exp_), cadr(exp_))) |> ignore
          !equal(Fix(1L), symval(q_n_starg))
        } &&
        solventh_p(exp_, symval(q_n_starg)).truthy() {
        t
      } else if equal(cadr(exp_), Fix(3L)) {
        solvecubic(exp_)
      } else if equal(cadr(exp_), Fix(4L)) {
        solvequartic(exp_)
      } else {
        let tt = solve_by_decomposition(exp_, symval(q_n_starmyvar))
        set(q_n_starfailures, append(cdr(tt), symval(q_n_starfailures)))
        |> ignore
        set(q_n_starroots, append(car(tt), symval(q_n_starroots)))
      }
    },
  )
}

///|
fn solve_simplist(list_of_things : Value) -> Value raise {
  cdr(simplifya(cons(list1(q_mlist), list_of_things), Nil))
}

///|
/// The Solve-by-decomposition program returns a "Solution" object, that
/// is, a CONS with the CAR being the successes and the CDR being the
/// failures.  It takes a POLY as an argument and returns a SOLUTION.
fn solve_by_decomposition(poly : Value, n_star_dolvar : Value) -> Value raise {
  let mut decomp : Value = Nil
  if !symval(q_d_solvedecomposes).truthy() ||
    {
      decomp = polydecomp(poly, car(poly))
      length(decomp) == 1
    } {
    cons(Nil, list2(mk(q_mequal, [Fix(0L), pdis(poly)]), Fix(1L)))
  } else {
    decomp_trace(
      mk(q_mequal, [Fix(0L), rdis(car(decomp))]),
      decomp,
      car(poly),
      n_star_dolvar,
      Fix(1L),
    )
  }
}

///|
/// DECOMP-TRACE is the recursive function which maps itself down the
/// intermediate solutions until the end is reached.  If it encounters
/// non-solvable equations it stops.  It returns a SOLUTION object.
fn decomp_trace(
  eqn : Value,
  decomp : Value,
  var_ : Value,
  n_star_dolvar : Value,
  mult : Value,
) -> Value raise {
  with_special(q_mult, mult, () => {
    let sol = if decomp.truthy() {
      re_solve(eqn, n_star_dolvar, mult)
    } else {
      cons(list2(eqn, Fix(1L)), Nil)
    }
    if cdr(sol).truthy() {
      sol
    } else if decomp is Nil {
      // End test
      sol
    } else {
      let mut wins : Value = Nil
      let mut losses : Value = Nil
      let mut l = car(sol)
      while !(l is Nil) {
        let chain_sol = decomp_chain(
          car(l),
          cdr(decomp),
          var_,
          n_star_dolvar,
          cadr(l),
        )
        wins = nconc(wins, copy_list(car(chain_sol)))
        losses = nconc(losses, copy_list(cdr(chain_sol)))
        l = cddr(l)
      }
      cons(wins, losses)
    }
  })
}

///|
/// Decomp-chain is the function which formats the mess for the recursive
/// call.  It returns a "Solution" object.
fn decomp_chain(
  rsol : Value,
  decomp : Value,
  var_ : Value,
  n_star_dolvar : Value,
  mult : Value,
) -> Value raise {
  with_special(q_mult, mult, () => {
    let sol = simplify(
      mk(q_mequal, [
        rdis(
          if decomp.truthy() {
            car(decomp)
          } else {
            // Include the var itself in the decomposition
            cons(cons(var_, list2(Fix(1L), Fix(1L))), Fix(1L))
          },
        ),
        caddr(rsol),
      ]),
    )
    decomp_trace(sol, decomp, var_, n_star_dolvar, mult)
  })
}

///|
/// RE-SOLVE calls SOLVE recursively, returning a SOLUTION object.
/// Will not decompose or factor.
fn re_solve(eqn : Value, var_ : Value, mult : Value) -> Value raise {
  with_specials(
    [
      (q_mult, mult),
      (q_n_starroots, Nil),
      (q_n_starfailures, Nil),
      // We've already decomposed and factored
      (q_d_solvedecomposes, Nil),
      (q_d_solvefactors, Nil),
    ],
    () => {
      solve(eqn, var_, mult) |> ignore
      cons(symval(q_n_starroots), symval(q_n_starfailures))
    },
  )
}

///|
/// SOLVENTH programs test to see if the variable of interest appears
/// to some power in all terms.  If so, a new variable is substituted for it
/// and the simpler expression solved with the multiplicity
/// adjusted accordingly.
/// SOLVENTHP returns gcd of exponents.
fn solventhp(l : Value, gcd_ : Value) -> Value raise {
  if l is Nil {
    gcd_
  } else if equal(gcd_, Fix(1L)) {
    Fix(1L)
  } else {
    solventhp(cddr(l), num_gcd(car(l), gcd_))
  }
}

///|
/// ROOT is *VARB = R, what is left of an equation once SOLVENTH has reduced
/// the exponents and undone the power. SOLVE inverts that where R is free
/// of the unknown. Where it is not, no inverse applies, and all that can be
/// looked for is where R vanishes - and such a point is a root only if
/// *VARB vanishes there as well.
fn solventh_invert(root : Value, mult : Value) -> Value raise {
  with_special(q_mult, mult, () => if broken_freeof(solve__var(), caddr(root)).truthy() {
    solve(root, symval(q_n_starmyvar), mult)
  } else {
    let found = with_specials(
      [(q_n_starroots, Nil), (q_n_starfailures, Nil)],
      () => {
        solve(mk(q_mequal, [caddr(root), Fix(0L)]), symval(q_n_starmyvar), mult)
        |> ignore
        symval(q_n_starroots)
      },
    )
    let mut l = found
    while l is Cons(_) {
      let r = car(l)
      let m = cadr(l)
      if zerop1(no_err_sub_var(caddr(r), symval(q_n_starvarb), solve__var())).truthy() {
        set(q_n_starroots, list_star([r, m, symval(q_n_starroots)])) |> ignore
      }
      l = cddr(l)
    }
    Nil
  })
}

///|
/// Reduces exponents by their gcd.
fn solventh(exp_ : Value, n_starg : Value) -> Value raise {
  with_special(q_n_starg, n_starg, () => {
    let varb = pdis(cons(car(exp_), list2(Fix(1L), Fix(1L))))
    let exp1 = cons(car(exp_), solventh1(cdr(exp_)))
    with_special(q_n_starvarb, varb, () => {
      let rts = re_solve_full(pdis(exp1), varb)
      let fails = cdr(rts)
      let wins = car(rts)
      with_special(q_n_starpower, mk(q_mexpt, [varb, n_starg]), () => {
        solve__map2c(
          (w, z) => if atom(symval(q_n_starvarb)) {
            solve(
              mk(q_mequal, [symval(q_n_starpower), caddr(w)]),
              symval(q_n_starvarb),
              z,
            )
          } else {
            let rts = re_solve_full(
              mk(q_mequal, [symval(q_n_starpower), caddr(w)]),
              symval(q_n_starvarb),
            )
            solve__map2c((a, b) => solventh_invert(a, b), car(rts))
          },
          wins,
        )
        |> ignore
        solve__map2c(
          (w, z) => {
            solve__push(q_n_starfailures, z) |> ignore
            solve__push(
              q_n_starfailures,
              solventh3(w, symval(q_n_starpower), symval(q_n_starvarb)),
            )
          },
          fails,
        )
        |> ignore
        symval(q_n_starroots)
      })
    })
  })
}

///|
/// SOLVENTH, answering whether it found anything. It can come up empty,
/// having reduced the exponents and then found nothing to invert, and that
/// settles nothing - the ordinary methods still get their chance at the
/// equation.
fn solventh_p(exp_ : Value, n_starg : Value) -> Value raise {
  with_special(q_n_starg, n_starg, () => {
    let roots = symval(q_n_starroots)
    let failures = symval(q_n_starfailures)
    solventh(exp_, n_starg) |> ignore
    lbool(
      !(
        physical_equal_value(roots, symval(q_n_starroots)) &&
        physical_equal_value(failures, symval(q_n_starfailures))
      ),
    )
  })
}

///|
fn solventh3(w : Value, n_starpower : Value, n_starvarb : Value) -> Value raise {
  with_specials(
    [
      (q_n_starpower, n_starpower),
      (q_n_starvarb, n_starvarb),
      (q_varlist, Nil),
      (q_genvar, Nil),
      (q_n_starflg, Nil),
    ],
    () => if broken_freeof(n_starvarb, w).truthy() {
      w
    } else {
      let w1 = ratf(cadr(w))
      let w2 = ratf(caddr(w))
      set(
        q_varlist,
        mapcar(
          h => if symval(q_n_starflg).truthy() {
            h
          } else if alike1(h, n_starvarb).truthy() {
            set(q_n_starflg, t) |> ignore
            n_starpower
          } else {
            h
          },
          symval(q_varlist),
        ),
      )
      |> ignore
      list3(car(w), rdis(cdr(w1)), rdis(cdr(w2)))
    },
  )
}

///|
fn solventh1(l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else {
    cons(quot(car(l), symval(q_n_starg)), cons(cadr(l), solventh1(cddr(l))))
  }
}

///|
/// Will decompose or factor
fn re_solve_full(x : Value, var_ : Value) -> Value raise {
  with_specials([(q_n_starroots, Nil), (q_n_starfailures, Nil)], () => {
    solve(x, var_, solve__mult()) |> ignore
    cons(symval(q_n_starroots), symval(q_n_starfailures))
  })
}

///|
/// Sees if expression is of the form A*F<X>^N+B.
fn of_form_a_starf_ltx_gt_hatn_plusb(e : Value) -> Value raise {
  let has_var = symval(q_n_starhas_starvar)
  if memalike(simplify(pdis(list3(car(e), Fix(1L), Fix(1L)))), has_var).truthy() &&
    (
      atom(caddr(e)) ||
      !memalike(simplify(pdis(list3(caaddr(e), Fix(1L), Fix(1L)))), has_var).truthy()
    ) &&
    (cdddr(e) is Nil || equal(cadddr(e), Fix(0L))) {
    t
  } else {
    Nil
  }
}

///|
/// Solves the special case A*F<X>^N+B.
fn solve_a_starf_ltx_gt_hatn_plusb(
  exp_ : Value,
  d__pctemode : Value,
) -> Value raise {
  with_special(q_d__pctemode, d__pctemode, () => {
    let a = pdis(caddr(exp_))
    let c = pdis(list3(car(exp_), Fix(1L), Fix(1L)))
    if cdddr(exp_) is Nil {
      return solve(c, solve__var(), num_mul(cadr(exp_), solve__mult()))
    }
    let b = pdis(pminus(cadddr(cdr(exp_))))
    solve_a_starf_ltx_gt_hatn_plusb1(
      c,
      simpnrt(div_star(b, a), cadr(exp_)),
      mk(q_rat, [Fix(1L), cadr(exp_)]),
      cadr(exp_),
    )
  })
}

///|
fn solve_a_starf_ltx_gt_hatn_plusb1(
  var_ : Value,
  root : Value,
  n : Value,
  thisn : Value,
) -> Value raise {
  let mut thisn = thisn
  while !zerop(thisn) {
    solve(
      addn_star([
        var_,
        muln_star([
          Fix(-1L),
          root,
          power_star(
            q_d__pcte,
            muln_star([Fix(2L), q_d__pctpi, q_d__pcti, thisn, n]),
          ),
        ]),
      ]),
      solve__var(),
      solve__mult(),
    )
    |> ignore
    thisn = one_minus(thisn)
  }
  Nil
}

///|
/// ADISPLINE displays a line like DISPLINE, and in addition, notes that it
/// is not free of *VAR if it isn't.
fn adispline(line : Value) -> Value raise {
  if symval(q_d_breakup).truthy() && !symval(q_d_programmode).truthy() {
    let linelabel = displine(line)
    if !broken_freeof(solve__var(), line).truthy() {
      set(q_broken_not_freeof, cons(linelabel, symval(q_broken_not_freeof)))
      |> ignore
    }
    linelabel
  } else {
    displine(line)
  }
}

///|
/// == (freeof var exp) but works even if solution is broken up ($breakup=t)
fn broken_freeof(var_ : Value, exp_ : Value) -> Value raise {
  if symval(q_d_breakup).truthy() {
    let mut b_n_fo = var_
    let mut b_n_fo_l = symval(q_broken_not_freeof)
    while !(b_n_fo is Nil) {
      if !argsfreeof(b_n_fo, exp_).truthy() {
        return Nil
      }
      b_n_fo = car(b_n_fo_l)
      b_n_fo_l = cdr(b_n_fo_l)
    }
    t
  } else {
    argsfreeof(var_, exp_)
  }
}

///|
/// Adds solutions to roots list.
/// Solves for inverse of functions (via USOLVE)
fn solve3(exp_ : Value, mult : Value) -> Value raise {
  with_special(q_mult, mult, () => {
    let exp_ = simplify(exp_)
    let myvar = symval(q_n_starmyvar)
    if !broken_freeof(solve__var(), exp_).truthy() {
      solve__push(q_n_starfailures, mult) |> ignore
      solve__push(q_n_starfailures, mk_simp(q_mequal, [simplify(myvar), exp_]))
    } else if eq(myvar, solve__var()) {
      solve__push(q_n_starroots, mult) |> ignore
      solve__push(q_n_starroots, mk_simp(q_mequal, [solve__var(), exp_]))
    } else if atom(myvar) {
      solve__push(q_n_starfailures, mult) |> ignore
      solve__push(q_n_starfailures, mk_simp(q_mequal, [myvar, exp_]))
    } else {
      usolve(exp_, caar(myvar))
    }
  })
}

///|
/// Solve a linear equation.  Argument is a polynomial in pseudo-cre form.
/// This function is called for side-effect only.
fn solvelin(exp_ : Value) -> Value raise {
  if equal(Fix(0L), ptterm(cdr(exp_), Fix(0L))) {
    solve1a(caddr(exp_), solve__mult()) |> ignore
  }
  solve3(
    rdis(ratreduce(pminus(ptterm(cdr(exp_), Fix(0L))), caddr(exp_))),
    solve__mult(),
  )
}

///|
/// Solve a quadratic equation.  Argument is a polynomial in pseudo-cre form.
/// This function is called for side-effect only.
fn solvequad(exp_ : Value) -> Value raise {
  let mut a = caddr(exp_)
  let mut b = ptterm(cdr(exp_), Fix(1L))
  let c = ptterm(cdr(exp_), Fix(0L))
  let mut discrim = simplify(
    pdis(pplus(pexpt(b, Fix(2L)), pminus(ptimes(Fix(4L), ptimes(a, c))))),
  )
  b = pdis(pminus(b))
  a = pdis(ptimes(Fix(2L), a))
  // At this point, everything is back in general representation.
  with_special(q_varlist, Nil, () => if equal(Fix(0L), discrim) {
    solve3(
      fullratsimp(mk(q_mquotient, [b, a])),
      num_mul(Fix(2L), solve__mult()),
    )
  } else {
    discrim = simpnrt(discrim, Fix(2L))
    solve3(
      fullratsimp(mk(q_mquotient, [mk(q_mplus, [b, discrim]), a])),
      solve__mult(),
    )
    |> ignore
    solve3(
      fullratsimp(
        mk(q_mquotient, [mk(q_mplus, [b, mk(q_mminus, [discrim])]), a]),
      ),
      solve__mult(),
    )
  })
}

///|
/// `(delete z l :count 1 :test #'equal)`
fn solve__delete1_equal(z : Value, l : Value) -> Value {
  match l {
    Cons({ car, cdr }) =>
      if equal(car, z) {
        cdr
      } else {
        cons(car, solve__delete1_equal(z, cdr))
      }
    _ => l
  }
}

///|
/// Reorders V so that members which contain the variable of
/// interest come first.
fn varsort(v : Value) -> Value raise {
  let mut u : Value = Nil
  let mut vv = copy_list(v)
  for z in v.iter() {
    if broken_freeof(solve__var(), z).truthy() {
      u = cons(z, u)
      vv = solve__delete1_equal(z, vv)
    }
  }
  set(q_d_dontfactor, u) |> ignore
  set(q_n_starhas_starvar, mapcar(x => resimplify(x), vv)) |> ignore
  append(u, vv)
}

///|
/// Solves for variable when it occurs within a function by taking the
/// inverse.  Solve <exp> = <*myvar> for <*var>, where <*myvar>=<op>(...)
fn usolve(exp_ : Value, op : Value) -> Value raise {
  let myvar = symval(q_n_starmyvar)
  let var_ = solve__var()
  let fail = () => set(
    q_n_starfailures,
    cons(
      simplify(mk(q_mequal, [symval(q_n_starmyvar), exp_])),
      cons(solve__mult(), symval(q_n_starfailures)),
    ),
  )
  let inverse = if eq(op, q_mexpt) {
    if broken_freeof(var_, cadr(myvar)).truthy() {
      if equal(exp_, Fix(0L)) {
        return fail()
      }
      mk(q_mplus, [
        mk(q_mminus, [caddr(myvar)]),
        div_star(mk(q_p_log, [exp_]), mk(q_p_log, [cadr(myvar)])),
      ])
    } else if broken_freeof(var_, caddr(myvar)).truthy() {
      if equal(exp_, Fix(0L)) {
        if mnegp(caddr(myvar)).truthy() {
          return fail()
        } else {
          cadr(myvar)
        }
      } else if !eq(ask_integer(caddr(myvar), q_d_integer), q_d_yes) &&
        free(exp_, q_d__pcti).truthy() &&
        eq(d_asksign(exp_), q_d_neg) {
        return fail()
      } else {
        mk(q_mplus, [
          cadr(myvar),
          mk(q_mminus, [
            mk(q_mexpt, [exp_, div_star(Fix(1L), caddr(myvar))]),
          ]),
        ])
      }
    } else {
      return fail()
    }
  } else if get(op, q_d_inverse).truthy() {
    let inverse = get(op, q_d_inverse)
    if symval(q_d_solvetrigwarn).truthy() &&
      memq(
        op,
        list([
          q_p_sin, q_p_cos, q_p_tan, q_p_sec, q_p_csc, q_p_cot, q_p_cosh, q_p_sech,
        ]),
      ).truthy() {
      mtell(
        list1(
          Str(
            "~&solve: using arc-trig functions to get a solution.~%Some solutions will be lost.~%",
          ),
        ),
      )
      |> ignore
      set(q_d_solvetrigwarn, Nil) |> ignore
    }
    // Sanity check: return NIL (no solutions) if either
    // - simplifying INVERSE(EXP) causes an error
    //   (e.g., tan(%pi/2) when solving atan(x) = %pi/2)
    // - simplifying OP(INVERSE(EXP)) causes an error
    // - MEQP says that OP(INVERSE(EXP)) is definitely not equal to EXP
    //   (e.g., tan(2) as a solution to atan(x) = 2)
    let inverse_exp_l = solve__errcatch(() => ftake_star(inverse, [exp_]))
    let check_l = if inverse_exp_l.truthy() {
      solve__errcatch(() => ftake(op, [car(inverse_exp_l)]))
    } else {
      Nil
    }
    if inverse_exp_l is Nil ||
      check_l is Nil ||
      // Workaround until SIGN gets smarter at judging zeroness of a
      // constant: Disable $SIGNBFLOAT.
      !with_special(q_d_signbfloat, Nil, () => meqp(car(check_l), exp_)).truthy() {
      return Nil
    }
    mk(q_mplus, [mk(q_mminus, [cadr(myvar)]), car(inverse_exp_l)])
  } else if eq(op, q_p_log) {
    mk(q_mplus, [mk(q_mminus, [cadr(myvar)]), mk(q_mexpt, [q_d__pcte, exp_])])
  } else if eq(op, q_mabs) {
    let exp_sign = d_csign(exp_)
    if eq(exp_sign, q_d_zero) {
      // abs(z) = 0 <=> z = 0
      solve(cadr(myvar), var_, solve__mult()) |> ignore
      return Nil
    } else if memq(exp_sign, list2(q_d_neg, q_d_imaginary)).truthy() ||
      eq(t, mnqp(Fix(0L), d_imagpart(exp_))) {
      // abs(z) can't be negative or complex; no solution.
      return Nil
    } else if !memq(d_csign(cadr(myvar)), list2(q_d_complex, q_d_imaginary)).truthy() {
      // abs(real) = EXP <=> real +- EXP = 0.
      solve(add2(cadr(myvar), exp_), var_, solve__mult()) |> ignore
      solve(sub(cadr(myvar), exp_), var_, solve__mult()) |> ignore
      return Nil
    } else {
      return fail()
    }
  } else if eq(op, q_p_signum) {
    if eq(d_csign(exp_), q_d_zero) {
      // signum(z) = 0 <=> z = 0
      solve(cadr(myvar), var_, solve__mult()) |> ignore
      return Nil
    } else if !memq(d_csign(cadr(myvar)), list2(q_d_complex, q_d_imaginary)).truthy() &&
      !meqp(exp_, Fix(-1L)).truthy() &&
      !meqp(exp_, Fix(0L)).truthy() &&
      !meqp(exp_, Fix(1L)).truthy() {
      // signum(real) can only be -1, 0, 1; no solution.
      return Nil
    } else {
      return fail()
    }
  } else {
    return fail()
  }
  // Return NIL (no solutions) if simplification causes an error.
  // Otherwise, keep solving.
  let inverse = solve__errcatch(() => simplify(inverse))
  if inverse.truthy() {
    solve(car(inverse), solve__var(), solve__mult())
  } else {
    Nil
  }
}

///|
/// Predicate for determining if an expression is messy enough to
/// generate a new linelabel for it.
/// Expression must be in general form.
fn complicated(exp_ : Value) -> Value raise {
  if symval(q_d_breakup).truthy() && !symval(q_d_programmode).truthy() {
    lbool(!free(exp_, q_mplus).truthy())
  } else {
    Nil
  }
}

///|
/// Merge the multiplicities of ALIKE1 entries of the alternating
/// root/multiplicity list L, destructively.
fn rootsort(l : Value) -> Value raise {
  let mut l = l
  while !(l is Nil) {
    // g1
    let mut fm = l
    let a = car(fm)
    let fm1 = cdr(fm)
    while true {
      // loop
      if cddr(fm) is Nil {
        l = cddr(l)
        break
      } else if alike1(caddr(fm), a).truthy() {
        rplaca(fm1, num_add(car(fm1), cadddr(fm))) |> ignore
        rplacd(cdr(fm), cddddr(fm)) |> ignore
        continue
      }
      fm = cddr(fm)
    }
  }
  Nil
}

///|
/// `(delete-duplicates l :test #'equal :from-end t)`
fn solve__delete_duplicates_from_end(l : Value) -> Value {
  let r : Array[Value] = []
  for x in l.iter() {
    if !r.iter().any(y => equal(y, x)) {
      r.push(x)
    }
  }
  list(r)
}

///|
fn d_linsolve(eql_ : Value, varl : Value) -> Value raise {
  with_special(q_d_ratfac, Nil, () => {
    let eql = if d_listp(eql_).truthy() { cdr(eql_) } else { list1(eql_) }
    let varl = if d_listp(varl).truthy() {
      solve__delete_duplicates_from_end(cdr(varl))
    } else {
      list1(varl)
    }
    for v in varl.iter() {
      if mnump(v).truthy() {
        merr("solve: variable must not be a number; found: ~M", [v]) |> ignore
      }
    }
    if varl is Nil {
      list1(list2(q_mlist, q_simp))
    } else {
      solvex(
        mapcar(x => meqhk(x), eql),
        varl,
        lbool(!symval(q_d_programmode).truthy()),
        Nil,
      )
    }
  })
}

///|
fn solvex(eql_ : Value, varl : Value, ind : Value, flag : Value) -> Value raise {
  with_specials(
    [
      (q_d_algebraic, symval(q_d_algebraic)),
      (q_varlist, Nil),
      (q_genvar, Nil),
      (q_xm_star, Nil),
      (q_xn_star, Nil),
      (q_mul_star, Nil),
    ],
    () => {
      let n_starvarl = varl
      let mut varl = varl
      let eql = mapcar(x => d_ratdisrep(d_ratnumer(x)), eql_)
      // IGNORE-RAT-ERR
      let mut error_p = true
      let mut result : Value = Nil
      catch_tag(q_rat_err, () => {
        result = formx(flag, q_xa_star, eql, varl)
        error_p = false
        Nil
      })
      |> ignore
      let formed : Value = if error_p { Nil } else { result }
      if atom(formed) {
        // This flag is T if called from SOLVE
        // and NIL if called from LINSOLVE.
        if flag.truthy() {
          return d_algsys(cons(list1(q_mlist), eql), cons(list1(q_mlist), varl))
        } else {
          merr("linsolve: cannot solve a nonlinear equation.", []) |> ignore
        }
      }
      let ans = tfgeli(q_xa_star, symval(q_xn_star), symval(q_xm_star))
      if symval(q_d_linsolvewarn).truthy() && car(ans).truthy() {
        mtell(
          list2(Str("~&solve: dependent equations eliminated: ~A~%"), car(ans)),
        )
        |> ignore
      }
      if cadr(ans).truthy() {
        return list1(list2(q_mlist, q_simp))
      }
      let xm = to_int(symval(q_xm_star))
      for j in 0..=xm {
        // I put this in the value cell--wfs
        aset(symval(q_xa_star), [0, j], Nil) |> ignore
      }
      ptorat(q_xa_star, symval(q_xn_star), symval(q_xm_star)) |> ignore
      varl = xrutout(
        q_xa_star,
        symval(q_xn_star),
        symval(q_xm_star),
        mapcar(x => ith(varl, x), caddr(ans)),
        ind,
      )
      if symval(q_d_programmode).truthy() {
        varl = cons(list1(q_mlist), linsort(cdr(varl), n_starvarl))
      }
      varl
    },
  )
}

///|
/// (LINSORT '(((MEQUAL) A2 FOO) ((MEQUAL) A3 BAR)) '(A3 A2))
/// returns (((MEQUAL) A3 BAR) ((MEQUAL) A2 FOO)) .
fn linsort(meq_list : Value, var_list : Value) -> Value raise {
  let head = caar(meq_list)
  mapcar(
    x => cons(head, x),
    sort_list(mapcar(x => cdr(x), meq_list), (x, y) => member_equal(
      car(y),
      member_equal(car(x), var_list),
    ).truthy()),
  )
}

///|
fn init_solve() -> Unit raise {
  putprop(
    q_p_sec,
    lfunc("%sec-trig-cannon", args => solve__p_sec_trig_cannon(arg(args, 0))),
    q_trig_cannon,
  )
  |> ignore
  putprop(
    q_p_csc,
    lfunc("%csc-trig-cannon", args => solve__p_csc_trig_cannon(arg(args, 0))),
    q_trig_cannon,
  )
  |> ignore
  putprop(
    q_p_tan,
    lfunc("%tan-trig-cannon", args => solve__p_tan_trig_cannon(arg(args, 0))),
    q_trig_cannon,
  )
  |> ignore
  putprop(
    q_p_cot,
    lfunc("%cot-trig-cannon", args => solve__p_cot_trig_cannon(arg(args, 0))),
    q_trig_cannon,
  )
  |> ignore
  putprop(
    q_p_sech,
    lfunc("%sech-trig-cannon", args => solve__p_sech_trig_cannon(arg(args, 0))),
    q_trig_cannon,
  )
  |> ignore
  putprop(
    q_p_csch,
    lfunc("%csch-trig-cannon", args => solve__p_csch_trig_cannon(arg(args, 0))),
    q_trig_cannon,
  )
  |> ignore
  putprop(
    q_p_tanh,
    lfunc("%tanh-trig-cannon", args => solve__p_tanh_trig_cannon(arg(args, 0))),
    q_trig_cannon,
  )
  |> ignore
  putprop(
    q_p_coth,
    lfunc("%coth-trig-cannon", args => solve__p_coth_trig_cannon(arg(args, 0))),
    q_trig_cannon,
  )
  |> ignore
  // (setq broken-not-freeof nil)
  set(q_broken_not_freeof, Nil) |> ignore
}
