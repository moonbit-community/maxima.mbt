// Port of share/contrib/unit/unit-functions.lisp: Lisp support for the
// unit package (unit.mac).
//
// Loading the file redefines TOPLEVEL-MACSYMA-EVAL (to run the functions
// in pre_eval_functions and post_eval_functions), KILL1 (so that kill(all)
// and kill(post_eval_functions) reset them), $LETSIMP (binding
// unitformatresults to false) and NFORMAT (displaying products with units
// grouped). The port installs the redefinitions in the function cells of
// the core (`macsys__toplevel_macsyma_eval_cell`, `suprv1__kill1_cell`,
// `nforma__nformat_cell`, the MFEXPR* property of $letsimp).

///|
/// Redefinition of TOPLEVEL-MACSYMA-EVAL for post_eval_functions.
fn share_unit_functions__toplevel_macsyma_eval(x : Value) -> Value raise {
  let mut x = x
  for fi in margs(symval(q_d_pre_eval_functions)).iter() {
    x = mfuncall(fi, list1(x))
  }
  x = meval_star(x)
  for fi in margs(symval(q_d_post_eval_functions)).iter() {
    x = mfuncall(fi, list1(x))
  }
  x
}

///|
/// Redefinition of KILL1, to be able to properly reset post_eval_functions
/// with kill(all) and kill(post_eval_functions).
fn share_unit_functions__kill1(x : Value) -> Value raise {
  let mut z : Value = Nil
  let allbutl = symval(q_allbutl)
  if allbutl.truthy() && memq(x, allbutl).truthy() {
    return Nil
  }
  let x = getopr(x)
  if eq(x, q_d_labels) {
    for u in cdr(symval(q_d_labels)).iter() {
      let allbutl = symval(q_allbutl)
      if allbutl.truthy() && memq(u, allbutl).truthy() {
        z = nconc(z, list1(u))
      } else {
        makunbound(u) |> ignore
        remprop(u, q_time) |> ignore
        remprop(u, q_nodisp) |> ignore
      }
    }
    set(q_d_labels, cons(list2(q_mlist, q_simp), z)) |> ignore
    set(q_d_linenum, int(0)) |> ignore
    set(q_dcount, int(0)) |> ignore
  } else if memq(
      x,
      list([
        q_d_values, q_d_arrays, q_d_aliases, q_d_rules, q_d_props, q_d_let_rule_packages,
      ]),
    ).truthy() {
    for y in cdr(symval(x)).iter() {
      kill1(y) |> ignore
    }
  } else if memq(
      x,
      list([q_d_functions, q_d_macros, q_d_gradefs, q_d_dependencies, q_d_structures]),
    ).truthy() {
    for y in cdr(symval(x)).iter() {
      kill1(caar(y)) |> ignore
    }
  } else if eq(x, q_d_myoptions) {
    ()
  } else if eq(x, q_d_tellrats) {
    set(q_tellratlist, Nil) |> ignore
  } else if eq(x, q_d_ratweights) {
    set(q_n_starratweights, Nil) |> ignore
    set(q_d_ratweights, list1(list2(q_mlist, q_simp))) |> ignore
  } else if eq(x, q_d_features) {
    if !equal(cdr(symval(q_d_features)), symval(q_featurel)) {
      set(
        q_d_features,
        cons(list2(q_mlist, q_simp), copy_list(symval(q_featurel))),
      )
      |> ignore
    }
  } else if eq(x, q_d_pre_eval_functions) {
    set(q_d_pre_eval_functions, list1(list1(q_mlist))) |> ignore
  } else if eq(x, q_d_post_eval_functions) {
    set(q_d_post_eval_functions, list1(list1(q_mlist))) |> ignore
  } else if eq(x, t) || eq(x, q_d_all) {
    set(q_d_pre_eval_functions, list1(list1(q_mlist))) |> ignore
    set(q_d_post_eval_functions, list1(list1(q_mlist))) |> ignore
    for y in cdr(symval(q_d_infolists)).iter() {
      kill1(y) |> ignore
    }
    set(q_d_ratvars, list1(list2(q_mlist, q_simp))) |> ignore
    set(q_varlist, Nil) |> ignore
    set(q_genvar, Nil) |> ignore
    set(q_checkfactors, Nil) |> ignore
    set(q_greatorder, Nil) |> ignore
    set(q_lessorder, Nil) |> ignore
    set(q_d_gensumnum, int(0)) |> ignore
    set(q_n_starratweights, Nil) |> ignore
    set(q_d_ratweights, list1(list2(q_mlist, q_simp))) |> ignore
    set(q_tellratlist, Nil) |> ignore
    set(q_d_dontfactor, list1(list1(q_mlist))) |> ignore
    set(q_d_setcheck, Nil) |> ignore
    killallcontexts() |> ignore
  } else {
    // the remaining clauses ($inlabels ..., label numbers, atoms, arrays,
    // allbut) are those of the core KILL1
    return suprv1__kill1_rest(x)
  }
  Nil
}

///|
/// Returns t if expression contains units, nil otherwise.
fn notunitfree(form : Value) -> Value raise {
  if atom(form) {
    d_member(form, symval(q_d_allunitslist))
  } else if car(form) is Nil {
    Nil
  } else if atom(car(form)) {
    let v = d_member(car(form), symval(q_d_allunitslist))
    if v.truthy() {
      v
    } else {
      notunitfree(cdr(form))
    }
  } else {
    let v = notunitfree(cdr(car(form)))
    if v.truthy() {
      v
    } else {
      notunitfree(cdr(form))
    }
  }
}

///|
/// Code to optionally group units by common unit.
fn unitmember(form : Value, list1_ : Value) -> Value raise {
  if equal(car(list1_), Nil) {
    Nil
  } else if equal(form, car(list1_)) {
    t
  } else {
    unitmember(form, cdr(list1_))
  }
}

///|
/// The coefficient difference test of GROUPBYADDLISP: are the units of the
/// first two terms equal?
fn share_unit_functions__same_unit(form : Value) -> Bool raise {
  equal(
    meval(
      list([
        list2(q_mplus, q_simp),
        caddr(car(form)),
        list([list2(q_mtimes, q_simp), int(-1), caddr(cadr(form))]),
      ]),
    ),
    int(0),
  )
}

///|
fn share_unit_functions__sum_coeffs(form : Value) -> Value raise {
  meval(list([list2(q_mplus, q_simp), cadr(car(form)), cadr(cadr(form))]))
}

///|
fn groupbyaddlisp(form : Value) -> Value raise {
  if !notunitfree(car(form)).truthy() || !notunitfree(cadr(form)).truthy() {
    form
  } else if cddr(form) is Nil && share_unit_functions__same_unit(form) {
    list1(
      list([
        list1(q_mtimes),
        share_unit_functions__sum_coeffs(form),
        caddr(car(form)),
      ]),
    )
  } else if cddr(form) is Nil {
    form
  } else if share_unit_functions__same_unit(form) {
    groupbyaddlisp(
      cons(
        list([
          list1(q_mtimes),
          share_unit_functions__sum_coeffs(form),
          caddr(car(form)),
        ]),
        cddr(form),
      ),
    )
  } else {
    cons(
      list([list1(q_mtimes), cadr(car(form)), caddr(car(form))]),
      groupbyaddlisp(cdr(form)),
    )
  }
}

///|
fn groupadd(form : Value) -> Value raise {
  if !atom(form) && notunitfree(form).truthy() && equal(caar(form), q_mplus) {
    let temp1 = groupbyaddlisp(cdr(nformat(form)))
    if !equal(cdr(temp1), Nil) ||
      (atom(cadr(temp1)) && !equal(cadr(temp1), Nil)) {
      cons(list1(q_mplus), temp1)
    } else if equal(cdr(temp1), Nil) {
      car(temp1)
    } else {
      Nil
    }
  } else {
    form
  }
}

///|
/// Returns t if expression contains only units, nil otherwise.
fn onlyunits(form : Value) -> Value raise {
  if car(form) is Nil {
    t
  } else if atom(car(form)) {
    if d_member(car(form), symval(q_d_allunitslist)).truthy() {
      onlyunits(cdr(form))
    } else {
      Nil
    }
  } else if onlyunits(list1(car(cdr(car(form))))).truthy() {
    onlyunits(cdr(form))
  } else {
    Nil
  }
}

///|
/// Returns a list containing all unit terms.
fn getunits(form : Value) -> Value raise {
  if cadr(form) is Nil {
    Nil
  } else {
    let rest = cons(car(form), cdr(cdr(form)))
    let key = if atom(cadr(form)) { cadr(form) } else { cadr(cadr(form)) }
    if d_member(key, symval(q_d_allunitslist)).truthy() {
      cons(cadr(form), getunits(rest))
    } else {
      getunits(rest)
    }
  }
}

///|
/// Returns a list containing all non-unit terms.
fn nonunits(form : Value) -> Value raise {
  if cadr(form) is Nil {
    Nil
  } else {
    let rest = cons(car(form), cdr(cdr(form)))
    let key = if atom(cadr(form)) { cadr(form) } else { cadr(cadr(form)) }
    if !d_member(key, symval(q_d_allunitslist)).truthy() {
      cons(cadr(form), nonunits(rest))
    } else {
      nonunits(rest)
    }
  }
}

///|
fn unitmtimeswrapper(form : Value) -> Value raise {
  if notunitfree(form).truthy() &&
    !onlyunits(cdr(form)).truthy() &&
    !equal(list1(int(-1)), nonunits(form)) &&
    equal(symval(q_d_unitformatresults), t) {
    list([
      list1(q_mtimes),
      cons(list2(q_mtimes, q_simp), nonunits(form)),
      cons(list2(q_mtimes, q_simp), getunits(form)),
    ])
  } else if onlyunits(cdr(form)).truthy() {
    form_mtimes(form)
  } else {
    form_mtimes(form)
  }
}

///|
/// Redefinition of NFORMAT: code to enable correct display of
/// multiplication by units.
fn share_unit_functions__nformat(form : Value) -> Value raise {
  if atom(form) {
    if numberp(form) && minusp(form) {
      list2(list1(q_mminus), num_neg(form))
    } else if eq(t, form) {
      if symval(q_in_p).truthy() {
        t
      } else {
        q_d_true
      }
    } else if form is Nil {
      if symval(q_in_p).truthy() {
        Nil
      } else {
        q_d_false
      }
    } else {
      form
    }
  } else if atom(car(form)) {
    form
  } else if eq(q_rat, caar(form)) {
    if minusp(cadr(form)) {
      list2(list1(q_mminus), list([list1(q_rat), num_neg(cadr(form)), caddr(form)]))
    } else {
      cons(list1(q_rat), cdr(form))
    }
  } else if eq(q_mmacroexpanded, caar(form)) {
    nformat(caddr(form))
  } else if cdar(form) is Nil {
    form
  } else if eq(q_mplus, caar(form)) {
    form_mplus(form)
  } else if eq(q_mtimes, caar(form)) {
    unitmtimeswrapper(form)
  } else if eq(q_mexpt, caar(form)) {
    form_mexpt(form)
  } else if eq(q_mrat, caar(form)) {
    form_mrat(form)
  } else if eq(q_mpois, caar(form)) {
    nformat(d_outofpois(form))
  } else if eq(q_bigfloat, caar(form)) {
    if minusp(cadr(form)) {
      list2(list1(q_mminus), list([car(form), num_neg(cadr(form)), caddr(form)]))
    } else {
      cons(car(form), cdr(form))
    }
  } else {
    form
  }
}

///|
fn init_share_unit_functions() -> Unit raise {
  // Redefining toplevel-macsyma-eval for post_eval_functions; define the
  // finaleval list.
  let list_of_symbols = lfunc("unit-eval-functions-predicate", args => {
    let val = arg(args, 0)
    lbool(d_listp(val).truthy() && every(x => symbolp(x), margs(val)))
  })
  defmvar(
    q_d_pre_eval_functions,
    val=list1(list1(q_mlist)),
    list([sym(":setting-predicate"), list_of_symbols]),
  )
  |> ignore
  defmvar(
    q_d_post_eval_functions,
    val=list1(list1(q_mlist)),
    list([sym(":setting-predicate"), list_of_symbols]),
  )
  |> ignore
  macsys__toplevel_macsyma_eval_cell.val = Some(share_unit_functions__toplevel_macsyma_eval)
  suprv1__kill1_cell.val = Some(share_unit_functions__kill1)
  // Define a couple variables specific to this code
  defmvar(q_d_allunitslist, val=list1(list1(q_mlist)), Nil) |> ignore
  defmvar(q_d_unitformatresults, val=t, Nil) |> ignore
  // Ensure that units formatting isn't invoked by letsimp. Unless
  // unitformatresults is bound to NIL, letsimp runs into an infinite
  // recursion via NFORMAT.
  let builtin_letsimp = get(q_d_letsimp, q_mfexpr_star)
  putprop(
    q_d_letsimp,
    lfunc("$letsimp", args => with_special(q_d_unitformatresults, Nil, () => funcall(
      builtin_letsimp,
      [arg(args, 0)],
    ))),
    q_mfexpr_star,
  )
  |> ignore
  nforma__nformat_cell.val = Some(share_unit_functions__nformat)
}
