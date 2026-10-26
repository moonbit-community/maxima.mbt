// Port of src/trans3.lisp: the translation of macsyma LAMBDA into lexicaly
// scoped closures.
//
// A function to determine free vars from a lisp expression. It returns a
// <var-set> which is a list of pairs (<var> . <side-effectp>).

///|
/// FREE-LISP-VARS
fn free_lisp_vars(exp_ : Value) -> Value raise {
  if atom(exp_) {
    if exp_ is Nil || eq(t, exp_) {
      Nil
    } else if symbolp(exp_) {
      list1(cons(exp_, Nil))
    } else {
      Nil
    }
  } else if atom(car(exp_)) {
    let prop = get(car(exp_), q_free_lisp_vars)
    if prop.truthy() {
      return funcall(prop, [exp_])
    }
    let prop = get(car(exp_), q_macro)
    if prop.truthy() {
      return free_lisp_vars(funcall(prop, [exp_]))
    }
    if getl(car(exp_), list2(q_fsubr, q_fexpr)).truthy() {
      warn_fexpr(car(exp_), comment=Str("environment may fail to be correct."))
      |> ignore
      free_lisp_vars_of_argl(cdr(exp_))
    } else {
      free_lisp_vars_of_argl(cdr(exp_))
    }
  } else if eq(caar(exp_), q_lambda) {
    sum_var_sets(
      list2(free_lisp_vars(car(exp_)), free_lisp_vars_of_argl(cdr(exp_))),
    )
  } else {
    barfo(
      Str("encountered an unrecognized Lisp expression in FREE-LISP-VARS."),
    )
  }
}

///|
/// FREE-LISP-VARS-OF-ARGL
fn free_lisp_vars_of_argl(argl : Value) -> Value raise {
  union_var_set(mapcar(x => free_lisp_vars(x), argl))
}

///|
/// REDUCE-VAR-SET&OP: mult-set reduction.
/// (REDUCE-VAR-SET '((A . NIL) NIL (B . T) (B . NIL))) => ((A . NIL) (B . T))
fn reduce_var_set_ampop(var_set : Value, op : Value) -> Value raise {
  let mut reduced : Value = Nil
  for var1 in var_set.iter() {
    if var1 is Nil {
      continue
    }
    let var2 = assq(car(var1), reduced)
    if var2.truthy() {
      rplacd(var2, funcall(op, [cdr(var1), cdr(var2)])) |> ignore
    } else {
      reduced = cons(var1, reduced)
    }
  }
  reduced
}

///|
let trans3__or2 : Value = lfunc("reduce-var-set-or", args => {
  let p1 = arg(args, 0)
  if p1.truthy() {
    p1
  } else {
    arg(args, 1)
  }
})

///|
/// REDUCE-VAR-SET
fn reduce_var_set(var_set : Value) -> Value raise {
  reduce_var_set_ampop(var_set, trans3__or2)
}

///|
/// DIFFERENCE-VAR-SETS: S1 - S2. S1 reduced, minus any vars that are in S2.
fn difference_var_sets(s1 : Value, s2 : Value) -> Value raise {
  let s1 = reduce_var_set(s1)
  let mut s : Value = Nil
  for e in s1.iter() {
    if assq(car(e), s2) is Nil {
      s = cons(e, s)
    }
  }
  s
}

///|
/// `(apply #'append lists)`: all lists but the last are copied.
fn trans3__append_all(lists : Value) -> Value {
  match lists {
    Nil => Nil
    Cons({ car: l, cdr: Nil }) => l
    Cons({ car: l, cdr: rest }) => append(l, trans3__append_all(rest))
    _ => Nil
  }
}

///|
/// UNION-VAR-SET: union of var sets is defined classicaly ala G.F.
fn union_var_set(set_of_var_sets : Value) -> Value raise {
  reduce_var_set(trans3__append_all(set_of_var_sets))
}

///|
/// SUM-VAR-SETS is the usual convention.
fn sum_var_sets(l : Value) -> Value raise {
  reduce_var_set(trans3__append_all(l))
}

///|
/// MAKE-VAR-SET
fn make_var_set(vars : Value) -> Value raise {
  mapcar(v => list1(v), vars)
}

///|
/// (LAMBDA <BVL> . <BODY>)
fn trans3__flv_lambda(form : Value) -> Value raise {
  difference_var_sets(
    // get free lisp vars from body forms
    free_lisp_vars_of_argl(cddr(form)),
    // get vars bound by LAMBDA
    make_var_set(cadr(form)),
  )
}

///|
/// Free vars of the init forms of a binding list.
fn trans3__init_forms_vars(bvl : Value) -> Value raise {
  union_var_set(
    mapcar(e => if consp(e) { free_lisp_vars(cadr(e)) } else { Nil }, bvl),
  )
}

///|
/// Free vars of body forms, skipping go tags.
fn trans3__tagbody_vars(body : Value) -> Value raise {
  union_var_set(
    mapcar(
      e => if go_tag_p(e).truthy() { Nil } else { free_lisp_vars(e) },
      body,
    ),
  )
}

///|
/// The variables bound by a binding list.
fn trans3__bound_vars(bvl : Value) -> Value raise {
  make_var_set(mapcar(e => if atom(e) { e } else { car(e) }, bvl))
}

///|
/// (PROG <BVLSPEC> . <BODY>)
fn trans3__flv_prog(form : Value) -> Value raise {
  let a = trans3__init_forms_vars(cadr(form))
  let b = difference_var_sets(
    trans3__tagbody_vars(cddr(form)),
    trans3__bound_vars(cadr(form)),
  )
  sum_var_sets(list2(a, b))
}

///|
/// (LET <BVLSPEC> . <BODY>)
fn trans3__flv_let(form : Value) -> Value raise {
  let a = trans3__init_forms_vars(cadr(form))
  let b = difference_var_sets(
    free_lisp_vars_of_argl(cddr(form)),
    trans3__bound_vars(cadr(form)),
  )
  sum_var_sets(list2(a, b))
}

///|
/// (DO (<VARSPEC> ...) (<END-TEST-FORM> . <RESULT-FORMS>) . <BODY>)
fn trans3__flv_do(form : Value) -> Value raise {
  let a = trans3__init_forms_vars(cadr(form))
  let body = trans3__tagbody_vars(cdddr(form))
  let end_ = free_lisp_vars_of_argl(caddr(form))
  let steps = union_var_set(
    mapcar(e => if consp(e) { free_lisp_vars(caddr(e)) } else { Nil }, cadr(form)),
  )
  let b = difference_var_sets(
    sum_var_sets(list3(body, end_, steps)),
    trans3__bound_vars(cadr(form)),
  )
  sum_var_sets(list2(a, b))
}

///|
/// (COND (<I> ..) (<J> ..) ...)
fn trans3__flv_cond(form : Value) -> Value raise {
  union_var_set(mapcar(x => free_lisp_vars_of_argl(x), cdr(form)))
}

///|
/// (SETQ ... ODD AND EVENS...)
fn trans3__flv_setq(form : Value) -> Value raise {
  let mut free_vars : Value = Nil
  let mut form = cdr(form)
  while form is Cons(_) {
    free_vars = sum_var_sets(
      list3(list1(cons(car(form), t)), free_lisp_vars(cadr(form)), free_vars),
    )
    form = cddr(form)
  }
  free_vars
}

///|
/// TRD-MSYMEVAL: generated by TRANSLATE.
fn trans3__flv_trd_msymeval(form : Value) -> Value raise {
  if get(cadr(form), q_sort_of_lexical).truthy() {
    // acts like a lexical variable because of the $SUBSTPART translator.
    list1(list1(cadr(form)))
  } else {
    Nil
  }
}

///|
/// FREE-LISP-VARS-M-TLAMBDA: the various augmented lambda forms.
fn free_lisp_vars_m_tlambda(form : Value) -> Value raise {
  difference_var_sets(
    free_lisp_vars_of_argl(cddr(form)),
    free_lisp_vars_of_argl(cadr(form)),
  )
}

///|
/// FREE-LISP-VARS-M-TLAMBDA&ENV
fn free_lisp_vars_m_tlambda_ampenv(form : Value) -> Value raise {
  difference_var_sets(
    free_lisp_vars_of_argl(cddr(form)),
    free_lisp_vars_of_argl(car(cadr(form))),
  )
}

///|
/// TBOUND-FREE-VARS: takes a FREE-VAR list and returns a list of two
/// lists: the tbound free vars and the tbound free vars that are side
/// effected also.
fn tbound_free_vars(free_varl : Value) -> Value raise {
  let mut free : Value = Nil
  let mut free_s : Value = Nil
  for v in free_varl.iter() {
    if tboundp(car(v)).truthy() && tr_get_special(car(v)) is Nil {
      free = cons(car(v), free)
      if cdr(v).truthy() {
        free_s = cons(car(v), free_s)
      }
    }
  }
  list2(free, free_s)
}

///|
/// SIDE-EFFECT-FREE-CHECK
fn side_effect_free_check(varl : Value, form : Value) -> Value raise {
  if varl is Nil {
    t
  } else {
    tr_format(
      Str("error: unsupported side effects on ~:M in expression ~M~%"),
      list2(cons(list1(q_mlist), varl), form),
    )
    |> ignore
    Nil
  }
}

///|
/// DEF%TR LAMBDA
fn trans3__tr_lambda(form : Value) -> Value raise {
  gen_tr_lambda(form)
}

///|
/// GEN-TR-LAMBDA: we keep a pointer to the original FORM so that we can
/// generate messages with it if need be.
fn gen_tr_lambda(form : Value) -> Value raise {
  if d_listp(cadr(form)) is Nil {
    tr_format(
      Str("error: first argument of lambda expression must be a list; found ~M"),
      list1(cadr(form)),
    )
    |> ignore
    tr_abort() |> ignore
    return Nil
  }
  if cddr(form) is Nil {
    tr_format(Str("error: empty body in lambda expression.~%"), Nil) |> ignore
    tr_abort() |> ignore
    return Nil
  }
  let mut arg_info = mapcar(
    v => if mdefparam(v).truthy() {
      Nil
    } else if op_equalp(v, list1(q_mlist)).truthy() &&
      mdefparam(cadr(v)).truthy() &&
      cddr(v) is Nil {
      t
    } else {
      q_ear_bad
    },
    cdr(cadr(form)),
  )
  let mut t_form : Value = Nil
  let mut frees : Value = Nil
  if memq(q_ear_bad, arg_info).truthy() ||
    (memq(t, arg_info).truthy() && cdr(memq(t, arg_info)).truthy()) {
    // the &REST is not the last one.
    tr_format(
      Str("error: unsupported argument list ~:M in lambda expression.~%"),
      list1(cadr(form)),
    )
    |> ignore
    tr_abort() |> ignore
  } else {
    let dup = find_duplicate(cdadr(form), test_=q_eq, key=q_mparam)
    if dup.truthy() {
      tr_format(
        Str("error: ~M occurs more than once in lambda expression parameter list"),
        list1(mparam(dup)),
      )
      |> ignore
      tr_abort() |> ignore
    } else {
      // &RESTP
      arg_info = memq(t, arg_info)
      t_form = tr_lambda(
        cons(
          list1(q_lambda),
          cons(
            cons(
              list1(q_mlist),
              mapcar(v => if atom(v) { v } else { cadr(v) }, cdr(cadr(form))),
            ),
            cddr(form),
          ),
        ),
        Nil,
      )
      t_form = cdr(t_form)
      frees = tbound_free_vars(free_lisp_vars(t_form))
    }
  }
  if car(frees) is Nil {
    let tlambda = if arg_info.truthy() { q_m_tlambda_amp } else { q_m_tlambda }
    cons(q_d_any, cons(tlambda, cons(cadr(t_form), cddr(t_form))))
  } else if cadr(frees) is Nil {
    let tlambda = if arg_info.truthy() {
      q_m_tlambda_ampenv_amp
    } else {
      q_m_tlambda_ampenv
    }
    let fvl = car(frees)
    let cfvl = intersection(fvl, symval(q_ear_tr_free_vars_to_capture))
    cons(
      q_d_any,
      cons(tlambda, cons(list3(cadr(t_form), fvl, cfvl), cddr(t_form))),
    )
  } else {
    warn_meval(form) |> ignore
    side_effect_free_check(cadr(frees), form) |> ignore
    punt_to_meval(form)
  }
}

///|
fn init_trans3() -> Unit raise {
  let deflv = fn(name : Value, f : (Value) -> Value raise) raise {
    putprop(
      name,
      lfunc(symbol_name(name) + "-free-lisp-vars", args => f(arg(args, 0))),
      q_free_lisp_vars,
    )
    |> ignore
  }
  for name in [q_declare, q_function, q_go, q_quote] {
    deflv(name, _ => Nil)
  }
  deflv(q_lambda, trans3__flv_lambda)
  deflv(q_prog, trans3__flv_prog)
  deflv(q_let, trans3__flv_let)
  deflv(q_do, trans3__flv_do)
  deflv(q_cond, trans3__flv_cond)
  deflv(q_setq, trans3__flv_setq)
  deflv(q_and, form => free_lisp_vars_of_argl(cdr(form)))
  deflv(q_or, form => free_lisp_vars_of_argl(cdr(form)))
  putprop(q_d_piece, t, q_sort_of_lexical) |> ignore
  deflv(q_trd_msymeval, trans3__flv_trd_msymeval)
  // it is not strictly known if the name of the function being called is a
  // variable or not. lets say its not.
  deflv(q_mfunction_call, form => free_lisp_vars_of_argl(cddr(form)))
  // (FUNGEN&ENV-FOR-MEVAL () () EXP)
  deflv(q_fungen_ampenv_for_meval, form => free_lisp_vars(car(cdddr(form))))
  for u in [q_m_tlambda, q_m_tlambda_amp] {
    putprop(u, q_free_lisp_vars_m_tlambda, q_free_lisp_vars) |> ignore
  }
  putprop(q_m_tlambda_ampenv, q_free_lisp_vars_m_tlambda_ampenv, q_free_lisp_vars)
  |> ignore
  putprop(
    q_m_tlambda_ampenv_amp,
    q_free_lisp_vars_m_tlambda_ampenv,
    q_free_lisp_vars,
  )
  |> ignore
  transl__deftr(q_lambda, trans3__tr_lambda)
}
