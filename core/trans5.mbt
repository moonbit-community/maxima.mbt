// Port of src/trans5.lisp: TRANSLATE properties for the FSUBRS in COMM
// and others.

///|
/// DEF%TR $DISP
fn trans5__tr_disp(form : Value) -> Value raise {
  cons(
    q_d_any,
    list_star([
      q_display_for_tr,
      lbool(eq(caar(form), q_d_ldisp)),
      // equationsp
      Nil,
      tr_args(cdr(form)),
    ]),
  )
}

///|
/// DEF%TR $DISPLAY
fn trans5__tr_display(form : Value) -> Value raise {
  cons(
    q_d_any,
    list_star([
      q_display_for_tr,
      lbool(eq(caar(form), q_d_ldisplay)),
      t,
      mapcar(x => tr_exp_to_display(x), cdr(form)),
    ]),
  )
}

///|
/// MAKE-VALUES: expressions which might have to get evaluated twice are
/// pushed on the VALUE-ALIST (<expression> . <gensym>).
fn make_values(expr_args : Value) -> Value raise {
  mapcar(
    arg => if atom(arg) || memq(car(arg), list2(q_trd_msymeval, q_quote)).truthy() {
      arg
    } else {
      let sym_ = gensym()
      set(q_value_alist, cons(cons(arg, sym_), symval(q_value_alist))) |> ignore
      sym_
    },
    expr_args,
  )
}

// (defstruct (disp-hack-ob (:conc-name nil) (:type list)) left-ob right-ob)

///|
fn trans5__make_ob(left_ob : Value, right_ob : Value) -> Value {
  list2(left_ob, right_ob)
}

///|
/// OBJECT-FOR-DISPLAY-HACK
fn object_for_display_hack(exp_ : Value) -> Value raise {
  if atom(exp_) {
    return trans5__make_ob(transl__quote(exp_), exp_)
  }
  let op = car(exp_)
  if eq(op, q_simplify) {
    let v = object_for_display_hack(cadr(exp_))
    trans5__make_ob(car(v), list2(q_simplify, cadr(v)))
  } else if eq(op, q_marrayref) {
    let vals = make_values(cdr(exp_))
    trans5__make_ob(
      cons(
        q_list,
        cons(list3(q_list_star, car(vals), transl__quote(list1(q_array))), cdr(vals)),
      ),
      cons(q_marrayref, vals),
    )
  } else if eq(op, q_mfunction_call) {
    // assume evaluation of arguments.
    let vals = make_values(cddr(exp_))
    trans5__make_ob(
      cons(q_list, cons(transl__quote(list1(cadr(exp_))), vals)),
      cons(q_mfunction_call, cons(cadr(exp_), vals)),
    )
  } else if eq(op, q_list) {
    let obs = mapcar(x => object_for_display_hack(x), cdr(exp_))
    trans5__make_ob(
      cons(q_list, mapcar(u => car(u), obs)),
      cons(q_list, mapcar(u => cadr(u), obs)),
    )
  } else if eq(op, q_quote) {
    trans5__make_ob(exp_, exp_)
  } else if eq(op, q_trd_msymeval) {
    trans5__make_ob(transl__quote(cadr(exp_)), exp_)
  } else if !atom(car(exp_)) ||
    getl(car(exp_), list([q_fsubr, q_fexpr, q_macro])).truthy() {
    trans5__make_ob(transl__quote(exp_), exp_)
  } else {
    let vals = make_values(cdr(exp_))
    trans5__make_ob(
      cons(q_list, cons(transl__quote(list1(untrans_op(car(exp_)))), vals)),
      cons(car(exp_), vals),
    )
  }
}

///|
/// TR-EXP-TO-DISPLAY
fn tr_exp_to_display(exp_ : Value) -> Value raise {
  let lisp_exp = dtranslate(exp_)
  let b = bind(q_value_alist, Nil)
  defer unbind(b)
  let ob = object_for_display_hack(lisp_exp)
  let disp = list4(q_list, transl__quote(list1(q_mequal)), car(ob), cadr(ob))
  set(q_value_alist, nreverse(symval(q_value_alist))) |> ignore
  let value_alist = symval(q_value_alist)
  if value_alist.truthy() {
    cons(
      list3(q_lambda, mapcar(x => cdr(x), value_alist), disp),
      mapcar(x => car(x), value_alist),
    )
  } else {
    disp
  }
}

///|
/// UNTRANS-OP
fn untrans_op(op : Value) -> Value raise {
  let a = assoc_equal(
    op,
    list([
      cons(q_add_star, q_mplus),
      cons(q_sub_star, q_mminus),
      cons(q_mul_star, q_mtimes),
      cons(q_div_star, q_mquotient),
      cons(q_power_star, q_mexpt),
    ]),
  )
  let r = cdr(a)
  if r.truthy() {
    r
  } else {
    op
  }
}

///|
/// DEF%TR $CF (from COMBIN)
fn trans5__tr_cf(form : Value) -> Value raise {
  let form = car(tr_args(cdr(form)))
  cons(
    q_d_any,
    list3(q_let, list1(list2(q_d_listarith, Nil)), list2(q_cfeval, form)),
  )
}

///|
/// DEF%TR $APPLY1 (from TRGRED)
fn trans5__tr_apply1(form : Value) -> Value raise {
  let expr = tr_gensym()
  let rules = tr_gensym()
  cons(
    q_d_any,
    list3(
      q_do,
      list2(
        list3(
          expr,
          dtranslate(cadr(form)),
          list4(q_apply1, expr, list2(q_car, rules), Fix(0L)),
        ),
        list3(rules, transl__quote(cddr(form)), list2(q_cdr, rules)),
      ),
      list2(list2(q_null, rules), expr),
    ),
  )
}

///|
/// DEF%TR $APPLY2
fn trans5__tr_apply2(form : Value) -> Value raise {
  cons(
    q_d_any,
    list4(q_apply2, transl__quote(cddr(form)), dtranslate(cadr(form)), Fix(0L)),
  )
}

///|
/// DEF%TR $APPLYB1
fn trans5__tr_applyb1(form : Value) -> Value raise {
  let expr = tr_gensym()
  let rules = tr_gensym()
  cons(
    q_d_any,
    list3(
      q_do,
      list2(
        list3(
          expr,
          dtranslate(cadr(form)),
          list2(q_car, list3(q_apply1hack, expr, list2(q_car, rules))),
        ),
        list3(rules, transl__quote(cddr(form)), list2(q_cdr, rules)),
      ),
      list2(list2(q_null, rules), expr),
    ),
  )
}

///|
/// DEF%TR $APPLYB2
fn trans5__tr_applyb2(form : Value) -> Value raise {
  cons(
    q_d_any,
    list2(
      q_car,
      list3(q_apply2hack, transl__quote(cddr(form)), dtranslate(cadr(form))),
    ),
  )
}

///|
/// DEF%TR $BUILDQ: this nice translation property written by REH.
fn trans5__tr_buildq(form : Value) -> Value raise {
  let alist = mapcar(
    var_ => if atom(var_) {
      list3(q_cons, transl__quote(var_), dtranslate(var_))
    } else if eq(caar(var_), q_msetq) {
      list3(q_cons, transl__quote(cadr(var_)), dtranslate(caddr(var_)))
    } else {
      tr_abort() |> ignore
      tr_format(
        Str("error: found unhandled variable ~:M in 'buildq'.~%"),
        list1(var_),
      )
    },
    cdr(cadr(form)),
  )
  if alist is Nil {
    list3(q_d_any, q_quote, caddr(form))
  } else {
    list4(
      q_d_any,
      q_mbuildq_subst,
      cons(q_list, alist),
      transl__quote(caddr(form)),
    )
  }
}

///|
fn init_trans5() -> Unit raise {
  transl__deftr(q_d_disp, trans5__tr_disp)
  transm__def_same_tr(q_d_ldisp, q_d_disp)
  transl__deftr(q_d_display, trans5__tr_display)
  transm__def_same_tr(q_d_ldisplay, q_d_display)
  transl__deftr(q_d_cf, trans5__tr_cf)
  transl__deftr(q_d_apply1, trans5__tr_apply1)
  transl__deftr(q_d_apply2, trans5__tr_apply2)
  transl__deftr(q_d_applyb1, trans5__tr_applyb1)
  transl__deftr(q_d_applyb2, trans5__tr_applyb2)
  transl__deftr(q_d_buildq, trans5__tr_buildq)
}
