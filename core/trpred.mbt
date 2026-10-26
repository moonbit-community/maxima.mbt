// Port of src/trpred.lisp: translation of predicates ($is, $maybe, mcond
// conditions, and, or, not, comparisons).

///|
/// WRAP-PRED
fn wrap_pred(form : Value, evalp? : Value = t) -> Value raise {
  let boole_fun = get(
    symval(q_wrap_a_pred),
    if evalp.truthy() {
      q_tr_boole_eval
    } else {
      q_tr_boole_verify
    },
  )
  cons(q_d_any, list2(boole_fun, form))
}

///|
/// TR-IS/MAYBE
fn tr_is_slmaybe(wrap_type : Value, form : Value) -> Value raise {
  let tr = with_special(q_wrap_a_pred, wrap_type, () => translate_predicate(
    form,
  ))
  let mode = car(tr)
  let tr_form = cdr(tr)
  if eq(mode, q_d_boolean) {
    tr
  } else {
    cons(q_d_any, tr_form)
  }
}

///|
/// DEF%TR MNOTEQUAL (and the other relations): these don't have an
/// imperative predicate semantics outside of being used in MNOT, MAND, MOR,
/// MCOND, $IS.
fn trpred__tr_mnotequal(form : Value) -> Value raise {
  cons(
    q_d_any,
    list2(
      q_simplify,
      cons(q_list, cons(transl__quote(list1(caar(form))), tr_args(cdr(form)))),
    ),
  )
}

///|
/// TRANSLATE-PREDICATE
fn translate_predicate(form : Value) -> Value raise {
  if atom(form) {
    return trp_with_boolean_convert(form)
  }
  let op = caar(form)
  if eq(q_mnot, op) {
    trp_mnot(form)
  } else if eq(q_mand, op) {
    trp_mand(form)
  } else if eq(q_mor, op) {
    trp_mor(form)
  } else if eq(q_mnotequal, op) {
    trp_mnotequal(form)
  } else if eq(q_mequal, op) {
    trp_mequal(form)
  } else if eq(q_d_equal, op) {
    trp__dolequal(form)
  } else if eq(q_d_notequal, op) {
    trp__dolnotequal(form)
  } else if eq(q_mgreaterp, op) {
    trp_mgreaterp(form)
  } else if eq(q_mgeqp, op) {
    trp_mgeqp(form)
  } else if eq(q_mlessp, op) {
    trp_mlessp(form)
  } else if eq(q_mleqp, op) {
    trp_mleqp(form)
  } else if eq(q_mprogn, op) {
    // it was a pain not to have this case working, so I just patched it in.
    let exprs = cdr(form)
    let r = translate_predicate(car(last(exprs)))
    let mode = car(r)
    let last_ = cdr(r)
    cons(
      mode,
      cons(q_progn, append(tr_args(butlast(exprs)), list1(last_))),
    )
  } else {
    trp_with_boolean_convert(form)
  }
}

///|
/// TRP-WITH-BOOLEAN-CONVERT
fn trp_with_boolean_convert(form : Value) -> Value raise {
  let tr = translate(form)
  if eq(car(tr), q_d_boolean) {
    tr
  } else {
    wrap_pred(cdr(tr))
  }
}

///|
/// MNOT_TR expander: `(mnot_tr operand)`.
fn mnot_tr(operand : Value) -> Value raise {
  list3(q_is_mnot, list2(q_function, q_identity), operand)
}

///|
/// TRP-MNOT
fn trp_mnot(form : Value) -> Value raise {
  let exp_ = cadr(form)
  if exp_ is Nil {
    cons(q_d_boolean, t)
  } else if eq(t, exp_) {
    cons(q_d_boolean, Nil)
  } else if !atom(exp_) && eq(caar(exp_), q_mnot) {
    translate_predicate(cadr(exp_))
  } else {
    let r = translate_predicate(exp_)
    let mode = car(r)
    let operand = cdr(r)
    if eq(mode, q_d_boolean) {
      cons(mode, list2(q_not, operand))
    } else {
      wrap_pred(list2(q_mnot_tr, operand), evalp=Nil)
    }
  }
}

///|
/// MAND/MOR_TR: the expansion of the MAND_TR / MOR_TR macros.
fn mand_slmor_tr(mop : Value, operands : Value, top : Value, bot : Value) -> Value raise {
  let val = tr_gensym()
  let ext = tr_gensym()
  let mut acc = list4(
    q_cond,
    list2(list2(q_null, ext), top),
    list2(list2(q_null, list2(q_cdr, ext)), list2(q_car, ext)),
    list2(t, list3(q_cons, transl__quote(list1(mop)), list2(q_nreverse, ext))),
  )
  // (reduce ... :from-end t :initial-value ...)
  for x in list_to_array(operands).rev_iter() {
    acc = list3(
      q_cond,
      list2(list3(q_eq, list3(q_setq, val, x), bot), bot),
      list3(
        t,
        list3(q_unless, list3(q_eq, val, top), list3(q_push, val, ext)),
        acc,
      ),
    )
  }
  list3(q_let, list2(list2(val, Nil), list2(ext, transl__quote(Nil))), acc)
}

///|
/// MAND_TR expander: `(mand_tr . operands)`.
fn mand_tr(operands : Value) -> Value raise {
  mand_slmor_tr(q_mand, operands, t, Nil)
}

///|
/// MOR_TR expander: `(mor_tr . operands)`.
fn mor_tr(operands : Value) -> Value raise {
  mand_slmor_tr(q_mor, operands, Nil, t)
}

///|
/// SIMPLIFY-MAND/MOR-OPERANDS_TR
fn simplify_mand_slmor_operands_tr(
  operands : Value,
  top : Value,
  bot : Value,
) -> Value raise {
  let c = Collector::new()
  for o in operands.iter() {
    if !eq(o, top) {
      c.add(o)
    }
    if eq(o, bot) {
      break
    }
  }
  c.result()
}

///|
/// MAP-TRP
fn map_trp(l : Value) -> Value raise {
  let mut a = cons(Nil, Nil)
  for x in list_to_array(l).rev_iter() {
    let r = translate_predicate(x)
    a = cons(n_starunion_mode(car(a), car(r)), cons(cdr(r), cdr(a)))
  }
  a
}

///|
/// TRP-MAND/MOR
fn trp_mand_slmor(
  operands : Value,
  lisp_op : Value,
  max_op : Value,
  top : Value,
  bot : Value,
) -> Value raise {
  let operands = simplify_mand_slmor_operands_tr(operands, top, bot)
  if operands is Nil {
    cons(q_d_boolean, top)
  } else if cdr(operands) is Nil {
    trp_with_boolean_convert(car(operands))
  } else {
    let r = map_trp(operands)
    let mode = car(r)
    let tr_operands = cdr(r)
    if eq(mode, q_d_boolean) {
      cons(mode, cons(lisp_op, tr_operands))
    } else {
      wrap_pred(cons(max_op, tr_operands), evalp=Nil)
    }
  }
}

///|
/// TRP-MAND
fn trp_mand(form : Value) -> Value raise {
  trp_mand_slmor(cdr(form), q_and, q_mand_tr, t, Nil)
}

///|
/// TRP-MOR
fn trp_mor(form : Value) -> Value raise {
  trp_mand_slmor(cdr(form), q_or, q_mor_tr, Nil, t)
}

///|
/// TRP-INEQUALITY
fn trp_inequality(args : Value, lisp_op : Value, max_op : Value) -> Value raise {
  let arg1 = translate(car(args))
  let arg2 = translate(cadr(args))
  let mode = n_starunion_mode(car(arg1), car(arg2))
  let number_types = symval(q_ear_number_types)
  if memq(mode, list2(q_d_fixnum, q_d_float)).truthy() ||
    (
      memq(car(arg1), number_types).truthy() &&
      memq(car(arg2), number_types).truthy()
    ) {
    cons(q_d_boolean, list3(lisp_op, dconv(arg1, mode), dconv(arg2, mode)))
  } else if eq(q_d_number, mode) {
    cons(q_d_boolean, list3(lisp_op, cdr(arg1), cdr(arg2)))
  } else {
    wrap_pred(list3(max_op, dconvx(arg1), dconvx(arg2)), evalp=Nil)
  }
}

///|
/// TRP-MLESSP
fn trp_mlessp(form : Value) -> Value raise {
  trp_inequality(cdr(form), q_op_lt, q_mlsp)
}

///|
/// TRP-MGREATERP
fn trp_mgreaterp(form : Value) -> Value raise {
  trp_inequality(cdr(form), q_op_gt, q_mgrp)
}

///|
/// TRP-MGEQP
fn trp_mgeqp(form : Value) -> Value raise {
  trp_inequality(cdr(form), q_op_gt_eq, q_mgqp)
}

///|
/// TRP-MLEQP: No mlqp in sight
fn trp_mleqp(form : Value) -> Value raise {
  translate_predicate(cons(list1(q_mgeqp), reverse(cdr(form))))
}

///|
/// TRP-MEQUAL
fn trp_mequal(form : Value) -> Value raise {
  let r1 = translate(cadr(form))
  let r2 = translate(caddr(form))
  let mode1 = car(r1)
  let arg1 = cdr(r1)
  let mode2 = car(r2)
  let arg2 = cdr(r2)
  cons(
    q_d_boolean,
    if covers(q_d_number, mode1).truthy() && covers(q_d_number, mode2).truthy() {
      list3(q_eql, arg1, arg2)
    } else {
      list3(q_like, arg1, arg2)
    },
  )
}

///|
/// TRP-MNOTEQUAL
fn trp_mnotequal(form : Value) -> Value raise {
  translate_predicate(
    list2(list1(q_mnot), cons(list1(q_mequal), cdr(form))),
  )
}

///|
/// TRP-$EQUALITY
fn trp__dolequality(args : Value, lisp_op : Value, max_op : Value) -> Value raise {
  let arg1 = translate(car(args))
  let arg2 = translate(cadr(args))
  let mode = n_starunion_mode(car(arg1), car(arg2))
  if memq(mode, list2(q_d_fixnum, q_d_float)).truthy() {
    cons(q_d_boolean, list3(lisp_op, dconv(arg1, mode), dconv(arg2, mode)))
  } else if eq(q_d_number, mode) {
    cons(q_d_any, list3(max_op, cdr(arg1), cdr(arg2)))
  } else {
    wrap_pred(list3(max_op, dconvx(arg1), dconvx(arg2)), evalp=Nil)
  }
}

///|
/// TRP-$EQUAL
fn trp__dolequal(form : Value) -> Value raise {
  trp__dolequality(cdr(form), q_op_eq, q_meqp)
}

///|
/// TRP-$NOTEQUAL
fn trp__dolnotequal(form : Value) -> Value raise {
  trp__dolequality(cdr(form), q_op_sl_eq, q_mnqp)
}

///|
/// DEF%TR $ASSUME: sigh, i have to copy a lot of the $assume function too.
fn trpred__tr_assume(form : Value) -> Value raise {
  let mut x = cdr(form)
  let mut nl : Value = Nil
  while x is Cons(_) {
    let a = car(x)
    if atom(a) {
      nl = cons(list2(q_assume, dtranslate(a)), nl)
    } else if eq(q_mand, caar(a)) {
      for l in cdr(a).iter() {
        nl = cons(list2(q_assume, dtranslate(l)), nl)
      }
    } else if eq(q_mnot, caar(a)) {
      nl = cons(list2(q_assume, dtranslate(pred_reverse(cadr(a)))), nl)
    } else if eq(q_mor, caar(a)) {
      merr("assume: argument cannot be an 'or' expression; found ~M", [a])
      |> ignore
    } else if eq(caar(a), q_mequal) {
      merr(
        "assume: argument cannot be an '=' expression; found ~M~%assume: maybe you want 'equal'.",
        [a],
      )
      |> ignore
    } else if eq(caar(a), q_mnotequal) {
      merr(
        "assume: argument cannot be a '#' expression; found ~M~%assume: maybe you want 'not equal'.",
        [a],
      )
      |> ignore
    } else {
      nl = cons(list2(q_assume, dtranslate(a)), nl)
    }
    x = cdr(x)
  }
  cons(
    q_d_any,
    list2(
      q_simplify,
      cons(q_list, cons(transl__quote(list1(q_mlist)), nreverse(nl))),
    ),
  )
}

///|
fn init_trpred() -> Unit raise {
  transl__deftr(q_d_is, form => tr_is_slmaybe(q_d_is, cadr(form)))
  transl__deftr(q_d_maybe, form => tr_is_slmaybe(q_d_maybe, cadr(form)))
  transl__deftr(q_mnotequal, trpred__tr_mnotequal)
  for name in [
    q_mequal, q_d_equal, q_d_notequal, q_mgreaterp, q_mgeqp, q_mlessp, q_mleqp,
  ] {
    transm__def_same_tr(name, q_mnotequal)
  }
  transl__deftr(q_d_assume, trpred__tr_assume)
}
