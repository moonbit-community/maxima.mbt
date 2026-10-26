// Port of src/transl.lisp, part 2: LAMBDA, MPROG, MCOND, MDO, MSETQ ...
// translation properties, and the mode accessing/binding functions.

///|
/// DEF%TR $EVAL_WHEN
fn transl__tr_eval_when(form : Value) -> Value raise {
  tr_format(
    Str("error: found 'eval_when' in a function or expression: ~:M~%"),
    list1(form),
  )
  |> ignore
  tr_format(
    Str("note: 'eval_when' can appear only at the top level in a file.~%"),
    Nil,
  )
  |> ignore
  tr_abort() |> ignore
  cons(q_d_any, Nil)
}

///|
/// DEF%TR MDEFMACRO
fn transl__tr_mdefmacro(form : Value) -> Value raise {
  tr_format(
    Str(
      "warning: globally defining macro ~:M now to ensure correct macro expansions.~%",
    ),
    list1(car(car(car(cdr(form))))),
  )
  |> ignore
  // Define the macro now to ensure that it's defined when it's time to
  // expand it.
  meval(form) |> ignore
  punt_to_meval(form)
}

///|
/// DEF%TR $LOCAL
fn transl__tr_local(form : Value) -> Value raise {
  if symval(q_ear_local).truthy() {
    tr_format(Str("error: there is already a 'local' in this block.~%"), Nil)
    |> ignore
    tr_abort() |> ignore
    return Nil
  }
  set(q_ear_local, t) |> ignore
  // We can't just translate to a call to MLOCAL here. The push onto
  // LOCLIST and the binding of MLOCP are handled in TR-LAMBDA.
  punt_to_meval(form)
}

///|
/// DEF%TR MQUOTE
fn transl__tr_mquote(form : Value) -> Value raise {
  list3(tr_class(cadr(form)), q_quote, cadr(form))
}

///|
/// The function object for an ASSIGN property in generated code:
/// `(if (symbolp assign) `(quote ,assign) (coerce assign 'function))`.
fn transl__assign_fn(assign : Value) -> Value raise {
  if symbolp(assign) {
    transl__quote(assign)
  } else if assign is Func(_) {
    assign
  } else {
    lisp_eval_form(list2(q_function, assign))
  }
}

///|
/// TR-LAMBDA: take a simple macsyma lambda expression and return a simple
/// lisp lambda expression. The optional TR-BODY hook can be used for
/// translating other special forms that do lambda binding.
fn tr_lambda(form : Value, tr_body? : Value, tr_body_argl : Value) -> Value raise {
  let arglist = mparams(cadr(form))
  let mut easy_assigns : Value = Nil
  let b = bind(q_ear_local, Nil)
  defer unbind(b)
  for v in arglist.iter() {
    tbind(v) |> ignore
  }
  let r = match tr_body {
    None => tr_seq(cddr(form))
    Some(f) => apply(f, cons(cddr(form), tr_body_argl))
  }
  let mode = car(r)
  let nbody = cdr(r)
  let local_declares = make_declares(arglist, t)
  let body = if symval(q_ear_local).truthy() {
    list1(
      list4(
        q_let,
        list1(list2(q_mlocp, t)),
        list3(q_push, Nil, q_loclist),
        list3(q_unwind_protect, cons(q_progn, nbody), list1(q_munlocal)),
      ),
    )
  } else {
    nbody
  }
  // -> BINDING of variables with ASSIGN properties may be difficult to do
  // correctly and efficiently if arbitrary code is to be run.
  let easy = symval(q_tr_lambda_punt_assigns).truthy() ||
    {
      let mut ok = true
      for var_ in arglist.iter() {
        let assign = get(var_, q_assign)
        if assign.truthy() {
          if eq(assign, q_assign_mode_check) {
            easy_assigns = cons(
              list3(assign, transl__quote(var_), teval(var_)),
              easy_assigns,
            )
          } else {
            ok = false
            break
          }
        }
      }
      ok
    }
  if easy {
    // Case with EASY or no ASSIGN's
    let args = tunbinds(arglist)
    cons(
      mode,
      cons(q_lambda, cons(args, cons(local_declares, append(easy_assigns, body)))),
    )
  } else {
    // Case with arbitrary ASSIGN's.
    let temps = mapcar(_ => tr_gensym(), arglist)
    // [1] Check before binding.
    let checks = Collector::new()
    let mut vl = arglist
    let mut tl = temps
    while vl is Cons(_) && tl is Cons(_) {
      let var_ = car(vl)
      let val = car(tl)
      let assign = get(var_, q_assign)
      if assign.truthy() {
        checks.add(
          list4(q_funcall, transl__assign_fn(assign), transl__quote(var_), val),
        )
      }
      vl = cdr(vl)
      tl = cdr(tl)
    }
    // [2] do the binding.
    let binding = cons(
      cons(q_lambda, cons(tunbinds(arglist), cons(local_declares, body))),
      temps,
    )
    // [2] check when unbinding too.
    let unchecks = Collector::new()
    for var_ in arglist.iter() {
      let assign = get(var_, q_assign)
      if assign.truthy() {
        // use DTRANSLATE to catch global scoping if any.
        unchecks.add(
          list4(
            q_funcall,
            transl__assign_fn(assign),
            transl__quote(var_),
            dtranslate(var_),
          ),
        )
      }
    }
    cons(
      mode,
      list3(
        q_lambda,
        temps,
        cons(
          q_unwind_protect,
          cons(
            cons(q_progn, append(checks.result(), list1(binding))),
            unchecks.result(),
          ),
        ),
      ),
    )
  }
}

///|
/// MAKE-DECLARES
fn make_declares(varlist : Value, localp : Value) -> Value raise {
  let mut dl : Value = Nil
  let mut fx : Value = Nil
  let mut fl : Value = Nil
  let mut bl : Value = Nil
  let mut specs : Value = Nil
  for v in varlist.iter() {
    // When a variable is declared special, be sure to declare it special
    // here.
    if localp.truthy() && tr_get_special(v).truthy() {
      specs = cons(v, specs)
    }
    if localp is Nil || tr_get_special(v) is Nil {
      // don't output local declarations on special variables.
      let var_ = teval(v)
      let mode = value_mode(var_)
      specs = cons(var_, specs)
      if eq(q_d_fixnum, mode) {
        if memq(var_, fx) is Nil {
          fx = cons(var_, fx)
        }
      } else if eq(q_d_float, mode) {
        if memq(var_, fl) is Nil {
          fl = cons(var_, fl)
        }
      } else if eq(q_d_boolean, mode) {
        if memq(var_, bl) is Nil {
          bl = cons(var_, bl)
        }
      }
    }
  }
  if fx.truthy() {
    dl = cons(cons(q_fixnum, fx), dl)
  }
  if fl.truthy() {
    dl = cons(cons(q_type, cons(q_flonum, fl)), dl)
  }
  if bl.truthy() {
    dl = cons(cons(q_type, cons(q_boolean, bl)), dl)
  }
  if specs.truthy() {
    dl = cons(cons(q_special, specs), dl)
  }
  if dl.truthy() {
    cons(q_declare, dl)
  } else {
    Nil
  }
}

///|
/// TR-SEQ
fn tr_seq(l : Value) -> Value raise {
  let mut mode : Value = Nil
  let mut body : Value = Nil
  let mut l = l
  while l is Cons(_) {
    let exp_ = translate(car(l))
    l = cdr(l)
    mode = car(exp_)
    body = cons(cdr(exp_), body)
  }
  cons(mode, nreverse(body))
}

///|
/// DEF%TR MPROGN
fn transl__tr_mprogn(form : Value) -> Value raise {
  let form = tr_seq(cdr(form))
  cons(car(form), cons(q_progn, cdr(form)))
}

///|
/// GO-TAG-P
fn go_tag_p(e : Value) -> Value raise {
  lbool(symbolp(e) || integerp(e))
}

///|
/// DEF%TR MPROG
fn transl__tr_mprog(form : Value) -> Value raise {
  // [1] normalize the MPROG syntax.
  let (arglist, body) = if d_listp(cadr(form)).truthy() {
    (cdr(cadr(form)), cddr(form))
  } else {
    (Nil, cdr(form))
  }
  let body = if body is Nil {
    list1(list2(list1(q_mquote), q_d_done))
  } else {
    body
  }
  let val_list = mapcar(
    u => if atom(u) { u } else { translate(caddr(u)) },
    arglist,
  )
  let arglist = mapcar(
    u => {
      // X or ((MSETQ) X Y)
      if atom(u) {
        u
      } else {
        cadr(u)
      }
    },
    arglist,
  )
  let dup = find_duplicate(arglist, test_=q_eq)
  if dup.truthy() {
    tr_format(
      Str("error: ~M occurs more than once in block variable list"),
      list1(dup),
    )
    |> ignore
    tr_abort() |> ignore
    return Nil
  }
  let form = tr_lambda(
    // [2] call the lambda translator.
    cons(list1(q_lambda), cons(cons(list1(q_mlist), arglist), body)),
    // [3] supply our own body translator.
    tr_body=q_tr_mprog_body,
    list2(val_list, arglist),
  )
  cons(car(form), cons(cdr(form), val_list))
}

///|
/// TR-MPROG-BODY
fn tr_mprog_body(body : Value, val_list : Value, arglist : Value) -> Value raise {
  let bs = bind_all([
    (q_inside_mprog, t),
    (q_return_mode, Nil),
    (q_need_prog_q, Nil),
    (q_ear_go_forms, Nil),
    (q_ear_returns, Nil),
  ])
  defer unbind_all(bs)
  let mut l : Value = Nil
  let mut body = body
  while body is Cons(_) {
    // [4] translate a form in the body
    let mut form = car(body)
    body = cdr(body)
    if body is Nil {
      if go_tag_p(form).truthy() &&
        find_if(g => eql(cadr(g), form), symval(q_ear_go_forms)).truthy() {
        // we treat the last expression in the body as a go tag if (1) it
        // looks like a go tag, and (2) we have seen a go form with this
        // tag.
        l = cons(form, l)
        form = list2(q_return, transl__quote(q_d_done))
      } else {
        // this is a really bad case. we don't really know if the return
        // mode of the expression is for the value of the block.
        form = translate(form)
        set(q_return_mode, n_starunion_mode(car(form), symval(q_return_mode)))
        |> ignore
        form = cdr(form)
        if symval(q_need_prog_q).truthy() &&
          (atom(form) || memq(car(form), list2(q_go, q_return)) is Nil) {
          // put a RETURN on just in case.
          form = list2(q_return, form)
        }
      }
    } else if go_tag_p(form).truthy() {
      ()
    } else {
      form = dtranslate(form)
    }
    l = cons(form, l)
  }
  // [5] hack the val-list for the mode context.
  let mut vl = val_list
  let mut al = arglist
  while vl is Cons(_) && al is Cons(_) {
    if atom(car(vl)) {
      let init = cdr(assq(value_mode(car(al)), symval(q_mode_init_value_table)))
      rplaca(vl, if init.truthy() { init } else { transl__quote(car(al)) })
      |> ignore
    } else {
      warn_mode(
        car(al),
        value_mode(car(al)),
        car(car(vl)),
        comment=Str("in a `block' statement"),
      )
      |> ignore
      rplaca(vl, cdr(car(vl))) |> ignore
    }
    vl = cdr(vl)
    al = cdr(al)
  }
  let l = nreverse(l)
  cons(
    symval(q_return_mode),
    if symval(q_need_prog_q).truthy() {
      list1(cons(q_prog, cons(Nil, remove(Nil, l))))
    } else {
      l
    },
  )
}

///|
/// DEF%TR MRETURN
fn transl__tr_mreturn(form : Value) -> Value raise {
  if symval(q_inside_mprog) is Nil {
    tr_format(
      Str("error: 'return' not within 'block' or 'do': ~:M~%"),
      list1(form),
    )
    |> ignore
    tr_abort() |> ignore
    return Nil
  }
  set(q_need_prog_q, t) |> ignore
  let form = translate(cadr(form))
  set(q_return_mode, n_starunion_mode(car(form), symval(q_return_mode)))
  |> ignore
  let form = list2(q_return, cdr(form))
  // USED by lusing MDO etc not yet re-written.
  set(q_ear_returns, cons(form, symval(q_ear_returns))) |> ignore
  // MODE here should be $PHANTOM or something.
  cons(q_d_any, form)
}

///|
/// DEF%TR MGO
fn transl__tr_mgo(form : Value) -> Value raise {
  if symval(q_inside_mprog) is Nil {
    tr_format(Str("error: 'go' not within 'block' or 'do': ~:M~%"), list1(form))
    |> ignore
    tr_abort() |> ignore
    return Nil
  }
  if go_tag_p(cadr(form)) is Nil {
    tr_format(
      Str("error: 'go' tag must be a symbol or an integer: ~:M~%"),
      list1(form),
    )
    |> ignore
    tr_abort() |> ignore
    return Nil
  }
  set(q_need_prog_q, t) |> ignore
  let form = list2(q_go, cadr(form))
  set(q_ear_go_forms, cons(form, symval(q_ear_go_forms))) |> ignore
  cons(q_d_any, form)
}

///|
/// DEF%TR MQAPPLY
fn transl__tr_mqapply(form : Value) -> Value raise {
  let fn_ = cadr(form)
  let args = cddr(form)
  let aryp = memq(q_array, cdar(form))
  if atom(fn_) {
    // I'm guessing (ATOM FN) is a parser error or other Lisp error, so
    // don't bother to translate the following error message.
    tr_format(
      Str("translator: MQAPPLY operator must be a cons; found: ~:M~%"),
      list1(form),
    )
    |> ignore
    tr_abort() |> ignore
    Nil
  } else if eq(caar(fn_), q_mquote) {
    cons(
      q_d_any,
      cons(q_list, cons(transl__quote(cons(cadr(fn_), aryp)), tr_args(args))),
    )
  } else if eq(caar(fn_), q_lambda) {
    let args = tr_args(args)
    let fn_ = translate(fn_)
    cons(car(fn_), cons(q_mfuncall, cons(cdr(fn_), args)))
  } else if aryp is Nil {
    list3(
      q_d_any,
      q_simplify,
      list4(
        q_mapply,
        dconvx(translate(fn_)),
        cons(q_list, tr_args(args)),
        transl__quote(fn_),
      ),
    )
  } else {
    warn_meval(form) |> ignore
    punt_to_meval(form)
  }
}

///|
/// MCOND-EVAL-SYMBOLS-TR
fn mcond_eval_symbols_tr(form : Value) -> Value raise {
  mcond_eval_symbols(q_maybe_msymeval, form)
}

///|
/// DEF%TR MCOND
fn transl__tr_mcond(form : Value) -> Value raise {
  let g = tr_gensym()
  let mut nl : Value = Nil
  let mut mode : Value = Nil
  let mut l = cdr(form)
  while l is Cons(_) {
    // Optimize the else-if case: if we're at the else case at the end and
    // the body is just another conditional, then we just continue directly
    // with the clauses of the inner conditional instead of nesting.
    if cddr(l) is Nil &&
      eq(car(l), t) &&
      consp(cadr(l)) &&
      eq(car(car(car(cdr(l)))), q_mcond) {
      l = cdr(cadr(l))
    }
    let (pred_tr_r, body_tr_r) = with_special(q_wrap_a_pred, q_mcond, () => {
      let p = translate_predicate(car(l))
      let b = translate(cadr(l))
      (p, b)
    })
    let pred_mode = car(pred_tr_r)
    let pred_tr = cdr(pred_tr_r)
    let body_mode = car(body_tr_r)
    let body_tr = cdr(body_tr_r)
    mode = n_starunion_mode(mode, body_mode)
    if eq(pred_mode, q_d_boolean) {
      nl = cons(body_tr, cons(pred_tr, nl))
    } else {
      nl = list_star([
        list4(
          q_list_star,
          transl__quote(list1(q_mcond)),
          g,
          list3(
            q_mapcar,
            list2(q_function, q_mcond_eval_symbols_tr),
            transl__quote(cdr(l)),
          ),
        ),
        list2(q_not, list2(q_null, g)),
        body_tr,
        list3(q_eq, t, list3(q_setq, g, pred_tr)),
        nl,
      ])
    }
    l = cddr(l)
  }
  // We leave off the final clause if the condition is true and the
  // consequent is false.
  if eq(t, cadr(nl)) && car(nl) is Nil {
    nl = cddr(nl)
  }
  let mut form : Value = Nil
  let mut l = nl
  while l is Cons(_) {
    let clause_body = if !atom(car(l)) && cdr(l).truthy() && eq(caar(l), q_progn) {
      cdar(l)
    } else if equal(car(l), cadr(l)) && atom(car(l)) {
      Nil
    } else {
      list1(car(l))
    }
    form = cons(cons(cadr(l), clause_body), form)
    l = cddr(l)
  }
  if among(g, form).truthy() {
    cons(q_d_any, list3(q_let, list1(g), cons(q_cond, form)))
  } else {
    cons(mode, cons(q_cond, form))
  }
}

///|
/// The body forms of a DO translated from the translation ACTION of a loop
/// body.
fn transl__do_body(action : Value) -> Value {
  if atom(cdr(action)) {
    Nil
  } else if eq(q_progn, cadr(action)) {
    cddr(action)
  } else {
    list1(cdr(action))
  }
}

///|
/// DEF%TR MDO
fn transl__tr_mdo(form : Value) -> Value raise {
  let bs = bind_all([
    (q_ear_returns, Nil),
    (q_ear_go_forms, Nil),
    (q_assigns, Nil),
    (q_return_mode, Nil),
    (q_inside_mprog, t),
    (q_need_prog_q, Nil),
  ])
  defer unbind_all(bs)
  let mut var_ = if cadr(form).truthy() { cadr(form) } else { q_mdo }
  tbind(var_) |> ignore
  let init = if caddr(form).truthy() {
    translate(caddr(form))
  } else {
    cons(q_d_fixnum, Fix(1L))
  }
  let varmode = tr_get_mode(var_)
  if varmode is Nil {
    declvalue(var_, car(init), t) |> ignore
  }
  let next = translate(
    if cadddr(form).truthy() {
      list3(list1(q_mplus), cadddr(form), var_)
    } else if car(cddddr(form)).truthy() {
      car(cddddr(form))
    } else {
      list3(list1(q_mplus), Fix(1L), var_)
    },
  )
  let form = copy_list(form)
  // to make the end test for thru be numberp if the index is numberp and
  // to eliminate reevaluation
  if varmode is Nil {
    declvalue(var_, n_starunion_mode(car(init), car(next)), t) |> ignore
  } else {
    warn_mode(var_, varmode, n_starunion_mode(car(init), car(next))) |> ignore
  }
  let test_r = translate_predicate(
    list3(
      list1(q_mor),
      if cadr(cddddr(form)) is Nil {
        Nil
      } else if cadddr(form).truthy() &&
        mnegp(d_numfactor(simplify(cadddr(form)))).truthy() {
        list3(list1(q_mlessp), var_, cadr(cddddr(form)))
      } else {
        list3(list1(q_mgreaterp), var_, cadr(cddddr(form)))
      },
      caddr(cddddr(form)),
    ),
  )
  let test_mode = car(test_r)
  let test_pred = cdr(test_r)
  let test_form = if eq(test_mode, q_d_boolean) {
    test_pred
  } else {
    list3(q_let, list1(list2(q_d_prederror, t)), test_pred)
  }
  let action = translate(cadddr(cddddr(form)))
  let mode = if symval(q_ear_returns) is Nil {
    q_d_any
  } else {
    symval(q_return_mode)
  }
  var_ = tunbind(if cadr(form).truthy() { cadr(form) } else { q_mdo })
  list_star([
    mode,
    q_do,
    list1(list3(var_, cdr(init), cdr(next))),
    list2(test_form, transl__quote(q_d_done)),
    list2(q_declare, list2(q_special, var_)),
    transl__do_body(action),
  ])
}

///|
/// DEF%TR MDOIN
fn transl__tr_mdoin(form : Value) -> Value raise {
  let bs = bind_all([
    (q_ear_returns, Nil),
    (q_ear_go_forms, Nil),
    (q_assigns, Nil),
    (q_return_mode, Nil),
    (q_inside_mprog, t),
    (q_need_prog_q, Nil),
  ])
  defer unbind_all(bs)
  let var_ = tbind(cadr(form))
  tbind(q_mdo) |> ignore
  let init = dtranslate(caddr(form))
  if cadr(cddddr(form)).truthy() || caddr(cddddr(form)).truthy() {
    tunbind(q_mdo) |> ignore
    tunbind(cadr(form)) |> ignore
    return punt_to_meval(cons(list1(q_mdoin), cdr(form)))
  }
  let action = translate(cadddr(cddddr(form)))
  let mode = if symval(q_ear_returns) is Nil {
    q_d_any
  } else {
    symval(q_return_mode)
  }
  tunbind(q_mdo) |> ignore
  tunbind(cadr(form)) |> ignore
  // MDOIN-ELEMENTS can give unsimplified values, such as ((MMINUS) 1) for
  // x-1, which the interpreter simplifies when it reads the variable.
  list_star([
    mode,
    q_do,
    list2(
      list1(var_),
      list3(q_mdo, list2(q_mdoin_elements, init), list2(q_cdr, q_mdo)),
    ),
    list2(list2(q_null, q_mdo), transl__quote(q_d_done)),
    list2(q_declare, list2(q_special, var_)),
    list3(q_setq, var_, list2(q_simplify, list2(q_car, q_mdo))),
    transl__do_body(action),
  ])
}

///|
/// LAMBDA-WRAP1
fn lambda_wrap1(tn : Value, val : Value, form : Value) -> Value raise {
  if atom(val) || eq(car(val), q_quote) {
    subst(val, tn, form)
  } else {
    list2(list3(q_lambda, list1(tn), form), val)
  }
}

///|
/// DEF%TR MSETQ
fn transl__tr_msetq(form : Value) -> Value raise {
  let var_ = cadr(form)
  let mut val = caddr(form)
  if atom(var_) {
    let mut mode = value_mode(var_)
    val = translate(val)
    warn_mode(var_, mode, car(val)) |> ignore
    if eq(q_d_any, mode) {
      mode = car(val)
      val = cdr(val)
    } else {
      val = dconv(val, mode)
    }
    let assign = get(var_, q_assign)
    cons(
      mode,
      if assign.truthy() {
        let tn = tr_gensym()
        let assign_fn = transl__assign_fn(assign)
        lambda_wrap1(
          tn,
          val,
          list([
            q_let,
            Nil,
            list2(q_declare, list3(q_special, var_, teval(var_))),
            list4(q_funcall, assign_fn, transl__quote(var_), tn),
            list3(q_setq, teval(var_), tn),
          ]),
        )
      } else {
        list([
          q_let,
          Nil,
          list2(q_declare, list2(q_special, teval(var_))),
          list3(
            q_if,
            list2(q_not, list2(q_boundp, transl__quote(teval(var_)))),
            list3(q_add2lnc, transl__quote(teval(var_)), q_d_values),
          ),
          list3(
            if symval(q_ear_macexpr_top_level_form_p).truthy() {
              q_defparameter
            } else {
              q_setq
            },
            teval(var_),
            val,
          ),
        ])
      },
    )
  } else if memq(q_array, car(var_)).truthy() {
    tr_arraysetq(var_, val)
  } else {
    if safe_get(caar(var_), q_mset_extension_operator) is Nil {
      tr_format(Str("warning: no assignment operator known for ~:M~%"), list1(var_))
      |> ignore
      tr_format(Str("note: just keep going and hope for the best.~%"), Nil)
      |> ignore
    }
    val = translate(val)
    list4(car(val), q_mset, transl__quote(var_), cdr(val))
  }
}

///|
/// TRANSLATE-$MAX-$MIN
fn translate__dolmax__dolmin(form : Value) -> Value raise {
  let mut mode : Value = Nil
  let op = stripdollar(caar(form))
  let arglist = mapcar(
    l => {
      let l = translate(l)
      if mode is Nil {
        mode = car(l)
      } else if eq(mode, car(l)) {
        ()
      } else {
        mode = q_d_any
      }
      l
    },
    cdr(form),
  )
  // To match the interpreted case, and to make sure we use the correct
  // mode for the return value, we do not apply float contagion to the
  // arguments and we use a special translation to call MAX or MIN only
  // when every argument has the same mode (either all fixnum or all
  // float).
  if memq(mode, list2(q_d_fixnum, q_d_float)).truthy() {
    cons(
      mode,
      cons(if eq(q_min, op) { q_min } else { q_max }, mapcar(x => cdr(x), arglist)),
    )
  } else {
    list3(
      q_d_any,
      if eq(q_min, op) {
        q_d_lmin
      } else {
        q_d_lmax
      },
      cons(
        q_list,
        cons(transl__quote(list1(q_mlist)), mapcar(x => dconvx(x), arglist)),
      ),
    )
  }
}

// ---------------------------------------------------------------------------
// mode accessing, binding, handling. Super over-simplified.

///|
/// TR-CLASS
fn tr_class(x : Value) -> Value raise {
  if integerp(x) {
    q_d_fixnum
  } else if floatp(x) {
    q_d_float
  } else if x is Nil || eq(x, t) {
    q_d_boolean
  } else if atom(x) {
    q_d_any
  } else if eq(q_rat, caar(x)) {
    q_d_rational
  } else {
    q_d_any
  }
}

///|
/// *UNION-MODE
fn n_starunion_mode(mode1 : Value, mode2 : Value) -> Value raise {
  if eq(mode1, mode2) {
    mode1
  } else if mode1 is Nil {
    mode2
  } else if mode2 is Nil {
    mode1
  } else if eq(q_d_boolean, mode1) || eq(q_d_boolean, mode2) {
    q_d_any
  } else if memq(mode2, symval(q_ear__dolany_modes)).truthy() ||
    memq(mode1, symval(q_ear__dolany_modes)).truthy() {
    q_d_any
  } else if eq(q_d_fixnum, mode1) {
    mode2
  } else if eq(q_d_float, mode1) {
    if eq(q_d_number, mode2) {
      q_d_number
    } else {
      q_d_float
    }
  } else if eq(q_d_rational, mode1) {
    if eq(q_d_float, mode2) {
      q_d_float
    } else {
      q_d_any
    }
  } else if eq(q_d_number, mode1) {
    if eq(q_d_rational, mode2) {
      q_d_any
    } else {
      q_d_number
    }
  } else {
    q_d_any
  }
}

///|
/// VALUE-MODE
fn value_mode(var_ : Value) -> Value raise {
  let m = tr_get_mode(var_)
  if m.truthy() {
    m
  } else {
    warn_undeclared(var_) |> ignore
    q_d_any
  }
}

///|
/// DECMODE-ARRAYFUN
fn decmode_arrayfun(f : Value, m : Value) -> Value raise {
  putprop(f, m, q_arrayfun_mode)
}

///|
/// ARRAY-MODE
fn array_mode(ar : Value) -> Value raise {
  let m = get(ar, q_array_mode)
  if m.truthy() {
    m
  } else {
    q_d_any
  }
}

///|
/// ARRAYFUN-MODE
fn arrayfun_mode(ar : Value) -> Value raise {
  let m = get(ar, q_arrayfun_mode)
  if m.truthy() {
    m
  } else {
    q_d_any
  }
}

///|
/// FUNCTION-MODE
fn function_mode(f : Value) -> Value raise {
  let m = get(f, q_function_mode)
  if m.truthy() {
    m
  } else {
    q_d_any
  }
}

///|
/// FUNCTION-MODE-@
fn function_mode__at(f : Value) -> Value raise {
  ass_eq_ref(tr_get_val_modes(f), q_function_mode, dflt=q_d_any)
}

///|
/// ARRAY-MODE-@
fn array_mode__at(f : Value) -> Value raise {
  ass_eq_ref(tr_get_val_modes(f), q_array_mode, dflt=q_d_any)
}

// TBIND, below, copies the MODE, VAL-MODES, and SPECIAL properties into
// the a table named TSTACK, and then removes those properties. So if TBIND
// has been called, we will need to look for those properties in TSTACK
// instead of the symbol property list.
//
// (defstruct tstack-slot mode tbind val-modes special): slots 0..3.

///|
fn transl__make_tstack_slot(
  mode : Value,
  tbind : Value,
  val_modes : Value,
  special : Value,
) -> Value {
  make_struct("tstack-slot", [mode, tbind, val_modes, special])
}

///|
/// The TSTACK-SLOT of A (which has the TBIND property).
fn transl__my_slot(a : Value) -> Value {
  cdr(assoc(a, symval(q_tstack)))
}

///|
/// TR-GET-MODE
fn tr_get_mode(a : Value) -> Value raise {
  if get(a, q_tbind).truthy() {
    struct_ref(transl__my_slot(a), 0)
  } else {
    get(a, q_mode)
  }
}

///|
/// (SETF TR-GET-MODE)
fn setf_tr_get_mode(b : Value, a : Value) -> Value raise {
  if get(a, q_tbind).truthy() {
    struct_set(transl__my_slot(a), 0, b)
  } else {
    putprop(a, b, q_mode)
  }
}

///|
/// TR-GET-VAL-MODES
fn tr_get_val_modes(a : Value) -> Value raise {
  if get(a, q_tbind).truthy() {
    struct_ref(transl__my_slot(a), 2)
  } else {
    get(a, q_val_modes)
  }
}

///|
/// (SETF TR-GET-VAL-MODES)
fn setf_tr_get_val_modes(b : Value, a : Value) -> Value raise {
  if get(a, q_tbind).truthy() {
    struct_set(transl__my_slot(a), 2, b)
  } else {
    putprop(a, b, q_val_modes)
  }
}

///|
/// TR-GET-SPECIAL
fn tr_get_special(a : Value) -> Value raise {
  if get(a, q_tbind).truthy() {
    struct_ref(transl__my_slot(a), 3)
  } else {
    get(a, q_special)
  }
}

///|
/// (SETF TR-GET-SPECIAL)
fn setf_tr_get_special(b : Value, a : Value) -> Value raise {
  if get(a, q_tbind).truthy() {
    struct_set(transl__my_slot(a), 3, b)
  } else {
    putprop(a, b, q_special)
  }
}

///|
/// VARIABLE-P
fn variable_p(var_ : Value) -> Value raise {
  lbool(var_.truthy() && symbolp(var_) && !eq(var_, t))
}

///|
/// BAD-VAR-WARN
fn bad_var_warn(var_ : Value) -> Value raise {
  tr_format(Str("warning: ~:M cannot be used as a variable.~%"), list1(var_))
}

///|
/// TBIND
fn tbind(var_ : Value) -> Value raise {
  if variable_p(var_).truthy() {
    let old = transl__make_tstack_slot(
      get(var_, q_mode),
      get(var_, q_tbind),
      get(var_, q_val_modes),
      get(var_, q_special),
    )
    set(q_tstack, cons(cons(var_, old), symval(q_tstack))) |> ignore
    if specialp(var_) is Nil {
      // It is the lisp convention in use to inherit specialness from
      // higher context.
      remprop(var_, q_val_modes) |> ignore
      remprop(var_, q_mode) |> ignore
      remprop(var_, q_special) |> ignore
    }
    putprop(var_, var_, q_tbind) |> ignore
    let hook = symval(q_d_tr_bind_mode_hook)
    if hook.truthy() {
      let mode_q = mapply(hook, list1(var_), q_d_tr_bind_mode_hook)
      if mode_q.truthy() {
        tr_declare_varmode(var_, mode_q) |> ignore
      }
    }
    var_
  } else {
    bad_var_warn(var_)
  }
}

///|
/// TUNBIND
fn tunbind(var_ : Value) -> Value raise {
  let old = assq(var_, symval(q_tstack))
  if variable_p(var_).truthy() {
    let r = teval(var_)
    if old.truthy() {
      // POP should be all we need.
      set(q_tstack, remove(old, symval(q_tstack))) |> ignore
      let slot = cdr(old)
      putprop1(var_, struct_ref(slot, 0), q_mode) |> ignore
      putprop1(var_, struct_ref(slot, 1), q_tbind) |> ignore
      putprop1(var_, struct_ref(slot, 2), q_val_modes) |> ignore
      putprop1(var_, struct_ref(slot, 3), q_special) |> ignore
    }
    r
  } else {
    Nil
  }
}

///|
/// PUTPROP1: leaves property list clean after unwinding.
fn putprop1(name : Value, value : Value, key : Value) -> Value raise {
  if value.truthy() {
    putprop(name, value, key)
  } else {
    remprop(name, key) |> ignore
    Nil
  }
}

///|
/// TUNBINDS
fn tunbinds(l : Value) -> Value raise {
  let mut nl : Value = Nil
  let mut l = l
  while l is Cons(_) {
    nl = cons(tunbind(caar(symval(q_tstack))), nl)
    l = cdr(l)
  }
  nl
}

///|
/// TBOUNDP: really LEXICAL-VARP.
fn tboundp(var_ : Value) -> Value raise {
  if symbolp(var_) && get(var_, q_tbind).truthy() {
    lbool(tr_get_special(var_) is Nil)
  } else {
    Nil
  }
}

///|
/// TEVAL
fn teval(var_ : Value) -> Value raise {
  if symbolp(var_) {
    let b = get(var_, q_tbind)
    if b.truthy() {
      return b
    }
  }
  var_
}

///|
fn init_transl() -> Unit raise {
  // complex initial value
  defvar_init(q_tr_unique, gensym())
  // DEFMVAR options and initial values (for `reset`)
  let tr_settings = list([q_d_all, q_d_compile, q_d_compfile, q_d_translate])
  for v in [
    q_ear_declared_translated_functions, q_tstack, q_ear_local, q_tr_progret, q_inside_mprog,
    q_ear_go_forms, q_ear_returns, q_return_mode, q_need_prog_q, q_assigns, q_translate_time_evalables,
    q_ear_transl_backtrace, q_ear_transl_debug, q_tr_abort, q_tr_unique, q_ear_warned_un_declared_vars,
    q_ear_warned_fexprs, q_ear_warned_mode_vars, q_d_tr_function_call_default, q_d_tr_array_as_ref,
    q_d_tr_numer, q_ear__dolany_modes, q_ear_tr_warn_break, q_d_tr_optimize_max_loop, q_d_tr_bound_function_applyp,
  ] {
    defmvar(v, val=symval(v), Nil) |> ignore
  }
  for v in [
    q_d_tr_warn_undeclared, q_d_tr_warn_meval, q_d_tr_warn_fexpr, q_d_tr_warn_mode, q_d_tr_warn_undefined_variable,
  ] {
    defmvar(v, val=symval(v), list([kw("setting-list"), tr_settings])) |> ignore
  }
  transl__deftr(q_d_eval_when, transl__tr_eval_when)
  transl__deftr(q_mdefmacro, transl__tr_mdefmacro)
  transl__deftr(q_d_local, transl__tr_local)
  transl__deftr(q_mquote, transl__tr_mquote)
  transl__deftr(q_mprogn, transl__tr_mprogn)
  transl__deftr(q_mprog, transl__tr_mprog)
  transl__deftr(q_mreturn, transl__tr_mreturn)
  transl__deftr(q_mgo, transl__tr_mgo)
  transl__deftr(q_mqapply, transl__tr_mqapply)
  transl__deftr(q_mcond, transl__tr_mcond)
  transl__deftr(q_mdo, transl__tr_mdo)
  transl__deftr(q_mdoin, transl__tr_mdoin)
  transl__deftr(q_msetq, transl__tr_msetq)
  transl__deftr(q_d_max, translate__dolmax__dolmin)
  transl__deftr(q_d_min, translate__dolmax__dolmin)
  transl__deftr(q_p_max, translate__dolmax__dolmin)
  transl__deftr(q_p_min, translate__dolmax__dolmin)
}
