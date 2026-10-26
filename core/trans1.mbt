// Port of src/trans1.lisp: System FSUBR translation properties that were
// not handled in TRANSL (mostly from JPG MLISP).

///|
/// QUOTED-SYMBOLP
fn quoted_symbolp(form : Value) -> Value raise {
  lbool(consp(form) && eq(q_quote, car(form)) && symbolp(cadr(form)))
}

///|
/// DEF%TR $APPLY: APPLY(F,[X]) is an idiom for funcall.
fn trans1__tr_apply(form : Value) -> Value raise {
  let fun = dtranslate(cadr(form))
  let mode = if symbolp(fun) {
    function_mode__at(fun)
  } else if quoted_symbolp(fun).truthy() {
    function_mode(cadr(fun))
  } else {
    q_d_any
  }
  if d_listp(caddr(form)).truthy() {
    let args = tr_args(cdr(caddr(form)))
    call_and_simp(mode, q_mfuncall, cons(fun, args))
  } else {
    let arg = dtranslate(caddr(form))
    call_and_simp(mode, q_mapply_tr, list2(fun, arg))
  }
}

///|
/// `(getopr ,fun)`
fn trans1__getopr(fun : Value) -> Value {
  list2(q_getopr, fun)
}

///|
/// DEF%TR $MAP
fn trans1__tr_map(form : Value) -> Value raise {
  let l = tr_args(cdr(form))
  call_and_simp(q_d_any, q_map1, cons(trans1__getopr(car(l)), cdr(l)))
}

///|
/// DEF%TR $MAPLIST
fn trans1__tr_maplist(form : Value) -> Value raise {
  let l = tr_args(cdr(form))
  cons(q_d_any, cons(q_maplist_tr, cons(car(l), cdr(l))))
}

///|
/// DEF%TR $FULLMAP
fn trans1__tr_fullmap(form : Value) -> Value raise {
  let l = tr_args(cdr(form))
  call_and_simp(
    q_d_any,
    q_fmap1,
    list3(trans1__getopr(car(l)), cons(q_list, cdr(l)), Nil),
  )
}

///|
/// DEF%TR $MATRIXMAP
fn trans1__tr_matrixmap(form : Value) -> Value raise {
  let l = tr_args(cdr(form))
  call_and_simp(
    q_d_any,
    list3(
      q_lambda,
      list1(q_fmaplvl),
      cons(q_fmapl1, cons(trans1__getopr(car(l)), cdr(l))),
    ),
    list1(Fix(2L)),
  )
}

///|
/// DEF%TR $FULLMAPL
fn trans1__tr_fullmapl(form : Value) -> Value raise {
  let l = tr_args(cdr(form))
  call_and_simp(q_d_any, q_fmapl1, cons(trans1__getopr(car(l)), cdr(l)))
}

///|
/// DEF%TR $OUTERMAP
fn trans1__tr_outermap(form : Value) -> Value raise {
  let l = tr_args(cdr(form))
  let args = cdr(l)
  call_and_simp(
    q_d_any,
    if length(args) == 1 {
      q_fmapl1
    } else {
      q_outermap1
    },
    cons(trans1__getopr(car(l)), args),
  )
}

///|
/// DEF%TR $SCANMAP
fn trans1__tr_scanmap(form : Value) -> Value raise {
  let l = tr_args(cdr(form))
  call_and_simp(q_d_any, q_scanmap1, cons(trans1__getopr(car(l)), cdr(l)))
}

///|
/// DEF%TR $QPUT
fn trans1__tr_qput(form : Value) -> Value raise {
  list([
    q_d_any,
    q_d_put,
    transl__quote(cadr(form)),
    transl__quote(caddr(form)),
    transl__quote(cadddr(form)),
  ])
}

///|
/// DEF%TR $SUBVAR
fn trans1__tr_subvar(form : Value) -> Value raise {
  translate(cons(list2(q_mqapply, q_array), cdr(form)))
}

///|
/// DEF%TR $SUBSTPART
fn trans1__tr_substpart(form : Value) -> Value raise {
  substpart_translation(form, t, Nil, q_d_inflag, q_d_substpart)
}

///|
/// DEF%TR $SUBSTINPART
fn trans1__tr_substinpart(form : Value) -> Value raise {
  substpart_translation(form, t, Nil, t, q_d_substinpart)
}

///|
/// FOR-EVAL-THEN-MQUOTE-SIMP-ARGL
fn for_eval_then_mquote_simp_argl(l : Value) -> Value raise {
  mapcar(
    x => list3(q_list, transl__quote(list2(q_mquote, q_simp)), x),
    l,
  )
}

///|
/// SUBSTPART-TRANSLATION: if the evaluation of the first argument does not
/// depend on the setting of the special variable PIECE, then it need not
/// be evaluated inside of PART1.
fn substpart_translation(
  form : Value,
  flag1 : Value,
  flag2 : Value,
  flag3 : Value,
  fn_ : Value,
) -> Value raise {
  let subst_item = dtranslate(cadr(form))
  let freevars = free_lisp_vars(subst_item)
  let argl = tr_args(cddr(form))
  if assq(q_d_piece, freevars) is Nil {
    cons(
      q_d_any,
      list2(
        q_simplify,
        list([
          q_part1,
          cons(q_list, for_eval_then_mquote_simp_argl(cons(subst_item, argl))),
          flag1,
          flag2,
          flag3,
          transl__quote(fn_),
        ]),
      ),
    )
  } else {
    let freevars = tbound_free_vars(freevars)
    side_effect_free_check(cadr(freevars), cadr(form)) |> ignore
    cons(
      q_d_any,
      list2(
        q_simplify,
        list([
          q_part1,
          cons(
            q_list,
            cons(
              list4(
                q_fungen_ampenv_for_meval,
                remove(q_d_piece, car(freevars)),
                list1(q_d_piece),
                subst_item,
              ),
              for_eval_then_mquote_simp_argl(argl),
            ),
          ),
          flag1,
          flag2,
          flag3,
          transl__quote(fn_),
        ]),
      ),
    )
  }
}

///|
/// DEF%TR $ERRCATCH
fn trans1__tr_errcatch(form : Value) -> Value raise {
  let body = cdr(translate(cons(list1(q_mprogn), cdr(form))))
  cons(
    q_d_any,
    list3(q_cons, transl__quote(list1(q_mlist)), list2(q_errcatch, body)),
  )
}

///|
/// DEF%TR $CATCH
fn trans1__tr_catch(form : Value) -> Value raise {
  let body = cdr(translate(cons(list1(q_mprogn), cdr(form))))
  cons(q_d_any, list2(q_mcatch, body))
}

///|
/// DEF%TR $THROW
fn trans1__tr_throw(form : Value) -> Value raise {
  let r = translate(cadr(form))
  cons(car(r), list2(q_d_throw, cdr(r)))
}

///|
/// `(merror (intl:gettext msg) ,nn)`
fn trans1__merror_form(msg : String, nn : Value) -> Value {
  list3(q_merror, list2(transl__q_intl_gettext, Str(msg)), nn)
}

///|
/// `(cons '(mlist) (nreverse ,sum))`
fn trans1__mlist_nreverse(sum : Value) -> Value {
  list3(q_cons, transl__quote(list1(q_mlist)), list2(q_nreverse, sum))
}

///|
/// DEF%TR $MAKELIST: MAKELIST(EXP,X,0,N) with 4 args it is an iteration,
/// with three it is a mapping over a list (the third argument).
fn trans1__tr_makelist(form : Value) -> Value raise {
  let form = cdr(form)
  let n_args = length(form)
  if n_args == 0 {
    cons(
      q_d_any,
      list3(q_simplifya, transl__quote(list1(list1(q_mlist))), t),
    )
  } else if n_args == 1 {
    let exp_ = car(form)
    cons(
      q_d_any,
      list3(
        q_simplifya,
        list3(
          q_list,
          transl__quote(list1(q_mlist)),
          cdr(tr_local_exp(exp_, Nil)),
        ),
        t,
      ),
    )
  } else if n_args == 2 {
    let exp_ = car(form)
    let mut n = cadr(form)
    let sum = tr_gensym()
    let nn = tr_gensym()
    let i0 = tr_gensym()
    n = dtranslate(n)
    cons(
      q_d_any,
      list3(
        q_simplifya,
        list2(
          list4(
            q_lambda,
            list1(nn),
            list3(q_setq, nn, list2(q_d_float, nn)),
            list4(
              q_if,
              list2(q_numberp, nn),
              list4(
                q_do,
                list2(
                  list3(i0, Fix(1L), list3(q_add, Fix(1L), i0)),
                  list2(sum, Nil),
                ),
                list2(
                  list3(q_op_gt, i0, nn),
                  list3(q_cons, transl__quote(list1(q_mlist)), sum),
                ),
                list3(
                  q_setq,
                  sum,
                  list3(q_cons, cdr(tr_local_exp(exp_, Nil)), sum),
                ),
              ),
              trans1__merror_form(
                "makelist: second argument must evaluate to a number; found: ~M",
                nn,
              ),
            ),
          ),
          n,
        ),
        t,
      ),
    )
  } else if n_args == 3 {
    let exp_ = car(form)
    let x = cadr(form)
    let mut n = caddr(form)
    let sum = tr_gensym()
    let nn = tr_gensym()
    let lil = tr_gensym()
    n = dtranslate(n)
    let do1 = list4(
      q_do,
      list3(
        list3(lil, list2(q_cdr, nn), list2(q_cdr, lil)),
        list2(sum, Nil),
        list1(x),
      ),
      list2(list2(q_null, lil), trans1__mlist_nreverse(sum)),
      list([
        q_setq,
        x,
        list2(q_car, lil),
        sum,
        list3(q_cons, cdr(tr_local_exp(exp_, list2(x, value_mode(x)))), sum),
      ]),
    )
    let do2 = list4(
      q_do,
      list2(
        list3(x, Fix(1L), list3(q_add, Fix(1L), x)),
        list3(
          sum,
          Nil,
          list3(q_cons, cdr(tr_local_exp(exp_, list2(x, value_mode(x)))), sum),
        ),
      ),
      list2(list3(q_op_gt, x, nn), trans1__mlist_nreverse(sum)),
      list2(q_declare, list2(q_special, x)),
    )
    cons(
      q_d_any,
      list3(
        q_simplifya,
        list2(
          list3(
            q_lambda,
            list1(nn),
            list4(
              q_if,
              list2(q_d_listp, nn),
              do1,
              list3(
                q_progn,
                list3(q_setq, nn, list2(q_d_float, nn)),
                list4(
                  q_if,
                  list2(q_numberp, nn),
                  do2,
                  trans1__merror_form(
                    "makelist: third argument must be a number or a list; found: ~M",
                    nn,
                  ),
                ),
              ),
            ),
          ),
          n,
        ),
        t,
      ),
    )
  } else if n_args == 4 {
    let exp_ = car(form)
    let x = cadr(form)
    let mut i0 = caddr(form)
    let mut n = cadddr(form)
    let i00 = tr_gensym()
    let nn = tr_gensym()
    let sum = tr_gensym()
    let ii = tr_gensym()
    i0 = dtranslate(i0)
    n = dtranslate(n)
    let do_ = list4(
      q_do,
      list3(
        list3(x, i00, list3(q_add, Fix(1L), x)),
        list3(ii, Fix(0L), list3(q_add, Fix(1L), ii)),
        list3(
          sum,
          Nil,
          list3(q_cons, cdr(tr_local_exp(exp_, list2(x, value_mode(x)))), sum),
        ),
      ),
      list2(list3(q_op_gt, ii, nn), trans1__mlist_nreverse(sum)),
      list2(q_declare, list2(q_special, x)),
    )
    cons(
      q_d_any,
      list3(
        q_simplifya,
        list3(
          list4(
            q_lambda,
            list2(i00, nn),
            list3(q_setq, nn, list2(q_d_float, list3(q_sub, nn, i00))),
            list4(
              q_if,
              list2(q_numberp, nn),
              do_,
              trans1__merror_form(
                "makelist: the fourth argument minus the third one must evaluate to a number; found: ~M",
                nn,
              ),
            ),
          ),
          i0,
          n,
        ),
        t,
      ),
    )
  } else if n_args == 5 {
    let exp_ = car(form)
    let x = cadr(form)
    let mut i0 = caddr(form)
    let mut n = cadddr(form)
    let mut s = car(cddddr(form))
    let i00 = tr_gensym()
    let nn = tr_gensym()
    let ss = tr_gensym()
    let sum = tr_gensym()
    let ii = tr_gensym()
    i0 = dtranslate(i0)
    n = dtranslate(n)
    s = dtranslate(s)
    let do_ = list4(
      q_do,
      list3(
        list3(x, i00, list3(q_add, ss, x)),
        list3(ii, Fix(0L), list3(q_add, Fix(1L), ii)),
        list3(
          sum,
          Nil,
          list3(q_cons, cdr(tr_local_exp(exp_, list2(x, value_mode(x)))), sum),
        ),
      ),
      list2(list3(q_op_gt, ii, nn), trans1__mlist_nreverse(sum)),
      list2(q_declare, list2(q_special, x)),
    )
    cons(
      q_d_any,
      list3(
        q_simplifya,
        list4(
          list4(
            q_lambda,
            list3(i00, nn, ss),
            list3(
              q_setq,
              nn,
              list2(q_d_float, list3(q_div, list3(q_sub, nn, i00), ss)),
            ),
            list4(
              q_if,
              list2(q_numberp, nn),
              do_,
              trans1__merror_form(
                "makelist: the fourth argument minus the third one, divided by the fifth one must evaluate to a number; found: ~M",
                nn,
              ),
            ),
          ),
          i0,
          n,
          s,
        ),
        t,
      ),
    )
  } else {
    tr_format(
      Str(
        "makelist: maximum 5 arguments allowed; found: ~M.~%makelist: to create a list with sublists, use nested makelist commands.~%",
      ),
      list1(int(n_args)),
    )
    |> ignore
    tr_abort() |> ignore
    cons(q_d_any, transl__quote(q_d_ear__starerror_star))
  }
}

///|
/// DEF%TR $KILL
fn trans1__tr_kill(form : Value) -> Value raise {
  cons(
    q_d_any,
    list4(q_mapply, transl__quote(q_d_kill), transl__quote(cdr(form)), Nil),
  )
}

///|
/// DEF%TR $ARRAY: if the type is one of the known types then the dims are
/// evaluated. But, if type is not one of those, it "must" be a dim spec!
fn trans1__tr_array(form : Value) -> Value raise {
  let form = cdr(form)
  let name = car(form)
  let specp = assq(
    cadr(form),
    list([
      cons(q_d_complete, t),
      cons(q_d_integer, q_fixnum),
      cons(q_d_fixnum, q_fixnum),
      cons(q_d_float, q_flonum),
      cons(q_d_flonum, q_flonum),
    ]),
  )
  let args = if specp.truthy() {
    cons(
      q_list,
      cons(
        transl__quote(name),
        cons(transl__quote(cadr(form)), tr_args(cddr(form))),
      ),
    )
  } else {
    cons(q_list, cons(transl__quote(name), tr_args(cdr(form))))
  }
  cons(
    q_d_any,
    list4(q_mapply, transl__quote(q_d_array), args, transl__quote(q_d_array)),
  )
}

///|
/// DEF%TR MRAT
fn trans1__tr_mrat(form : Value) -> Value raise {
  let t_form = translate(d_ratdisrep(form))
  if memq(car(t_form), list([q_d_float, q_d_fixnum, q_d_number])).truthy() {
    t_form
  } else {
    cons(q_d_any, list2(q_ratf, cdr(t_form)))
  }
}

///|
/// DEF%TR $ALIAS: the following special forms do not call the evaluator.
fn trans1__tr_alias(form : Value) -> Value raise {
  punt_to_meval(form)
}

///|
fn init_trans1() -> Unit raise {
  transl__deftr(q_d_apply, trans1__tr_apply)
  transl__deftr(q_d_map, trans1__tr_map)
  transl__deftr(q_d_maplist, trans1__tr_maplist)
  transl__deftr(q_d_fullmap, trans1__tr_fullmap)
  transl__deftr(q_d_matrixmap, trans1__tr_matrixmap)
  transl__deftr(q_d_fullmapl, trans1__tr_fullmapl)
  transl__deftr(q_d_outermap, trans1__tr_outermap)
  transl__deftr(q_d_scanmap, trans1__tr_scanmap)
  transl__deftr(q_d_qput, trans1__tr_qput)
  transl__deftr(q_d_subvar, trans1__tr_subvar)
  transl__deftr(q_d_substpart, trans1__tr_substpart)
  transl__deftr(q_d_substinpart, trans1__tr_substinpart)
  transl__deftr(q_d_errcatch, trans1__tr_errcatch)
  transl__deftr(q_d_catch, trans1__tr_catch)
  transl__deftr(q_d_throw, trans1__tr_throw)
  transl__deftr(q_d_makelist, trans1__tr_makelist)
  transl__deftr(q_d_kill, trans1__tr_kill)
  transl__deftr(q_d_array, trans1__tr_array)
  transl__deftr(q_mrat, trans1__tr_mrat)
  transl__deftr(q_d_alias, trans1__tr_alias)
  // most of these will lose in common since a local variable will not have
  // its value accessible to the mfexpr*.
  for name in [
    "$batch", "$batchload", "$closefile", "$compfile", "$declare", "$defstruct", "$demo",
    "$dependencies", "$describe", "$dispfun", "$disprule", "$fundef", "$gradef", "$labels",
    "$loadarrays", "$loadfile", "$new", "$numerval", "$options", "$ordergreat", "$orderless",
    "$printfile", "$printprops", "$product", "%product", "$properties", "$propvars", "$rearray",
    "$remarray", "$remfunction", "$remove", "$remvalue", "$setup_autoload", "$sum", "%sum",
    "$translate", "$writefile",
  ] {
    transm__def_same_tr(sym(name), q_d_alias)
  }
}
