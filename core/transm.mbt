// Port of src/transm.lisp: macros for TRANSL source compilation.
//
// DEF%TR (defining a TRANSLATE property) is expanded by hand in each
// translator file: the property is a function installed by that file's
// init.  The macros that appear in *translated code* (MASET, MAREF) and the
// code-producing macros (DEF-SAME%TR, BIND-TRANSL-STATE, TR) are declared
// functions here; they are implemented as macro EXPANDERS: they take the
// unevaluated argument forms and return the expansion, which the Lisp
// evaluator (`lisp_eval_form`) evaluates.

///|
/// The state variables bound by BIND-TRANSL-STATE, with their binding
/// values (all NIL except $TR_NUMER, bound to itself).
fn transm__transl_state_bindings() -> Array[(Value, Value)] {
  [
    (q_ear_warned_un_declared_vars, Nil),
    (q_ear_warned_fexprs, Nil),
    (q_ear_warned_mode_vars, Nil),
    (q_warned_undefined_variables, Nil),
    (q_tr_abort, Nil),
    (q_transl_file, Nil),
    (q_ear_in_compfile, Nil),
    (q_ear_in_translate_file, Nil),
    (q_ear_in_translate, Nil),
    (q_ear_pre_transl_forms, Nil),
    (q_d_tr_numer, symval(q_d_tr_numer)),
    (q_defined_variables, Nil),
    (q_ear_local, Nil),
  ]
}

///|
/// `(bind-transl-state . body)` for the port's own callers: binds all
/// transl state variables to NIL (and $TR_NUMER to itself) around `body`.
fn[T] transm__with_transl_state(body : () -> T raise) -> T raise {
  let bs = bind_all(transm__transl_state_bindings())
  defer unbind_all(bs)
  body()
}

///|
/// DEF-SAME%TR expander: `(def-same%tr name same-as)`.
fn def_same_pcttr(name : Value, same_as : Value) -> Value raise {
  list([
    q_putprop,
    list2(q_quote, name),
    list([
      q_or,
      list([q_get, list2(q_quote, same_as), list2(q_quote, q_translate)]),
      list([
        q_maxima_error,
        Str(
          "DEF-SAME%TR: ~a has no TRANSLATE property, so I can't make an alias.",
        ),
        list2(q_quote, same_as),
      ]),
    ]),
    list2(q_quote, q_translate),
  ])
}

///|
/// DEF-SAME%TR at load time: give NAME the TRANSLATE property of SAME-AS.
fn transm__def_same_tr(name : Value, same_as : Value) -> Unit raise {
  let p = get(same_as, q_translate)
  if p is Nil {
    raise LispError::SimpleError(
      "DEF-SAME%TR: \{princ_to_string(same_as)} has no TRANSLATE property, so I can't make an alias.",
    )
  }
  putprop(name, p, q_translate) |> ignore
}

///|
/// BIND-TRANSL-STATE expander: `(bind-transl-state . forms)`.
fn bind_transl_state(forms : Value) -> Value raise {
  let vars = list([
    q_ear_warned_un_declared_vars,
    q_ear_warned_fexprs,
    q_ear_warned_mode_vars,
    q_warned_undefined_variables,
    q_tr_abort,
    q_transl_file,
    q_ear_in_compfile,
    q_ear_in_translate_file,
    q_ear_in_translate,
    q_ear_pre_transl_forms,
    list2(q_d_tr_numer, q_d_tr_numer),
    q_defined_variables,
    q_ear_local,
  ])
  list_star([q_let, vars, forms])
}

///|
/// TR-FORMAT: print a message on each stream of *TRANSLATION-MSGS-FILES*.
fn tr_format(sstring : Value, argl : Value) -> Value raise {
  let files = symval(q_ear_translation_msgs_files)
  let strs = if consp(files) { files } else { list1(files) }
  for v in strs.iter() {
    mformat(cons(v, cons(sstring, argl))) |> ignore
  }
  Nil
}

///|
/// TR expander: `(tr '<maxima expression>)` translates at expansion time.
fn tr(u : Value) -> Value raise {
  if consp(u) && eq(car(u), q_quote) {
    transm__with_transl_state(() => translate_macexpr_toplevel(cadr(u)))
  } else {
    Nil
  }
}

///|
/// MASET expander: `(maset val ar . inds)`.
fn maset(val : Value, ar : Value, inds : Value) -> Value raise {
  if eq(ar, q_mqapply) || (consp(ar) && memq(q_mqapply, ar).truthy()) {
    list_star([q_marrayset, val, car(inds), cdr(inds)])
  } else {
    list([
      q_progn,
      list([
        q_when,
        list2(q_symbolp, ar),
        list([
          q_setf,
          ar,
          list2(q_make_equal_hash_table, if cdr(inds).truthy() { t } else { Nil }),
        ]),
      ]),
      list_star([q_maset1, val, ar, inds]),
    ])
  }
}

///|
/// MAREF expander: `(maref ar . inds)`.
fn maref(ar : Value, inds : Value) -> Value raise {
  if eql(ar, q_mqapply) || (consp(ar) && memq(q_mqapply, ar).truthy()) {
    cons(q_marrayref, cons(car(inds), cdr(inds)))
  } else if consp(ar) {
    list_star([q_marrayref, ar, car(inds), cdr(inds)])
  } else {
    list_star([q_maref1, ar, inds])
  }
}
