// Port of src/transl.lisp: the Maxima to Lisp translator driver and the
// basic translation properties.
//
// Functions and literals have various MODE properties (at user level set
// up by $MODEDECLARE), such as "$FLOAT" and "$ANY". The function TRANSLATE
// returns a list where the CAR of the list is the MODE of the expression
// and the CDR is the expression to be evaluated by the Lisp evaluator to
// give the equivalent result of evaluating the given macsyma expression
// with the macsyma evaluator. One doesn't know the MODE of an expression
// until seeing the modes of all its parts. See "*UNION-MODE".
//
// The Lisp code produced here is evaluated by the Lisp evaluator
// (`lisp_eval_form`), which also expands the macros of transm.lisp,
// transq.lisp and mdefun.lisp that appear in it (DEFMTRFUN, M-TLAMBDA, ...).
//
// DEF%TR (transm.lisp) defines a TRANSLATE property: in the port each such
// property is a private function `<file>__tr_<op>` installed with
// `transl__deftr` by the file's init function.

///|
let transl__q_intl_gettext : Value = sym("intl:gettext")

///|
/// `'x`
fn transl__quote(x : Value) -> Value {
  list2(q_quote, x)
}

///|
/// Install a DEF%TR translation property.
fn transl__deftr(name : Value, f : (Value) -> Value raise) -> Unit raise {
  let nm = symbol_name(name)
  putprop(name, lfunc(nm + "-translate", args => f(arg(args, 0))), q_translate)
  |> ignore
}

///|
/// The message of a caught Lisp error, for ~A.
fn transl__error_message(e : Error) -> Value {
  match e {
    LispError::SimpleError(m) => Str(m)
    LispError::Condition(_, m, _) => Str(m)
    _ => Str(e.to_string())
  }
}

///|
/// TR-ABORT
fn tr_abort() -> Value raise {
  set(q_tr_abort, t) |> ignore
  Nil
}

///|
/// BARFO
fn barfo(msg : Value) -> Value raise {
  tr_format(Str("Internal translator error: ~M~%"), list1(msg)) |> ignore
  if symval(q_ear_transl_debug).truthy() {
    // (break "transl barfo"): there is no Lisp debugger to enter.
    raise LispError::SimpleError("transl barfo")
  } else {
    tr_abort() |> ignore
    Nil
  }
}

///|
/// SPECIALP
fn specialp(var_ : Value) -> Value raise {
  let o = optionp(var_)
  if o.truthy() {
    o
  } else {
    tr_get_special(var_)
  }
}

///|
/// TR-WARNBREAK: `(and *transl-debug* *tr-warn-break* (break "transl"))`.
fn tr_warnbreak() -> Value raise {
  if symval(q_ear_transl_debug).truthy() && symval(q_ear_tr_warn_break).truthy() {
    raise LispError::SimpleError("transl")
  }
  Nil
}

///|
/// TR-WARNP
fn tr_warnp(val : Value) -> Value raise {
  if val is Nil {
    return Nil
  }
  if symval(q_ear_in_compile).truthy() {
    memq(val, list([q_d_all, q_d_compile, q_d_compfile, q_d_translate]))
  } else if symval(q_ear_in_compfile).truthy() ||
    symval(q_ear_in_translate_file).truthy() {
    memq(val, list([q_d_all, q_d_compfile, q_d_translate]))
  } else if symval(q_ear_in_translate).truthy() {
    memq(val, list([q_d_all, q_d_translate]))
  } else {
    Nil
  }
}

///|
/// Print COMMENT on each message stream (the `comment` part of the WARN-
/// functions).
fn transl__print_comment(comment : Value) -> Unit raise {
  if comment.truthy() {
    for v in symval(q_ear_translation_msgs_files).iter() {
      terpri(stream=v)
      princ(comment, stream=v) |> ignore
    }
  }
}

///|
/// WARN-UNDEFINED-VARIABLE
fn warn_undefined_variable(form : Value) -> Value raise {
  if tr_warnp(symval(q_d_tr_warn_undefined_variable)) is Nil {
    return Nil
  }
  let m = memq(form, symval(q_warned_undefined_variables))
  if m.truthy() {
    m
  } else {
    set(
      q_warned_undefined_variables,
      cons(form, symval(q_warned_undefined_variables)),
    )
    |> ignore
    tr_format(
      Str("warning: encountered undefined variable ~:M in translation.~%"),
      list1(form),
    )
    |> ignore
    tr_warnbreak()
  }
}

///|
/// WARN-UNDECLARED
fn warn_undeclared(form : Value, comment? : Value = Nil) -> Value raise {
  if tr_warnp(symval(q_d_tr_warn_undeclared)) is Nil {
    return Nil
  }
  if member_equal(form, symval(q_ear_warned_un_declared_vars)).truthy() {
    t
  } else {
    set(
      q_ear_warned_un_declared_vars,
      cons(form, symval(q_ear_warned_un_declared_vars)),
    )
    |> ignore
    tr_format(
      Str("warning: no type declaration for ~:M; assume type is 'any'.~%"),
      list1(form),
    )
    |> ignore
    tr_format(Str("note: 'modedeclare' declares types for translation.~%"), Nil)
    |> ignore
    transl__print_comment(comment)
    tr_warnbreak() |> ignore
    Nil
  }
}

///|
/// WARN-MEVAL
fn warn_meval(form : Value, comment? : Value = Nil) -> Value raise {
  if tr_warnp(symval(q_d_tr_warn_meval)).truthy() {
    tr_format(
      Str("warning: emit call to MEVAL for expression: ~:M~%"),
      list1(form),
    )
    |> ignore
    transl__print_comment(comment)
    tr_warnbreak() |> ignore
    q_warned
  } else {
    Nil
  }
}

///|
/// WARN-MODE
fn warn_mode(
  var_ : Value,
  mode : Value,
  newmode : Value,
  comment? : Value = Nil,
) -> Value raise {
  if eq(mode, newmode) {
    return t
  }
  if tr_warnp(symval(q_d_tr_warn_mode)).truthy() &&
    covers(mode, newmode) is Nil &&
    member_equal(list3(var_, mode, newmode), symval(q_ear_warned_mode_vars))
    is Nil {
    set(
      q_ear_warned_mode_vars,
      cons(list3(var_, mode, newmode), symval(q_ear_warned_mode_vars)),
    )
    |> ignore
    tr_format(
      Str("warning: variable ~:M (declared type ~:M) assigned type ~:M.~%"),
      list([var_, mode, newmode]),
    )
    |> ignore
    transl__print_comment(comment)
    tr_warnbreak()
  } else {
    Nil
  }
}

///|
/// WARN-FEXPR
fn warn_fexpr(form : Value, comment? : Value = Nil) -> Value raise {
  if tr_warnp(symval(q_d_tr_warn_fexpr)).truthy() &&
    member_equal(form, symval(q_ear_warned_fexprs)) is Nil {
    set(q_ear_warned_fexprs, cons(form, symval(q_ear_warned_fexprs))) |> ignore
    tr_format(
      Str(
        "warning: ~:M is a special function without a full Lisp translation.~%",
      ),
      list1(form),
    )
    |> ignore
    tr_format(
      Str(
        "warning: calling ~:M in compiled code might not have the desired effect.~%",
      ),
      list1(form),
    )
    |> ignore
    transl__print_comment(comment)
    tr_warnbreak()
  } else {
    Nil
  }
}

///|
/// MACSYMA-SPECIAL-MACRO-P
fn macsyma_special_macro_p(fcn : Value) -> Value raise {
  getl_lm_fcn_prop(fcn, list1(q_macro))
}

///|
/// MACSYMA-SPECIAL-OP-P
fn macsyma_special_op_p(f : Value) -> Value raise {
  getl(f, list([q_fsubr, q_fexpr, q_mfexpr_star, q_mfexpr_stars, q_n_starfexpr]))
}

// ---------------------------------------------------------------------------

///|
/// TR-LOCAL-EXP: the way to call the TRANSLATOR on an expression with
/// locally bound internal mode declarations. Returns (MODE . EXP).
fn tr_local_exp(exp_ : Value, vars_modes : Value) -> Value raise {
  let loc = with_special(q_tr_lambda_punt_assigns, t, () => {
    let mut ll : Value = Nil
    let mut l = vars_modes
    while l is Cons(_) {
      if !variable_p(car(l)).truthy() {
        bad_var_warn(car(l)) |> ignore
      }
      ll = cons(car(l), ll)
      l = cddr(l)
    }
    tr_lambda(
      list4(
        list1(q_lambda),
        cons(list1(q_mlist), ll),
        cons(list1(q_d_modedeclare), vars_modes),
        exp_,
      ),
      Nil,
    )
  })
  let mode = car(loc)
  let exp_ = car(last(loc))
  cons(mode, exp_)
}

///|
/// TRANSLATE-ARGS/UNION-MODE: returns (UNION-MODE . TARGS) where TARGS are
/// the translated ARGS (with individual mode info present) and UNION-MODE
/// is the union of their modes as determined by *UNION-MODE.
fn translate_args_slunion_mode(args : Value) -> Value raise {
  let mut l = args
  let mut targs : Value = Nil
  let mut mode : Value = Nil
  while l is Cons(_) {
    targs = cons(translate(car(l)), targs)
    mode = n_starunion_mode(car(car(targs)), mode)
    l = cdr(l)
  }
  cons(mode, nreverse(targs))
}

///|
/// TR-ARGS
fn tr_args(form : Value) -> Value raise {
  mapcar(x => dconvx(translate(x)), form)
}

///|
/// DTRANSLATE
fn dtranslate(form : Value) -> Value raise {
  cdr(translate(form))
}

///|
/// DCONV
fn dconv(x : Value, mode : Value) -> Value raise {
  if eq(q_d_float, mode) {
    dconv__dolfloat(x)
  } else if eq(q_d_cre, mode) {
    dconv__dolcre(x)
  } else {
    cdr(x)
  }
}

///|
/// DCONVX
fn dconvx(x : Value) -> Value raise {
  if memq(car(x), list2(q_ratexpr, q_pexpr)).truthy() {
    dconv__dolcre(x)
  } else {
    cdr(x)
  }
}

///|
/// DCONV-$FLOAT
fn dconv__dolfloat(x : Value) -> Value raise {
  if memq(car(x), list2(q_d_fixnum, q_d_number)).truthy() {
    if integerp(cdr(x)) {
      lfloat(cdr(x))
    } else {
      list2(q_float, cdr(x))
    }
  } else if eq(q_d_rational, car(x)) {
    if atom(cdr(x)) || !eq(q_quote, cadr(x)) {
      list2(q_d_float, cdr(x))
    } else {
      num_div(lfloat(car(cdr(cadr(cdr(x))))), lfloat(caddr(caddr(x))))
    }
  } else {
    cdr(x)
  }
}

///|
/// DCONV-$CRE
fn dconv__dolcre(x : Value) -> Value raise {
  if eq(q_d_cre, car(x)) {
    cdr(x)
  } else {
    list2(q_ratf, cdr(x))
  }
}

///|
/// COVERS
fn covers(mode1 : Value, mode2 : Value) -> Value raise {
  if eq(mode1, mode2) {
    t
  } else if eq(q_d_float, mode1) {
    memq(mode2, list([q_d_float, q_d_fixnum, q_d_rational]))
  } else if eq(q_d_number, mode1) {
    memq(mode2, list2(q_d_fixnum, q_d_float))
  } else if memq(mode1, symval(q_ear__dolany_modes)).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// TR-MFUN: takes a function name as input.
fn tr_mfun(name : Value) -> Value raise {
  with_special(q_ear_transl_backtrace, Nil, () => {
    let def_form = consfundef(name, Nil, Nil)
    if def_form is Nil {
      tr_abort()
    } else {
      tr_mdefine_toplevel(def_form)
    }
  })
}

///|
/// TR-MDEFINE-TOPLEVEL: right now this handles MDEFMACRO and MDEFINE. The
/// decisions of where to put the actual properties and what kind of defuns
/// to make are punted to the macro package (DEFMTRFUN).
fn tr_mdefine_toplevel(form : Value) -> Value raise {
  let mut and_restp = false
  let name = caar(cadr(form))
  let flags = cdar(cadr(form))
  let args = cdr(cadr(form))
  let body = caddr(form)
  let mut a_args : Value = Nil
  let mut out_forms : Value = Nil
  let tr_unique = symval(q_tr_unique)
  // array functions cannot be LEXPR-like.
  let full_restricted_flag = eq(name, q_mqapply) ||
    memq(q_array, flags).truthy()
  let mut l = args
  while l is Cons(_) {
    let u = car(l)
    if atom(u) {
      a_args = cons(u, a_args)
    } else if !full_restricted_flag &&
      !and_restp &&
      eq(caar(u), q_mlist) &&
      cdr(u).truthy() &&
      atom(cadr(u)) {
      a_args = cons(cadr(u), a_args)
      and_restp = true
    } else {
      a_args = cons(tr_unique, a_args)
    }
    l = cdr(l)
  }
  a_args = nreverse(a_args)
  if eq(name, q_mqapply) {
    // don't you love syntax! do a switch-a-roo here. Calling ourselves
    // recursively like this allows all legal forms and also catches errors.
    // the allowed generalizations aren't necessarily subscripted
    // functions, but we'll act like they are when determining the free
    // vars to capture.
    with_special(
      q_ear_tr_free_vars_to_capture,
      union_(cdar(args), symval(q_ear_tr_free_vars_to_capture)),
      () => tr_mdefine_toplevel(
        list3(
          car(form),
          car(args),
          list3(list1(q_lambda), cons(list1(q_mlist), cdr(args)), body),
        ),
      ),
    )
  } else if memq(tr_unique, a_args).truthy() {
    // WHAT IS "BAD" ABOUT THE ARGUMENT LIST HERE ??
    tr_format(
      Str("error: unhandled argument list in function definition: ~:M~%"),
      list1(cons(list1(q_mlist), args)),
    )
    |> ignore
    tr_abort() |> ignore
    Nil
  } else if memq(caar(form), list2(q_mdefine, q_mdefmacro)).truthy() {
    let kind = if eq(caar(form), q_mdefmacro) {
      q_macro
    } else if memq(q_array, flags).truthy() {
      q_array
    } else {
      q_func
    }
    let t_expr = list3(list1(q_lambda), cons(list1(q_mlist), a_args), body)
    let t_form = {
      let once = get(name, q_once_translated)
      putprop(name, t, q_once_translated) |> ignore
      defer (putprop(name, once, q_once_translated) |> ignore)
      tr_lambda(t_expr, Nil)
    }
    let desc_header = list([
      name,
      car(t_form),
      caar(form),
      lbool(and_restp),
      lbool(eq(kind, q_array)),
    ])
    if eq(kind, q_func) {
      if memq(car(t_form), list2(q_d_any, Nil)) is Nil {
        putprop(name, car(t_form), q_function_mode) |> ignore
      }
    } else if eq(kind, q_array) {
      if memq(car(t_form), list2(q_d_any, Nil)) is Nil {
        decmode_arrayfun(name, car(t_form)) |> ignore
      }
    }
    if symval(q_ear_in_translate).truthy() || symval(q_d_packagefile) is Nil {
      // These are all properties which tell the user that functions are in
      // the environment, and that also allow him to SAVE the functions.
      out_forms = cons(list4(q_defprop, name, t, q_translated), out_forms)
      out_forms = cons(
        list3(q_add2lnc, transl__quote(name), q_d_props),
        out_forms,
      )
      if eq(q_d_all, symval(q_d_savedef)) {
        out_forms = cons(
          list3(
            q_add2lnc,
            transl__quote(cons(cons(name, flags), args)),
            if eq(kind, q_array) {
              q_d_arrays
            } else if eq(kind, q_func) {
              q_d_functions
            } else {
              q_d_macros
            },
          ),
          out_forms,
        )
      }
    }
    if eq(q_d_all, symval(q_d_savedef)) {
      // For some reason one may want to save the interpreted definition
      // even if in a PACKAGEFILE.
      out_forms = cons(
        list4(
          q_mdefprop,
          name,
          list3(list1(q_lambda), cons(list1(q_mlist), args), body),
          if eq(kind, q_array) {
            q_aexpr
          } else if eq(kind, q_macro) {
            q_mmacro
          } else {
            q_mexpr
          },
        ),
        out_forms,
      )
    }
    // once a function has been translated we want to make sure
    // mfunction-call is eliminated.
    remprop(car(desc_header), q_undefined_warnp) |> ignore
    putprop(car(desc_header), Str("I was once translated"), q_once_translated)
    |> ignore
    cons(
      q_progn,
      append(
        nreverse(out_forms),
        list1(cons(q_defmtrfun, cons(desc_header, cddr(t_form)))),
      ),
    )
  } else {
    barfo(sym("?"))
  }
}

///|
/// TRANSLATE-FUNCTION
fn translate_function(name : Value) -> Value raise {
  transm__with_transl_state(() => {
    set(q_ear_in_translate, t) |> ignore
    let lisp_def_form = tr_mfun(name)
    let delete_subr_q = get(name, q_translated).truthy() &&
      get(name, q_expr) is Nil
    if symval(q_tr_abort).truthy() {
      trfail(name)
    } else {
      if delete_subr_q {
        remprop(name, q_subr) |> ignore
      }
      if mget(name, q_trace).truthy() {
        macsyma_untrace(name) |> ignore
      }
      if symval(q_d_savedef) is Nil {
        meval(list2(list1(q_d_remfunction), name)) |> ignore
      }
      let ok = (fn() -> Bool raise {
        lisp_eval_form(lisp_def_form) |> ignore
        true
      })() catch {
        LispError::Throw(_, _) as e => raise e
        LispError::ReturnFrom(_, _) as e => raise e
        LispError::Go(_) as e => raise e
        e => {
          tr_abort() |> ignore
          trfail(name, msg=transl__error_message(e)) |> ignore
          false
        }
      }
      if ok {
        name
      } else {
        Nil
      }
    }
  })
}

///|
/// PUNT-TO-MEVAL
fn punt_to_meval(form : Value, mode? : Value = q_d_any) -> Value raise {
  cons(mode, list2(q_meval, transl__quote(form)))
}

///|
/// TRFAIL
fn trfail(x : Value, msg? : Value = Nil) -> Value raise {
  tr_format(Str("Error: failed to translate ~:@M~%"), list1(x)) |> ignore
  if msg.truthy() {
    tr_format(Str("Message: ~A~%"), list1(msg)) |> ignore
  }
  Nil
}

///|
/// TRANSLATE-AND-EVAL-MACSYMA-EXPRESSION: the hyper-random entry to the
/// transl package! It is used by MLISP for TRANSLATE:TRUE "::=".
fn translate_and_eval_macsyma_expression(form : Value) -> Value raise {
  transm__with_transl_state(() => {
    set(q_ear_in_translate, t) |> ignore
    translator_eval(translate_macexpr_toplevel(form))
  })
}

///|
/// TRANSLATOR-EVAL
fn translator_eval(x : Value) -> Value raise {
  lisp_eval_form(x)
}

///|
/// TR-EVAL-WHEN-SITUATION
fn tr_eval_when_situation(situation : Value) -> Value raise {
  let s = symbol_name(situation)
  match s {
    "$compile" | "compile" | ":compile-toplevel" => q_kw_compile_toplevel
    "$load" | "load" | ":load-toplevel" => q_kw_load_toplevel
    "$eval" | "eval" | ":execute" => q_kw_execute
    _ =>
      raise LispError::SimpleError(
        "\{prin1_to_string(situation)} fell through ECASE expression.",
      )
  }
}

///|
/// TRANSLATE-MACEXPR-TOPLEVEL
fn translate_macexpr_toplevel(form : Value) -> Value raise {
  let bs = bind_all([(q_ear_transl_backtrace, Nil), (q_tr_abort, Nil)])
  defer unbind_all(bs)
  // there are very few top-level special cases, I don't think it would
  // help the code any to generalize TRANSLATE to target levels.
  //
  // Except msetq at top-level is special for ANSI CL.
  let form = toplevel_optimize(form)
  if atom(form) {
    Nil
  } else if eq(caar(form), q_d_eval_when) {
    let mut whens = cadr(form)
    let body = cddr(form)
    whens = if d_listp(whens).truthy() {
      cdr(whens)
    } else if atom(whens) {
      list1(whens)
    } else {
      tr_format(
        Str("error: 'eval_when' argument must be a list or atom; found: ~:M~%"),
        list1(cadr(form)),
      )
      |> ignore
      Nil
    }
    if memq(q_d_translate, whens).truthy() {
      for b in body.iter() {
        meval(b) |> ignore
      }
    }
    if memq(q_d_loadfile, whens).truthy() {
      cons(q_progn, mapcar(x => translate_macexpr_toplevel(x), body))
    } else {
      whens = intersect(whens, list([q_d_compile, q_d_load, q_d_eval]))
      if whens.truthy() {
        cons(
          q_eval_when,
          cons(
            mapcar(x => tr_eval_when_situation(x), whens),
            mapcar(x => translate_macexpr_toplevel(x), body),
          ),
        )
      } else {
        Nil
      }
    }
  } else if memq(caar(form), symval(q_translate_time_evalables)).truthy() {
    meval1(form) |> ignore
    list3(
      q_eval_when,
      list([q_kw_compile_toplevel, q_kw_load_toplevel, q_kw_execute]),
      list2(q_meval_star, transl__quote(form)),
    )
  } else if memq(caar(form), list2(q_mdefine, q_mdefmacro)).truthy() {
    let name = car(car(car(cdr(form))))
    tr_format(Str("note: translating ~:@M~%"), list1(name)) |> ignore
    let trl = tr_mdefine_toplevel(form)
    if symval(q_tr_abort).truthy() {
      tr_format(Str("error: failed to translate ~:@M~%"), list1(name)) |> ignore
      tr_format(Str("note: keep going and hope for the best.~%"), Nil)
      |> ignore
      list2(q_meval_star, transl__quote(form))
    } else {
      trl
    }
  } else if eq(q_mprogn, caar(form)) {
    // note that this ignores the $%% crock.
    cons(q_progn, mapcar(x => translate_macexpr_toplevel(x), cdr(form)))
  } else if eq(q_msetq, caar(form)) || eq(q_d_define_variable, caar(form)) {
    // Toplevel msetq's should really be defparameter instead of setq for
    // Common Lisp.
    with_special(q_ear_macexpr_top_level_form_p, t, () => dtranslate(form))
  } else {
    let t_form = dtranslate(form)
    if symval(q_tr_abort).truthy() {
      list2(q_meval_star, transl__quote(form))
    } else {
      t_form
    }
  }
}

///|
/// TOPLEVEL-OPTIMIZE: it is vital that optimizations be done within the
/// context of variable meta bindings, declarations, etc.
fn toplevel_optimize(form : Value) -> Value raise {
  if atom(form) {
    if symbolp(form) {
      // If this symbol has the constant property, then use its assigned
      // constant value in place of the symbol.
      let v = getl(mget(form, q_d_props), list1(q_d_constant))
      if v.truthy() {
        cadr(v)
      } else {
        form
      }
    } else {
      form
    }
  } else {
    let mut form = form
    let mut kount = 0
    while true {
      if num_gt(int(kount), symval(q_d_tr_optimize_max_loop)) {
        tr_format(
          Str(
            "warning: I've looped ~A times in macro expansion; just give up and return ~:@M~%",
          ),
          list2(symval(q_d_tr_optimize_max_loop), form),
        )
        |> ignore
        return form
      }
      let new_form = toplevel_optimize_1(form)
      if atom(new_form) {
        return toplevel_optimize(new_form)
      } else if physical_equal_value(new_form, form) {
        return form
      } else {
        form = new_form
      }
      kount += 1
    }
    form
  }
}

///|
/// TOPLEVEL-OPTIMIZE-1
fn toplevel_optimize_1(form : Value) -> Value raise {
  let op = car(form)
  if atom(op) || memq(q_array, op).truthy() {
    return form
  }
  let op = car(op)
  let prop = if symval(q_d_transrun).truthy() {
    let p = get(op, q_translated_mmacro)
    if p.truthy() {
      p
    } else {
      mget(op, q_mmacro)
    }
  } else {
    let p = mget(op, q_mmacro)
    if p.truthy() {
      p
    } else {
      get(op, q_translated_mmacro)
    }
  }
  if prop.truthy() {
    return mmacro_apply(prop, form)
  }
  let prop = d_get(op, q_d_optimize)
  if prop.truthy() {
    // interesting, the MAPPLY here causes the simplification of the form
    // and the result.
    return mapply1(prop, list1(form), Str("an optimizer property"), Nil)
  }
  if d_get(op, q_d_transload).truthy() &&
    get(op, q_autoload).truthy() &&
    // check for all reasonable definitions, $OPTIMIZE and MACRO already
    // checked.
    !(
      get_lisp_fun_type(op).truthy() ||
      getl(
        op,
        list([
          q_translate,
          q_mfexpr_star,
          q_mfexpr_stars,
          q_fsubr,
          q_fexpr,
          q_n_starfexpr,
          q_macro,
        ]),
      ).truthy() ||
      mgetl(op, list1(q_mexpr)).truthy()
    ) {
    load_function(op, t) |> ignore
    // to loop.
    return cons(car(form), cdr(form))
  }
  form
}

///|
/// TRANSLATE
fn translate(form : Value) -> Value raise {
  let debug = symval(q_ear_transl_debug).truthy()
  if debug {
    set(q_ear_transl_backtrace, cons(form, symval(q_ear_transl_backtrace)))
    |> ignore
  }
  let form = toplevel_optimize(form)
  if symval(q_ear_transl_debug).truthy() {
    set(q_ear_transl_backtrace, cdr(symval(q_ear_transl_backtrace))) |> ignore
    set(q_ear_transl_backtrace, cons(form, symval(q_ear_transl_backtrace)))
    |> ignore
  }
  let r = if atom(form) { translate_atom(form) } else { translate_form(form) }
  if symval(q_ear_transl_debug).truthy() {
    set(q_ear_transl_backtrace, cdr(symval(q_ear_transl_backtrace))) |> ignore
  }
  r
}

///|
/// TRANSLATE-ATOM
fn translate_atom(form : Value) -> Value raise {
  if numberp(form) {
    return cons(tr_class(form), form)
  }
  let temp = assq(form, symval(q_boolean_object_table))
  if temp.truthy() {
    return cdr(temp)
  }
  let temp = mget(form, q_d_numer)
  if temp.truthy() && symval(q_d_tr_numer).truthy() {
    return cons(q_d_float, temp)
  }
  if implied_quotep(form).truthy() {
    return cons(q_d_any, transl__quote(form))
  }
  if self_evaluating_lisp_object_p(form).truthy() {
    return cons(q_d_any, form)
  }
  if tboundp(form).truthy() {
    let form = teval(form)
    return cons(value_mode(form), form)
  }
  if specialp(form) is Nil {
    warn_undefined_variable(form) |> ignore
  }
  // note that the lisp analysis code must know that the TRD-MSYMEVAL form
  // is a semantic variable.
  let mode = value_mode(form)
  let init_val = assq(mode, symval(q_mode_init_value_table))
  let init_val = if init_val.truthy() {
    cdr(init_val)
  } else {
    transl__quote(form)
  }
  // in the compiler TRD-MSYMEVAL doesn't do a darn thing, but it provides
  // dynamic initialization of variables in interpreted code which is
  // translated in-core. In FILE loaded code the DEFVAR will take care of
  // this.
  push_defvar(form, init_val) |> ignore
  cons(mode, list3(q_trd_msymeval, form, init_val))
}

///|
/// TRANSLATE-FORM
fn translate_form(form : Value) -> Value raise {
  if eq(car(form), q_meval) {
    // for those lispy macsyma forms
    return cons(q_d_any, form)
  }
  if !atom(caar(form)) {
    // this is a check like that in the simplifier. form could result from
    // substitution macros.
    return translate(cons(list1(q_mqapply), cons(caar(form), cdr(form))))
  }
  if memq(q_array, cdar(form)).truthy() {
    // dispatch this bad-boy to another module quick.
    return tr_arraycall(form)
  }
  // TRANSLATE properties have priority.
  let temp = get(caar(form), q_translate)
  if temp.truthy() {
    return funcall(temp, [form])
  }
  let temp = get_lisp_fun_type(caar(form))
  if temp.truthy() {
    return tr_lisp_function_call(form, temp)
  }
  if macsyma_special_macro_p(caar(form)).truthy() {
    return attempt_translate_random_macro_op(form)
  }
  if macsyma_special_op_p(caar(form)).truthy() {
    // a special form not handled yet! foobar!
    return attempt_translate_random_special_op(form)
  }
  if get(caar(form), q_noun).truthy() || get(caar(form), q_operators).truthy() {
    // puntastical case.
    return tr_infamous_noun_form(form)
  }
  // "What does a macsyma function call mean?".
  tr_macsyma_user_function_call(caar(form), cdr(form), form)
}

///|
/// TR-MACSYMA-USER-FUNCTION-CALL
fn tr_macsyma_user_function_call(
  function : Value,
  args : Value,
  form : Value,
) -> Value raise {
  let dflt = symval(q_d_tr_function_call_default)
  if eq(dflt, q_d_apply) {
    translate(
      list3(list1(q_d_apply), caar(form), cons(list1(q_mlist), cdr(form))),
    )
  } else if eq(dflt, q_d_expr) {
    tr_lisp_function_call(form, q_subr)
  } else if eq(dflt, q_d_general) {
    if symval(q_d_tr_bound_function_applyp).truthy() &&
      tboundp(function).truthy() {
      // G(F,X):=F(X+1); case.
      let new_form = list3(
        list1(q_d_apply),
        function,
        cons(list1(q_mlist), args),
      )
      tr_format(
        Str(
          "warning: ~:M is a bound variable in ~:M, but it is used as a function.~%",
        ),
        list2(function, form),
      )
      |> ignore
      tr_format(Str("note: instead I'll translate it as: ~:M~%"), list1(new_form))
      |> ignore
      translate(new_form)
    } else {
      // MFUNCTION-CALL cleverely punts this question to a FSUBR in the
      // interpreter, and a macro in the compiler.
      if member(caar(form), symval(q_ear_untranslated_functions_called)) is Nil {
        set(
          q_ear_untranslated_functions_called,
          cons(caar(form), symval(q_ear_untranslated_functions_called)),
        )
        |> ignore
      }
      call_and_simp(
        function_mode(caar(form)),
        q_mfunction_call,
        cons(caar(form), tr_args(args)),
      )
    }
  } else {
    // This case used to be the most common, a real loser.
    warn_meval(form) |> ignore
    punt_to_meval(form, mode=function_mode(caar(form)))
  }
}

///|
/// ATTEMPT-TRANSLATE-RANDOM-MACRO-OP
fn attempt_translate_random_macro_op(form : Value) -> Value raise {
  warn_fexpr(form) |> ignore
  cons(q_d_any, cons(caar(form), cdr(form)))
}

///|
/// ATTEMPT-TRANSLATE-RANDOM-SPECIAL-OP
fn attempt_translate_random_special_op(form : Value) -> Value raise {
  warn_fexpr(form) |> ignore
  punt_to_meval(form, mode=function_mode(caar(form)))
}

///|
/// TR-LISP-FUNCTION-CALL
fn tr_lisp_function_call(form : Value, type_ : Value) -> Value raise {
  let op = caar(form)
  let args = if memq(type_, list([q_subr, q_lsubr, q_expr])).truthy() {
    mapcar(llis => dconvx(translate(llis)), cdr(form))
  } else {
    mapcar(x => dtranslate(x), cdr(form))
  }
  let mode = function_mode(op)
  call_and_simp(mode, op, args)
}

///|
/// GET-LISP-FUN-TYPE: the once-translated is so that inside translate file
/// where a function has been translated, subsequent calls won't use
/// mfunction call.
fn get_lisp_fun_type(fun : Value) -> Value raise {
  // N.B. this is Functional types. NOT special-forms, lisp special forms
  // are meaningless to macsyma.
  if get(fun, q_n_starlexpr).truthy() {
    return q_lsubr
  }
  if get(fun, q_n_starexpr).truthy() {
    return q_subr
  }
  // *LEXPR & *EXPR gotten from DEFMFUN declarations which is loaded by
  // TrData.
  if mget(fun, q_d_fixed_num_args_function).truthy() {
    return q_subr
  }
  if mget(fun, q_d_variable_num_args_function).truthy() {
    return q_lsubr
  }
  let temp = getl(fun, list([q_expr, q_subr, q_lsubr]))
  if temp.truthy() {
    return car(temp)
  }
  let v = get(fun, q_once_translated)
  if v.truthy() {
    return v
  }
  get(fun, q_translated)
}

///|
/// TR-INFAMOUS-NOUN-FORM: 'F(X,Y) means noun-form. The arguments are
/// evaluated, but the function is cons on, not applied.
fn tr_infamous_noun_form(form : Value) -> Value raise {
  let op = if memq(q_array, car(form)).truthy() {
    list2(caar(form), q_array)
  } else {
    list1(caar(form))
  }
  let args = tr_args(cdr(form))
  cons(
    q_d_any,
    list2(q_simplify, cons(q_list, cons(transl__quote(op), args))),
  )
}

///|
/// IMPLIED-QUOTEP: Some atoms, solely by usage, are self evaluating.
fn implied_quotep(x : Value) -> Value raise {
  safe_get(x, q_implied_quotep)
}

///|
/// SELF-EVALUATING-LISP-OBJECT-P
fn self_evaluating_lisp_object_p(x : Value) -> Value raise {
  lbool(!(symbolp(x) || consp(x)))
}

///|
/// TR-NOSIMPP
fn tr_nosimpp(op : Value) -> Value raise {
  if atom(op) {
    get(op, q_tr_nosimp)
  } else {
    Nil
  }
}

///|
/// CALL-AND-SIMP: conses up the call to the function, adding in the
/// SIMPLIFY if the mode is $ANY.
fn call_and_simp(mode : Value, fun : Value, args : Value) -> Value raise {
  if !eq(mode, q_d_any) || tr_nosimpp(fun).truthy() {
    cons(mode, cons(fun, args))
  } else {
    list3(mode, q_simplify, cons(fun, args))
  }
}

///|
/// $DECLARE_TRANSLATED
fn d_declare_translated(fns : Value) -> Value raise {
  for v0 in cdr(fns).iter() {
    let mut v = v0
    let ok = symbolp(v) ||
      (
        stringp(v) &&
        {
          v = d_verbify(v)
          v.truthy()
        }
      )
    if ok {
      putprop(v, t, q_once_translated) |> ignore
      if memq(v, symval(q_ear_declared_translated_functions)) is Nil {
        set(
          q_ear_declared_translated_functions,
          cons(v, symval(q_ear_declared_translated_functions)),
        )
        |> ignore
      }
    } else {
      merr(
        "declare_translated: arguments must be symbols or strings; found: ~:M",
        [v],
      )
      |> ignore
    }
  }
  Nil
}
