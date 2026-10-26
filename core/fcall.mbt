// Port of src/fcall.lisp: run time support for interpreted translated
// Maxima code (MFUNCTION-CALL and friends).

///|
fn d_tr_warnings_get() -> Value raise {
  cons(
    list1(q_mlist),
    mapcar(
      u => list3(list1(q_mlist), car(u), cdr(u)),
      symval(q_ear_tr_runtime_warned),
    ),
  )
}

///|
fn mfunction_call_warn(f : Value, type_ : Value) -> Value raise {
  let w = assq(f, symval(q_ear_tr_runtime_warned))
  if w.truthy() {
    return w
  }
  set(q_ear_tr_runtime_warned, cons(cons(f, type_), symval(q_ear_tr_runtime_warned)))
  |> ignore
  if symval(q_d_tr_warn_bad_function_calls).truthy() {
    let tabl : Value = if eq(type_, q_d_undefined) {
      list2(
        q_undefined_warnp,
        Str("The function was totally undefined. Maybe you want to quote it."),
      )
    } else if eq(type_, q_d_punt_nil) {
      list2(
        q_punt_nil_warnp,
        Str("If you want the value of the function name, use `apply'."),
      )
    } else if eq(type_, q_d_lisp_macro) {
      list2(
        q_lisp_macro_warnp,
        Str("Lisp macros should already be loaded at translate time."),
      )
    } else if eq(type_, q_d_maxima_fexpr) {
      list2(
        q_mfexpr_warnp,
        Str("Maxima fexprs should already be loaded at translate time."),
      )
    } else if eq(type_, q_d_maxima_special_form) {
      list2(
        q_mfexpr_star_warnp,
        Str("Maxima special forms should already be loaded at translate time."),
      )
    } else {
      Nil
    }
    if tabl is Nil {
      ()
    } else if get(f, car(tabl)).truthy() {
      ()
    } else {
      putprop(f, t, car(tabl)) |> ignore
      terpri()
      finish_output()
      princ(Str("Warning: ")) |> ignore
      mgrind(f, Nil) |> ignore
      princ(
        Str(" has a function or macro call which has not been translated properly."),
      )
      |> ignore
      if cdr(tabl).truthy() {
        terpri()
        finish_output()
        princ(cadr(tabl)) |> ignore
      }
    }
  }
  Nil
}

///|
fn mapcar_eval(x : Value) -> Value raise {
  mapcar(a => lisp_eval_form(a), x)
}

///|
/// The MFUNCTION-CALL macro, with F and ARGL the (unevaluated) operator
/// and argument forms.
fn mfunction_call(f : Value, argl : Value) -> Value raise {
  if fboundp(f) {
    apply(f, mapcar_eval(argl))
  } else {
    // loses if the argl could not be evaluated but macsyma &quote
    // functions but the translator should be fixed so that if (mget f
    // 'mfexprp) is t then it doesn't translate as an mfunction-call.
    mfunction_call_aux(f, argl, Nil)
  }
}

///|
fn mfunction_call_aux(
  f : Value,
  argl : Value,
  autoloaded_already_q : Value,
) -> Value raise {
  if functionp_(f).truthy() {
    return apply(f, mapcar_eval(argl))
  }
  if lisp_macro_p(f) {
    mfunction_call_warn(f, q_d_lisp_macro) |> ignore
    return lisp_eval_form(cons(f, argl))
  }
  if !symbolp(f) {
    return merr("apply: expected symbol or function; found: ~M", [f])
  }
  let fp = get(f, q_mfexpr_star)
  if fp.truthy() {
    mfunction_call_warn(f, q_d_maxima_special_form) |> ignore
    return funcall(fp, [cons(list1(f), argl)])
  }
  let fp = mget(f, q_mexpr)
  if fp.truthy() {
    if mget(f, q_mfexprp).truthy() {
      mfunction_call_warn(f, q_d_maxima_fexpr) |> ignore
      return meval(cons(list1(f), argl))
    } else {
      return mlambda(fp, mapcar_eval(argl), f, t, Nil)
    }
  }
  let fp = get(f, q_autoload)
  if fp.truthy() {
    if autoloaded_already_q.truthy() {
      return merr("apply: function ~:@M undefined after loading file ~A", [
        f,
        get(f, q_autoload),
      ])
    } else {
      funcall(symval(q_autoload), [cons(f, fp)]) |> ignore
      return mfunction_call_aux(f, argl, t)
    }
  }
  if boundp(f) {
    mfunction_call_warn(f, q_d_punt_nil) |> ignore
    mapply(symval(f), mapcar_eval(argl), f)
  } else {
    mfunction_call_warn(f, q_d_undefined) |> ignore
    cons(list1(f), mapcar_eval(argl))
  }
}

///|
fn maybe_msymeval(var_ : Value) -> Value raise {
  if boundp(var_) {
    symval(var_)
  } else {
    var_
  }
}
