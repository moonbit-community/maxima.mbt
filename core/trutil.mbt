// Port of src/trutil.lisp: translator utilities.

///|
/// TR-GENSYM: an interned gensym (so that it can be written to a file and
/// read back as the same symbol).
fn tr_gensym() -> Value raise {
  // (intern (symbol-name (gensym "TR-GENSYM")) :maxima); port names are
  // the case-inverted CL names.
  sym(symbol_name(gensym(prefix="tr-gensym")))
}

///|
/// PUSH-DEFVAR: make sure there is a form at the beginning of the file that
/// insures the special variable is declared and bound.
fn push_defvar(var_ : Value, val : Value) -> Value raise {
  if memq(var_, symval(q_defined_variables)).truthy() {
    return t
  }
  // $NO_DEFAULT says that the user takes responsibility for binding.
  if eq(symval(q_d_define_variable), q_d_no_default) {
    return t
  }
  // $MODE is same, but double-checks with the declarations available.
  if eq(symval(q_d_define_variable), q_d_mode) {
    let m = tr_get_mode(var_)
    if m.truthy() {
      return m
    }
  }
  let mut l = symval(q_ear_pre_transl_forms)
  while true {
    if l is Nil {
      // push one with a priority of 1, which will be over-rided by any
      // user-specified settings.
      if eq(symval(q_d_define_variable), q_d_mode) {
        tr_format(
          Str("note: variable ~:M being given a default assignment ~:M~%"),
          list([var_, if atom(val) { val } else { cadr(val) }]),
        )
        |> ignore
      }
      return push_pre_transl_form(list([q_def_mtrvar, var_, val, Fix(1L)]))
    }
    let form = car(l)
    if eq(car(form), q_def_mtrvar) && eq(cadr(form), var_) {
      return Nil
    }
    l = cdr(l)
  }
  Nil
}

///|
/// PUSH-PRE-TRANSL-FORM
fn push_pre_transl_form(form : Value) -> Value raise {
  let found = member_equal(form, symval(q_ear_pre_transl_forms))
  if found.truthy() {
    return found
  }
  set(q_ear_pre_transl_forms, cons(form, symval(q_ear_pre_transl_forms)))
  |> ignore
  if symval(q_ear_in_translate).truthy() {
    let mut winp = false
    defer {
      if !winp {
        let _ = barfo(Str("Bad *pre-transl-forms*")) catch { _ => Nil }

      }
    }
    lisp_eval_form(form) |> ignore
    winp = true
    return t
  }
  Nil
}

///|
/// TR-NARGS-CHECK: the maclisp args info format is NIL meaning no info,
/// probably a lexpr, or cons (min . max). Returns the number of arguments.
fn tr_nargs_check(form : Value, args_p? : Value = Nil, nargs? : Value) -> Value raise {
  let nargs = match nargs {
    Some(n) => n
    None => int(length(cdr(form)))
  }
  if args_p.truthy() {
    let n = length(cdr(form))
    let min = {
      let a = car(args_p)
      if a.truthy() {
        a
      } else {
        cdr(args_p)
      }
    }
    let max = cdr(args_p)
    if min.truthy() && num_lt(int(n), min) {
      tr_format(
        Str("error: too few arguments supplied to ~:@M~%~:M~%"),
        list([caar(form), form]),
      )
      |> ignore
    } else if max.truthy() && num_gt(int(n), max) {
      tr_format(
        Str("error: too many arguments supplied to ~:@M~%~:M~%"),
        list([caar(form), form]),
      )
      |> ignore
    }
  }
  nargs
}
