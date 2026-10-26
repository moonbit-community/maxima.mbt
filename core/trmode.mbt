// Port of src/trmode.lisp: MODEDECLARE, DEFINE_VARIABLE, MODE_IDENTITY
// and the run time mode checking code (the ASSIGN-MODE-CHECK assign
// property).

///|
/// MSEEMINGLY-UNBOUND
fn mseemingly_unbound(x : Value) -> Value raise {
  lbool(!boundp(x) || eq(symval(x), x))
}

///|
/// ASSIGN-MODE-CHECK
fn assign_mode_check(var_ : Value, value : Value) -> Value raise {
  let mode = tr_get_mode(var_)
  let user_level = d_get(var_, q_d_value_check)
  if mode.truthy() {
    with_specials([(q_d_mode_check_warnp, t), (q_d_mode_check_errorp, t)], () => chekvalue(
      var_,
      mode,
      val=value,
    ))
    |> ignore
  }
  if user_level.truthy() {
    mcall(user_level, list1(value)) |> ignore
  }
  value
}

///|
/// DEF%TR $DEFINE_VARIABLE: VAR INIT MODE.
fn trmode__tr_define_variable(form : Value) -> Value raise {
  if length(form) > 3 {
    let var_ = cadr(form)
    let val = caddr(form)
    let mode = cadddr(form)
    let mode_form = list3(list1(q_d_modedeclare), var_, mode)
    translate(mode_form) |> ignore
    // POSSIBLE OVERKILL HERE
    push_pre_transl_form(list2(q_declaim, list2(q_special, var_))) |> ignore
    set(q_defined_variables, cons(var_, symval(q_defined_variables))) |> ignore
    // Get rid of previous definitions put on by the translator.
    let mut l = symval(q_ear_pre_transl_forms)
    while l is Cons(_) {
      // REMOVE SOME OVERKILL
      if eq(caar(l), q_def_mtrvar) && eq(cadar(l), var_) {
        set(q_ear_pre_transl_forms, remove(car(l), symval(q_ear_pre_transl_forms)))
        |> ignore
      }
      l = cdr(l)
    }
    if !eq(mode, q_d_any) {
      // so that the rest of the translation gronks this.
      putprop(var_, q_assign_mode_check, q_assign) |> ignore
    }
    cons(
      q_d_any,
      list([
        q_eval_when,
        list([q_kw_compile_toplevel, q_kw_load_toplevel, q_kw_execute]),
        list2(q_meval_star, transl__quote(mode_form)),
        if !eq(mode, q_d_any) {
          list4(q_defprop, var_, q_assign_mode_check, q_assign)
        } else {
          Nil
        },
        list3(q_def_mtrvar, var_, dtranslate(val)),
      ]),
    )
  } else {
    tr_format(
      Str("error: 'define_variable' must have 3 arguments; found: ~:M~%"),
      list1(form),
    )
    |> ignore
    Nil
  }
}

///|
/// `(defmspec $define_variable (l) ...)`
fn d_define_variable(l : Value) -> Value raise {
  let l = cdr(l)
  if !(length(l) > 2) {
    merror(
      Str("define_variable: expected three arguments; found: ~M"),
      list1(cons(list1(q_mlist), l)),
    )
    |> ignore
  }
  if !symbolp(car(l)) {
    merror(
      Str("define_variable: first argument must be a symbol; found: ~M"),
      list1(car(l)),
    )
    |> ignore
  }
  meval(list([list1(q_d_modedeclare), car(l), caddr(l)])) |> ignore
  if !eq(caddr(l), q_d_any) {
    putprop(car(l), q_assign_mode_check, q_assign) |> ignore
  }
  if mseemingly_unbound(car(l)).truthy() {
    meval(list([list1(q_msetq), car(l), cadr(l)]))
  } else {
    meval(car(l))
  }
}

///|
/// `(defmspec $mode_identity (l) ...)`
fn d_mode_identity(l : Value) -> Value raise {
  let l = cdr(l)
  if length(l) != 2 {
    merror(
      Str("mode_identity: expected two arguments; found: ~M"),
      list1(cons(list1(q_mlist), l)),
    )
    |> ignore
  }
  let obj = cadr(l)
  let v = meval(obj)
  chekvalue(obj, ir_or_extend(car(l)), val=v) |> ignore
  v
}

///|
/// IR-OR-EXTEND
fn ir_or_extend(x : Value) -> Value raise {
  let name = if symbolp(x) { symbol_name(x) } else { "" }
  let built_in_type = match name {
    "$float" | "$real" | "$floatp" | "$flonum" | "$floatnum" => q_d_float
    "$fixp" | "$fixnum" | "$integer" => q_d_fixnum
    "$rational" | "$rat" => q_d_rational
    "$number" | "$bignum" | "$big" => q_d_number
    "$boolean" | "$bool" => q_d_boolean
    "$list" | "$listp" => q_d_list
    "$complex" => q_d_complex
    "$any" | "$none" | "$any_check" => q_d_any
    _ => Nil
  }
  if built_in_type.truthy() {
    built_in_type
  } else {
    mtell(
      list2(
        Str(
          "modedeclare: ~M is not a built-in type; assuming it is a Maxima extension type.",
        ),
        x,
      ),
    )
    |> ignore
    x
  }
}

///|
/// `(defmspec $modedeclare (x) ...)`
fn d_modedeclare(x : Value) -> Value raise {
  let x = cdr(x)
  if oddp(int(length(x))) {
    merror(
      Str("mode_declare: expected an even number of arguments; found: ~M"),
      list1(cons(list1(q_mlist), x)),
    )
    |> ignore
  }
  let nl = Collector::new()
  let mut l = x
  while !(l is Nil) {
    declmode(car(l), ir_or_extend(cadr(l)), Nil) |> ignore
    nl.add(car(l))
    l = cddr(l)
  }
  cons(list1(q_mlist), nl.result())
}

///|
/// DECLMODE; TRFLAG is true only in the translator.
fn declmode(form : Value, mode : Value, trflag : Value) -> Value raise {
  if atom(form) {
    declvalue(form, mode, trflag) |> ignore
    if trflag is Nil && symval(q_d_mode_checkp).truthy() {
      chekvalue(form, mode) |> ignore
    }
  } else if eq(caar(form), q_mlist) {
    for l in cdr(form).iter() {
      declmode(l, mode, trflag) |> ignore
    }
  } else if memq(q_array, cdar(form)).truthy() {
    declarray(caar(form), mode) |> ignore
  } else if eq(caar(form), q_d_function) {
    for l in cdr(form).iter() {
      let l = if stringp(l) { d_verbify(l) } else { l }
      declfun(l, mode) |> ignore
    }
  } else if eq(caar(form), q_d_fixed_num_args_function) ||
    eq(caar(form), q_d_variable_num_args_function) {
    for f in cdr(form).iter() {
      let f = if stringp(f) { d_verbify(f) } else { f }
      declfun(f, mode) |> ignore
      mputprop(f, t, caar(form)) |> ignore
    }
  } else if eq(caar(form), q_d_completearray) {
    for l in cdr(form).iter() {
      putprop(if atom(l) { l } else { caar(l) }, mode, q_array_mode) |> ignore
    }
  } else if eq(caar(form), q_d_array) {
    for l in cdr(form).iter() {
      mputprop(l, mode, q_array_mode) |> ignore
    }
  } else if eq(caar(form), q_d_arrayfun) {
    for l in cdr(form).iter() {
      mputprop(l, mode, q_arrayfun_mode) |> ignore
    }
  } else {
    declfun(caar(form), mode) |> ignore
  }
  Nil
}

///|
/// DECLVALUE
fn declvalue(v : Value, mode : Value, trflag : Value) -> Value raise {
  let v = if trflag.truthy() { teval(v) } else { v }
  add2lnc(v, symval(q_d_props)) |> ignore
  setf_tr_get_mode(mode, v)
}

///|
/// CHEKVALUE (my-v mode &optional (val (meval1 my-v) val-givenp))
fn chekvalue(my_v : Value, mode : Value, val? : Value) -> Value raise {
  let val_givenp = val is Some(_)
  let val = match val {
    Some(v) => v
    None => meval1(my_v).0
  }
  if !(val_givenp || !eq(my_v, val)) {
    return Nil
  }
  // hack because macsyma PROG binds variable to itself.
  let checker : ((Value) -> Bool raise)? = if eq(mode, q_d_float) {
    Some(u => floatp(u))
  } else if eq(mode, q_d_fixnum) {
    Some(u => integerp(u))
  } else if eq(mode, q_d_number) {
    Some(u => numberp(u))
  } else if eq(mode, q_d_list) {
    Some(u => d_listp(u).truthy())
  } else if eq(mode, q_d_boolean) {
    Some(u => eq(u, t) || u is Nil)
  } else {
    None
  }
  let nchecker = if eq(mode, q_d_float) {
    q_d_real
  } else if eq(mode, q_d_fixnum) {
    q_d_integer
  } else if eq(mode, q_d_complex) {
    q_d_complex
  } else {
    Nil
  }
  let mut not_done = true
  let bad = match checker {
    Some(c) if !c(val) =>
      if nchecker.truthy() {
        not_done = false
        !mfuncall(q_d_featurep, list2(val, nchecker)).truthy()
      } else {
        true
      }
    _ => false
  }
  let bad = bad ||
    (not_done &&
    nchecker.truthy() &&
    !mfuncall(q_d_featurep, list2(val, nchecker)).truthy())
  if bad {
    signal_mode_error(my_v, mode, val)
  } else {
    Nil
  }
}

///|
/// SIGNAL-MODE-ERROR
fn signal_mode_error(
  object_ : Value,
  mode : Value,
  value : Value,
) -> Value raise {
  let msg = "translator: ~:M was declared with mode ~:M, but it has value: ~M"
  if symval(q_d_mode_check_warnp).truthy() &&
    !symval(q_d_mode_check_errorp).truthy() {
    mtell(list([Str(msg), object_, mode, value]))
  } else if symval(q_d_mode_check_errorp).truthy() {
    merror(Str(msg), list([object_, mode, value]))
  } else {
    Nil
  }
}

///|
/// TR-DECLARE-VARMODE
fn tr_declare_varmode(variable : Value, mode : Value) -> Value raise {
  declvalue(variable, ir_or_extend(mode), t)
}

///|
/// DEF%TR $MODE_IDENTITY
fn trmode__tr_mode_identity(form : Value) -> Value raise {
  cons(ir_or_extend(cadr(form)), dtranslate(caddr(form)))
}

///|
/// DEF%TR $MODEDECLARE: if we really wanted to we could cons up a list here
/// at translate time and return it to match the return value in the
/// interpreted case
fn trmode__tr_modedeclare(form : Value) -> Value raise {
  let mut l = cdr(form)
  while l is Cons(_) {
    declmode(car(l), ir_or_extend(cadr(l)), t) |> ignore
    l = cddr(l)
  }
  cons(q_d_any, Nil)
}

///|
/// ASS-EQ-REF
fn ass_eq_ref(table : Value, key : Value, dflt? : Value = Nil) -> Value raise {
  let val = assq(key, table)
  if val.truthy() {
    cdr(val)
  } else {
    dflt
  }
}

///|
/// ASS-EQ-SET
fn ass_eq_set(val : Value, table : Value, key : Value) -> Value raise {
  let cell = assq(key, table)
  if cell.truthy() {
    rplacd(cell, val) |> ignore
    table
  } else {
    cons(cons(key, val), table)
  }
}

///|
/// PUT-MODE
fn put_mode(name : Value, mode : Value, type_ : Value) -> Value raise {
  if get(name, q_tbind).truthy() {
    setf_tr_get_val_modes(ass_eq_set(mode, tr_get_val_modes(name), type_), name)
  } else {
    putprop(name, mode, type_)
  }
}

///|
/// DECLARRAY
fn declarray(ar : Value, mode : Value) -> Value raise {
  put_mode(ar, mode, q_array_mode)
}

///|
/// DECLFUN
fn declfun(f : Value, mode : Value) -> Value raise {
  put_mode(f, mode, q_function_mode)
}

///|
/// UDM-ERR: 1/2 is not $RATIONAL. bad name. it means CRE form.
fn udm_err(mode : Value) -> Value raise {
  mtell(list2(Str("translator: no such mode declaration: ~:M~%"), mode))
}

///|
fn init_trmode() -> Unit raise {
  for v in [q_d_mode_checkp, q_d_mode_check_warnp, q_d_mode_check_errorp] {
    defmvar(v, val=symval(v), Nil) |> ignore
  }
  transl__deftr(q_d_define_variable, trmode__tr_define_variable)
  transl__deftr(q_d_mode_identity, trmode__tr_mode_identity)
  transl__deftr(q_d_modedeclare, trmode__tr_modedeclare)
}
