// Interpreter-level parts of trmode.lisp: $modedeclare (mode_declare),
// $define_variable, $mode_identity and the ASSIGN-MODE-CHECK assign
// property. The translator (and so the rest of trmode.lisp) is excluded
// from the port, so nothing here is in gen_decls and everything is private.
// The translator binds the TBIND property during translation only; with no
// translator it is never set, so TR-GET-MODE is (GET A 'MODE) and PUT-MODE
// is (SETF (GET NAME TYPE) MODE).

///|
let trmode__q_mode_checkp : Value = sym("$mode_checkp")

///|
let trmode__q_mode_check_warnp : Value = sym("$mode_check_warnp")

///|
let trmode__q_mode_check_errorp : Value = sym("$mode_check_errorp")

///|
let trmode__q_define_variable : Value = sym("$define_variable")

///|
let trmode__q_mode_identity : Value = sym("$mode_identity")

///|
let trmode__q_value_check : Value = sym("$value_check")

///|
let trmode__q_tbind : Value = sym("tbind")

///|
/// MSEEMINGLY-UNBOUND
fn trmode__mseemingly_unbound(x : Value) -> Bool raise {
  !boundp(x) || eq(symval(x), x)
}

///|
/// TR-GET-MODE (transl.lisp), interpreter case.
fn trmode__tr_get_mode(a : Value) -> Value {
  get(a, q_mode)
}

///|
/// ASSIGN-MODE-CHECK
fn trmode__assign_mode_check(var_ : Value, value : Value) -> Value raise {
  let mode = trmode__tr_get_mode(var_)
  let user_level = d_get(var_, trmode__q_value_check)
  if mode.truthy() {
    with_specials(
      [(trmode__q_mode_check_warnp, t), (trmode__q_mode_check_errorp, t)],
      () => trmode__chekvalue(var_, mode, val=value),
    )
    |> ignore
  }
  if user_level.truthy() {
    mcall(user_level, list1(value)) |> ignore
  }
  value
}

///|
/// `(defmspec $define_variable (l) ...)`
fn trmode__d_define_variable(l : Value) -> Value raise {
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
  if trmode__mseemingly_unbound(car(l)) {
    meval(list([list1(q_msetq), car(l), cadr(l)]))
  } else {
    meval(car(l))
  }
}

///|
/// `(defmspec $mode_identity (l) ...)`
fn trmode__d_mode_identity(l : Value) -> Value raise {
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
  trmode__chekvalue(obj, trmode__ir_or_extend(car(l)), val=v) |> ignore
  v
}

///|
/// IR-OR-EXTEND
fn trmode__ir_or_extend(x : Value) -> Value raise {
  let name = if symbolp(x) { symbol_name(x) } else { "" }
  let built_in_type = match name {
    "$float" | "$real" | "$floatp" | "$flonum" | "$floatnum" => q_d_float
    "$fixp" | "$fixnum" | "$integer" => q_d_fixnum
    "$rational" | "$rat" => q_d_rational
    "$number" | "$bignum" | "$big" => q_d_number
    "$boolean" | "$bool" => sym("$boolean")
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
fn trmode__d_modedeclare(x : Value) -> Value raise {
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
    trmode__declmode(car(l), trmode__ir_or_extend(cadr(l)), false)
    nl.add(car(l))
    l = cddr(l)
  }
  cons(list1(q_mlist), nl.result())
}

///|
/// DECLMODE; TRFLAG is true only in the translator.
fn trmode__declmode(form : Value, mode : Value, trflag : Bool) -> Unit raise {
  if atom(form) {
    trmode__declvalue(form, mode, trflag)
    if !trflag && symval(trmode__q_mode_checkp).truthy() {
      trmode__chekvalue(form, mode) |> ignore
    }
  } else if eq(caar(form), q_mlist) {
    for l in cdr(form).iter() {
      trmode__declmode(l, mode, trflag)
    }
  } else if memq(q_array, cdar(form)).truthy() {
    trmode__put_mode(caar(form), mode, q_array_mode)
  } else if eq(caar(form), q_d_function) {
    for l in cdr(form).iter() {
      let l = if stringp(l) { d_verbify(l) } else { l }
      trmode__put_mode(l, mode, q_function_mode)
    }
  } else if eq(caar(form), sym("$fixed_num_args_function")) ||
    eq(caar(form), sym("$variable_num_args_function")) {
    for f in cdr(form).iter() {
      let f = if stringp(f) { d_verbify(f) } else { f }
      trmode__put_mode(f, mode, q_function_mode)
      mputprop(f, t, caar(form)) |> ignore
    }
  } else if eq(caar(form), sym("$completearray")) {
    for l in cdr(form).iter() {
      putprop(if atom(l) { l } else { caar(l) }, mode, q_array_mode) |> ignore
    }
  } else if eq(caar(form), q_d_array) {
    for l in cdr(form).iter() {
      mputprop(l, mode, q_array_mode) |> ignore
    }
  } else if eq(caar(form), sym("$arrayfun")) {
    for l in cdr(form).iter() {
      mputprop(l, mode, q_arrayfun_mode) |> ignore
    }
  } else {
    trmode__put_mode(caar(form), mode, q_function_mode)
  }
}

///|
/// DECLVALUE
fn trmode__declvalue(v : Value, mode : Value, trflag : Bool) -> Unit raise {
  let v = if trflag {
    // TEVAL
    let b = if symbolp(v) { get(v, trmode__q_tbind) } else { Nil }
    if b.truthy() {
      b
    } else {
      v
    }
  } else {
    v
  }
  add2lnc(v, symval(q_d_props)) |> ignore
  putprop(v, mode, q_mode) |> ignore
}

///|
/// CHEKVALUE (my-v mode &optional (val (meval1 my-v) val-givenp))
fn trmode__chekvalue(my_v : Value, mode : Value, val? : Value) -> Value raise {
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
  } else if eq(mode, sym("$boolean")) {
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
    trmode__signal_mode_error(my_v, mode, val)
  } else {
    Nil
  }
}

///|
/// SIGNAL-MODE-ERROR
fn trmode__signal_mode_error(
  object : Value,
  mode : Value,
  value : Value,
) -> Value raise {
  let msg = "translator: ~:M was declared with mode ~:M, but it has value: ~M"
  if symval(trmode__q_mode_check_warnp).truthy() &&
    !symval(trmode__q_mode_check_errorp).truthy() {
    mtell(list([Str(msg), object, mode, value]))
  } else if symval(trmode__q_mode_check_errorp).truthy() {
    merror(Str(msg), list([object, mode, value]))
  } else {
    Nil
  }
}

///|
/// PUT-MODE, interpreter case (TBIND is never set without the translator).
fn trmode__put_mode(name : Value, mode : Value, type_ : Value) -> Unit raise {
  putprop(name, mode, type_) |> ignore
}

///|
/// Top-level forms of trmode.lisp needed by the interpreter. Called from
/// init_macsys (trmode has no generated init).
fn trmode__init() -> Unit raise {
  defvar_init(trmode__q_mode_checkp, t)
  defvar_init(trmode__q_mode_check_warnp, t)
  defvar_init(trmode__q_mode_check_errorp, Nil)
  defun(q_assign_mode_check, args => trmode__assign_mode_check(
    args[0],
    args[1],
  ))
  register_mspec(q_d_modedeclare, trmode__d_modedeclare)
  register_mspec(trmode__q_define_variable, trmode__d_define_variable)
  register_mspec(trmode__q_mode_identity, trmode__d_mode_identity)
}
