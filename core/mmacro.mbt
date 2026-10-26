// Port of src/mmacro.lisp: Maxima macros (::=), macroexpand and
// macroexpand1. MMACRO-APPLY, MMACROEXPANDED, MMACROEXPAND and
// MMACROEXPAND1 live in mlisp_3.mbt like in the Lisp sources.

///|
/// LOCAL MACRO: `(cons (car name) (cdr name))`.
fn copy1cons(name : Value) -> Value raise {
  cons(car(name), cdr(name))
}

///|
fn mdefmacro(form : Value) -> Value raise {
  let form = cdr(form)
  if cdr(form) is Nil || cdddr(form).truthy() {
    merr("macro definition: must have exactly two arguments; found: ~M", [
      cons(list1(q_mdefmacro), form),
    ])
  } else {
    mdefmacro1(car(form), cadr(form))
  }
}

///|
fn mdefmacro1(fun : Value, body : Value) -> Value raise {
  let mut name : Value = Nil
  if atom(fun) ||
    !atom(caar(fun)) ||
    memq(q_array, cdar(fun)).truthy() ||
    {
      name = d_verbify(caar(fun))
      mopp(name).truthy()
    } ||
    eq(name, q_d_all) ||
    eq(name, q_d_op_pct) ||
    eq(name, q_d_op_pct_pct) ||
    eq(name, q_mqapply) {
    // ferret out all the illegal forms
    merr("macro definition: illegal definition: ~M", [fun]) |> ignore
  } else if !eq(name, caar(fun)) {
    // efficiency hack I guess, done in jpg;mlisp (in MDEFINE).
    rplaca(car(fun), name) |> ignore
  }
  let args = cdr(fun)
  let dup = find_duplicate(args, test_=mlisp__eq_fn, key=q_mparam)
  if dup.truthy() {
    merr("macro definition: ~M occurs more than once in the parameter list", [
      mparam(dup),
    ])
    |> ignore
  }
  mredef_check(name) |> ignore
  let mut a = args
  let mut mlexprp = false
  while a is Cons(_) {
    if mdefparam(car(a)).truthy() {
      ()
    } else if mdeflistp(a).truthy() && mdefparam(cadr(car(a))).truthy() {
      mlexprp = true
    } else {
      merr("macro definition: bad argument: ~M", [car(a)]) |> ignore
    }
    a = cdr(a)
  }
  // do all arg checking, then remove MEXPR defn
  remove1(list1(name), q_mexpr, t, symval(q_d_functions), t) |> ignore
  if mlexprp {
    mputprop(name, t, q_mlexprp) |> ignore
  }
  remove_transl_fun_props(name) |> ignore
  add2lnc(cons(list1(name), args), symval(q_d_macros)) |> ignore
  mputprop(name, mdefine1(args, body), q_mmacro) |> ignore
  if symval(q_d_translate).truthy() {
    translate_and_eval_macsyma_expression(
      list3(list1(q_mdefmacro), fun, body),
    )
    |> ignore
  }
  list3(list2(q_mdefmacro, q_simp), fun, body)
}

///|
fn d_macroexpand(form : Value) -> Value raise {
  let form = cdr(form)
  if form is Nil || cdr(form).truthy() {
    merr("macroexpand: must have exactly one argument; found: ~M", [
      cons(list1(q_d_macroexpand), form),
    ])
  } else {
    mmacroexpand(car(form))
  }
}

///|
fn d_macroexpand1(form : Value) -> Value raise {
  let form = cdr(form)
  if form is Nil || cdr(form).truthy() {
    merr("macroexpand1: must have exactly one argument; found: ~M", [
      cons(list1(q_d_macroexpand1), form),
    ])
  } else {
    mmacroexpand1(car(form))
  }
}

///|
/// emulating simpmdef (for mdefine) in jm;simp
fn simpmdefmacro(x : Value, ignored : Value, simp_flag : Value) -> Value raise {
  ignore(ignored)
  ignore(simp_flag)
  cons(list2(q_mdefmacro, q_simp), cdr(x))
}

///|
fn init_mmacro() -> Unit raise {
  // Governs the expansion of Maxima Macros: FALSE, EXPAND or DISPLACE.
  defvar_init(q_d_macroexpansion, Nil)
  mlisp__setting_list(q_d_macroexpansion, list([Nil, q_d_expand, q_d_displace]))
  putprop(q_mdefmacro, q_simpmdefmacro, q_operators) |> ignore
}
