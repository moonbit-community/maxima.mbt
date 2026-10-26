// Port of src/trprop.lisp: META-PROP functions.
//
// Many macsyma extension commands, e.g. $INFIX, $TELLSIMP, $DEFTAYLOR work
// by doing explicit PUTPROPS. These META-PROP functions allow selected
// commands to also output DEFPROP's when processed in the Macsyma->lisp
// translation.

///|
/// META-OUTPUT
fn meta_output(form : Value) -> Value raise {
  set(q_meta_prop_l, cons(form, symval(q_meta_prop_l))) |> ignore
  // unfortunately, MATCOM needs to see properties in order to compose
  // tellsimps. so eval it always.
  lisp_eval_form(form)
}

///|
/// META-ADD2LNC
fn meta_add2lnc(item : Value, ssymbol : Value) -> Value raise {
  if symval(q_meta_prop_p).truthy() {
    meta_output(list3(q_add2lnc, list2(q_quote, item), ssymbol))
  } else {
    add2lnc(item, symval(ssymbol))
  }
}

///|
/// META-PUTPROP
fn meta_putprop(ssymbol : Value, item : Value, key : Value) -> Value raise {
  if symval(q_meta_prop_p).truthy() {
    meta_output(list4(q_defprop, ssymbol, item, key)) |> ignore
    item
  } else {
    putprop(ssymbol, item, key)
  }
}

///|
/// META-MPUTPROP
fn meta_mputprop(ssymbol : Value, item : Value, key : Value) -> Value raise {
  if symval(q_meta_prop_p).truthy() {
    meta_output(list4(q_mdefprop, ssymbol, item, key)) |> ignore
    item
  } else {
    mputprop(ssymbol, item, key)
  }
}

///|
/// META-FSET
fn meta_fset(ssymbol : Value, definition : Value) -> Value raise {
  let form = list3(
    q_fset,
    list2(q_quote, ssymbol),
    list3(q_coerce, list2(q_quote, definition), list2(q_quote, q_function)),
  )
  if symval(q_meta_prop_p).truthy() {
    meta_output(form) |> ignore
    definition
  } else {
    // (fset ssymbol (coerce definition 'function)): the definition is a
    // Lisp lambda expression, so the Lisp evaluator does the coercion.
    lisp_eval_form(form)
  }
}

///|
fn init_trprop() -> Unit raise {
  defmvar(q_meta_prop_p, val=symval(q_meta_prop_p), Nil) |> ignore
  defmvar(q_meta_prop_l, val=symval(q_meta_prop_l), Nil) |> ignore
}
