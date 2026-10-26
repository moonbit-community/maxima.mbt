// Port of src/transf.lisp: some floating point translations, with tricks.

///|
/// TRANSLATE-WITH-FLONUM-OP
fn translate_with_flonum_op(form : Value, can_branch_p : Value) -> Value raise {
  let r = translate_args_slunion_mode(cdr(form))
  let mode = car(r)
  let targs = cdr(r)
  let args = mapcar(a => dconv(a, mode), targs)
  let lisp_function = gethash(caar(form), symval(q_ear_flonum_op))
  if eq(mode, q_d_float) && lisp_function.truthy() {
    let call = cons(q_funcall, cons(lisp_function, args))
    if can_branch_p.truthy() && symval(q_d_tr_float_can_branch_complex).truthy() {
      cons(q_d_any, list2(q_complexify, call))
    } else {
      cons(q_d_float, call)
    }
  } else {
    cons(
      q_d_any,
      list2(
        q_simplify,
        cons(q_list, cons(transl__quote(list1(caar(form))), args)),
      ),
    )
  }
}

///|
fn init_transf() -> Unit raise {
  defmvar(
    q_d_tr_float_can_branch_complex,
    val=symval(q_d_tr_float_can_branch_complex),
    Nil,
  )
  |> ignore
  transl__deftr(q_p_sin, form => translate_with_flonum_op(form, Nil))
  for name in [
    "%cos", "%tan", "%cot", "%csc", "%sec", "%acot", "%sinh", "%cosh", "%tanh", "%coth",
    "%csch", "%sech", "%asinh", "%acsch", "%atan", "%atan2", "%erf", "%exp",
  ] {
    transm__def_same_tr(sym(name), q_p_sin)
  }
  transl__deftr(q_p_acos, form => translate_with_flonum_op(form, t))
  for name in [
    "%asin", "%asec", "%acsc", "%acosh", "%asech", "%atanh", "%acoth", "%log", "%plog",
    "%sqrt",
  ] {
    transm__def_same_tr(sym(name), q_p_acos)
  }
}
