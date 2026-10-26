// Port of share/contrib/noninteractive/noninteractive.lisp (Robert Dodier,
// 2007): functions used by noninteractive.mac, which catches asksign and
// askprop queries and constructs conditional expressions.
//
// Loading the file redefines MERROR to throw ((merror) s ...) instead of
// signalling an error; the port installs the redefinition in
// `merror__merror_cell`.

///|
/// Redefinition of MERROR: throw something.
fn share_noninteractive__merror(s : Value, l : Value) -> Value raise {
  d_throw(cons(list1(q_merror), cons(s, l)))
}

///|
fn d_assuming(e : Value) -> Value raise {
  let args = margs(e)
  let assumptions = mapcar(x => meval(x), extract_assumptions(first(args)))
  let my_context = mfuncall(q_d_supcontext, Nil)
  meval(cons(list1(q_d_assume), assumptions)) |> ignore
  defer mfuncall(q_d_killcontext, list1(my_context)) |> ignore
  first(
    last(mapcar(x => mfuncall(share_noninteractive__q_meval1, list1(x)), cdr(args))),
  )
}

///|
/// The Maxima function MEVAL1 of noninteractive.mac (CL symbol |$meval1|).
let share_noninteractive__q_meval1 : Value = sym("$MEVAL1")

///|
fn extract_assumptions(x : Value) -> Value raise {
  if d_listp(x).truthy() {
    cdr(x)
  } else {
    list1(x)
  }
}

///|
/// Remove functions and variables defined at Maxima level so that kill does
/// not affect noninteractive. Unfortunately, this function has to be
/// revised if any more functions or variables are defined.
fn d_delete_noninteractive_stuff_from_infolists() -> Value raise {
  set(q_d_values, delete(sym("$within_MEVAL1"), symval(q_d_values))) |> ignore
  set(
    q_d_functions,
    share_noninteractive__delete_equal(list1(list1(share_noninteractive__q_meval1)), symval(q_d_functions)),
  )
  |> ignore
  set(
    q_d_functions,
    share_noninteractive__delete_equal(
      list2(list1(sym("$enumerate_cases")), sym("$L%")),
      symval(q_d_functions),
    ),
  )
  |> ignore
  set(
    q_d_functions,
    share_noninteractive__delete_equal(
      list([list1(sym("$interleave")), sym("$L1"), sym("$L2")]),
      symval(q_d_functions),
    ),
  )
  |> ignore
  q_d_done
}

///|
fn init_share_noninteractive() -> Unit raise {
  merror__merror_cell.val = Some(share_noninteractive__merror)
}

///|
/// (delete item list :test #'equal)
fn share_noninteractive__delete_equal(item : Value, l : Value) -> Value raise {
  remove_if(x => equal(x, item), l)
}
