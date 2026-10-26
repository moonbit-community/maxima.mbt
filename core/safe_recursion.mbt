// Port of src/safe-recursion.lisp.
//
// This is intended as a simple way to allow code to bounce around the
// (large and confusing) Maxima system without having to worry so much
// about stack overflows from unbounded recursion.
//
// An "unsafe recursion" is defined as one that comes back to the same
// call site with an argument that is either equal to or contains one
// we've seen before.  In that case, we assume that we're either stuck in a
// recursive loop or we're diverging and we should raise an error.
//
// `(with-safe-recursion name arg body...)` expands to
// `call_with_safe_recursion(q_name, arg, lfunc("body", _ => ...))`.

///|
/// Call (FUNCALL THUNK), but record the call on the plist of NAME.  The
/// thunk may recurse through this call site again, but only if the new
/// argument isn't a cons containing ARG as a subtree.  If a recursion is
/// spotted, signal an UNSAFE-RECURSION error (a Lisp condition whose
/// payload is the list (name existing arg)).
fn call_with_safe_recursion(
  name : Value,
  arg : Value,
  thunk : Value,
) -> Value raise {
  let known_args = get(name, q_current_recursion_args)
  let found = find_if(
    known => {
      if consp(known) {
        appears_in(arg, known).truthy()
      } else {
        equal(arg, known)
      }
    },
    known_args,
  )
  if found.truthy() {
    raise LispError::Condition(
      intern("unsafe-recursion"),
      format_to_string(
        "Unsafe recursion at site ~A. Known args ~S contain ~S as a subtree",
        [name, known_args, arg],
      ),
      list([name, known_args, arg]),
    )
  }
  defer setf_get(name, q_current_recursion_args, remove(arg, known_args))
    |> ignore
  setf_get(name, q_current_recursion_args, cons(arg, known_args)) |> ignore
  funcall0(thunk)
}
