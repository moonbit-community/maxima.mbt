// Port of src/evalw.lisp: EVAL_WHEN.
//
// EVAL_WHEN(TRANSLATE,FOO(ME),BAZ())$
// EVAL_WHEN([LOADFILE,BATCH],INITIALIZE())$

///|
/// Assuming that this will only be a top-level form, it will only be seen
/// by MEVAL when a file is batched.
fn d_eval_when(argl : Value) -> Value raise {
  let argl = cdr(argl)
  if length(argl) < 2 || !(atom(car(argl)) || d_listp(car(argl)).truthy()) {
    merr("eval_when: incorrect arguments; found: ~M", [car(argl)]) |> ignore
  }
  let whens = if d_listp(car(argl)).truthy() {
    cdar(argl)
  } else {
    list1(car(argl))
  }
  if member(q_d_batch, whens).truthy() {
    cons(list1(q_d_evaluated_when), mapcar(x => meval(x), cdr(argl)))
  } else {
    q_d_not_evaluated_when
  }
}
