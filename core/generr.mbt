// Port of src/generr.lisp: the Maclisp-style ERRSET macro.
//
// Desired behavior:
//   (let ((errset t)) (errset (+ 2 'a)))      ;==> signals error
//   (let ((errset nil)) (errset (+ 2 'a)))    ;==> nil
//   (let ((errset nil)) (errset (+ 2 3)))     ;==> (5)
//
// In translated code, prefer the glue helper `errset(() => form)`
// (returns `Value?`) and test `symval(q_errset)` where the Lisp relies
// on re-signalling.  The declared macro function below takes the form as
// a thunk: `errset_(list1(lfunc("form", _ => ...)))`.

///|
/// `(errset form ...)`: FORM is `(car l)`, a function of no arguments.
/// Returns `(value)` on success; on a Lisp/Maxima error returns NIL, or
/// re-signals the error when the special ERRSET is true.  Non-local
/// control transfers (throw, return-from, go) are not errors and pass
/// through.  (Multiple values are not represented: the result list holds
/// the primary value only.)
fn errset_(l : Value) -> Value raise {
  let form = car(l)
  let v = funcall0(form) catch {
    LispError::Throw(_, _) as e => raise e
    LispError::ReturnFrom(_, _) as e => raise e
    LispError::Go(_) as e => raise e
    e => if symval(q_errset).truthy() { raise e } else { return Nil }
  }
  list1(v)
}
