// Port of src/errset.lisp: macros and conditions related to signaling
// Maxima errors.
//
// The MAXIMA-$ERROR condition is the runtime's
// `LispError::Condition(intern("maxima-$error"), msg, $error)` (see the
// glue predicate `is_maxima_error`).  The body macros are translated as
// follows:
//
//   (with-$error body...)          with_special(q_ear_merror_signals__dolerror_p, t, () => body)
//   (rat-error-to-merror body...)  errset__rat_error_to_merror(() => body)
//   (with-errcatch-tag-$errors f)  with_errcatch_tag__dolerrors(thunk)
//   (errcatch form)                errcatch(thunk)
//
// where THUNK is a Lisp function of no arguments, e.g.
// `lfunc("form", _ => ...)`.

///|
/// `(rat-error-to-merror body...)`: run F; a throw to RAT-ERR (whose value
/// is the list of MERROR arguments) is turned into a call to MERROR.
fn errset__rat_error_to_merror(f : () -> Value raise) -> Value raise {
  let mut result : Value = Nil
  let mut error_p = true
  let error_args = catch_tag(q_rat_err, () => {
    result = f()
    error_p = false
    Nil
  })
  if error_p {
    merror(car(error_args), cdr(error_args)) |> ignore
  }
  result
}

///|
/// Evaluate FORM (a thunk) while catching throws to the "errcatch tags"
/// ERRORSW, MACSYMA-QUIT and RAT-ERR.  If no throw to an errcatch tag is
/// caught, then the value of FORM is returned.  If a throw to an errcatch
/// tag is caught, then a Maxima error is signaled.
fn with_errcatch_tag__dolerrors(form : Value) -> Value raise {
  let mut done : Value? = None
  catch_tag(q_macsyma_quit, () => {
    catch_tag(q_errorsw, () => {
      // RAT-ERROR-TO-MERROR will catch any throws to RAT-ERR and call merror
      // with a specific error message.
      let v = errset__rat_error_to_merror(() => funcall0(form))
      done = Some(v)
      Nil
    })
  })
  |> ignore
  match done {
    Some(v) => v
    None =>
      // If we're here, then we don't know any information about the
      // error, so just call MERROR with a vague error message.  This
      // message will not be printed by MERROR, but it will be stored in
      // Maxima's error variable.
      with_special(q_ear_merror_signals__dolerror_p, t, () => {
        merr("An error was caught by errcatch.", [])
      })
  }
}

///|
/// The report string of a Lisp error (PRINC-TO-STRING of the condition).
fn errset__error_message(e : Error) -> String {
  match e {
    LispError::SimpleError(msg) => msg
    LispError::Condition(_, msg, _) => msg
    _ => e.to_string()
  }
}

///|
/// This is similar to the classic errset, but errcatch handles lisp and
/// Maxima errors.  FORM is a thunk; returns `(value)` or NIL on error.
fn errcatch(form : Value) -> Value raise {
  with_specials(
    [
      (q_errcatch, cons(symval(q_bindlist), symval(q_loclist))),
      (q_ear_mdebug, Nil),
    ],
    () => {
      let v = with_errcatch_tag__dolerrors(form) catch {
        LispError::Throw(_, _) as e => raise e
        LispError::ReturnFrom(_, _) as e => raise e
        LispError::Go(_) as e => raise e
        e =>
          if is_maxima_error(e) {
            // If this was signaled by MERROR, then it has already handled
            // the setting of the error variable and the printing of any
            // error messages (as applicable).  Either way, we just need to
            // clean up here.
            errlfun1(symval(q_errcatch)) |> ignore
            return Nil
          } else {
            // We store the error report message in the error variable and
            // print the message if errormsg is true.  Then we clean up.
            set(
              q_d_error,
              list2(list2(q_mlist, q_simp), Str(errset__error_message(e))),
            )
            |> ignore
            if symval(q_d_errormsg).truthy() {
              d_errormsg() |> ignore
            }
            errlfun1(symval(q_errcatch)) |> ignore
            return Nil
          }
      }
      list1(v)
    },
  )
}
