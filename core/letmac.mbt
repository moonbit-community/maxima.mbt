// Port of src/letmac.lisp: the destructuring macros DESTRUCTURING-LET,
// DESTRUCTURING-LET* and DESETQ.
//
// These are compile-time macros.  In translated code, expand a use such as
//   (destructuring-let (((a b . c) expr)) body)
//   (desetq (a . b) expr)
// by hand into ordinary MoonBit bindings of car/cdr paths
// (`let a = car(e); let b = cadr(e); let c = cddr(e)`).
//
// The helper functions below are the macro-expansion helpers; they build
// Lisp code (as data) exactly like the originals.

///|
fn let_macro_get_vars(pattern : Value, vars : Value) -> Value raise {
  if pattern is Nil {
    vars
  } else if atom(pattern) {
    if !symbolp(pattern) {
      raise LispError::SimpleError(
        format_to_string("Garbage found in `let' pattern: ~S", [pattern]),
      )
    }
    set(q_ear_let_macro_vals, cons(Nil, symval(q_ear_let_macro_vals))) |> ignore
    cons(pattern, vars)
  } else {
    let_macro_get_vars(cdr(pattern), let_macro_get_vars(car(pattern), vars))
  }
}

///|
/// `(desetq pattern1 value1 pattern2 value2 ...)`: returns the expansion
/// `(progn (setq ...) ...)`.
fn desetq(p : Value) -> Value raise {
  let mut p = p
  let mut body : Value = Nil
  while !(p is Nil) {
    if atom(cdr(p)) {
      raise LispError::SimpleError(
        format_to_string("Odd number of args to `desetq': ~S", [p]),
      )
    } else if atom(car(p)) {
      if !symbolp(car(p)) {
        raise LispError::SimpleError(
          format_to_string("Garbage found in `desetq' pattern: ~S", [car(p)]),
        )
      }
      if car(p) is Nil {
        raise LispError::SimpleError(
          format_to_string("Bad `desetq' pattern: ~S", [car(p)]),
        )
      }
      body = nconc(body, list1(list([q_setq, car(p), cadr(p)])))
    } else {
      let tem = cons(Nil, Nil)
      body = nconc(
        body,
        cons(
          list_star([q_setq, let_macro_get_last_var(car(p)), tem]),
          let_macro_hair(car(p), cadr(p), tem),
        ),
      )
    }
    p = cddr(p)
  }
  cons(q_progn, body)
}

///|
fn let_macro_get_last_var(pattern : Value) -> Value raise {
  if atom(pattern) {
    pattern
  } else {
    let v = let_macro_get_last_var(cdr(pattern))
    if v.truthy() {
      v
    } else {
      let_macro_get_last_var(car(pattern))
    }
  }
}

///|
fn let_macro_hair(pattern : Value, code : Value, cell : Value) -> Value raise {
  if pattern is Nil {
    Nil
  } else if atom(pattern) {
    rplaca(cell, code) |> ignore
    Nil
  } else {
    let avar = let_macro_get_last_var(car(pattern))
    let dvar = let_macro_get_last_var(cdr(pattern))
    if avar is Nil {
      if dvar is Nil {
        Nil
      } else {
        let_macro_hair(cdr(pattern), list2(q_cdr, code), cell)
      }
    } else if dvar is Nil {
      let_macro_hair(car(pattern), list2(q_car, code), cell)
    } else {
      rplaca(cell, code) |> ignore
      let acell = cons(Nil, Nil)
      let dcell = cons(Nil, Nil)
      cons(
        list_star([q_setq, avar, acell]),
        nconc(
          let_macro_hair(car(pattern), list2(q_car, dvar), acell),
          cons(
            list_star([q_setq, dvar, dcell]),
            let_macro_hair(cdr(pattern), list2(q_cdr, dvar), dcell),
          ),
        ),
      )
    }
  }
}
