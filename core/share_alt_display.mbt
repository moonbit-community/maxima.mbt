// Port of share/contrib/alt-display/alt-display.lisp (Leo Butler, 2013):
// alternative display functions (*alt-display1d*, *alt-display2d*) and
// prompt settings.

///|
/// The MASSERT macro: `(handler-bind ((error (lambda (msg) (merror "~a"
/// msg)))) (assert assertion vars ,@action))`. ASSERTION is the value of the
/// assertion, ACTION the list of the evaluated datum (a format control) and
/// its arguments. Callers evaluate the action arguments only when the
/// assertion fails, as ASSERT does.
fn massert(assertion : Value, vars : Value, action : Value) -> Value raise {
  ignore(vars)
  if assertion.truthy() {
    return Nil
  }
  let msg = if action is Nil {
    "The assertion failed."
  } else {
    lstring(format(Nil, lstring(car(action)), list_to_array(cdr(action))))
  }
  merr("~a", [Str(msg)])
}

///|
fn d_alt_display_output_type(form? : Value = Nil) -> Value raise {
  if !(listp(form) && car(form).truthy() && listp(car(form)) && caar(form).truthy()) {
    massert(Nil, list1(form), list1(
      d_printf(
        Nil,
        Str(
          "alt_display_output_type(form): form is ill-structured, found: ~a.",
        ),
        list1(form),
      ),
    ))
    |> ignore
  }
  let op = caar(form)
  if eq(op, q_mlabel) {
    q_d_label
  } else if eq(op, q_mtext) {
    q_d_text
  } else {
    q_d_unknown
  }
}

///|
/// *set-prompt-alist*: the options of set_prompt and the corresponding Lisp
/// special variables.
fn share_alt_display__set_prompt_alist() -> Value raise {
  symval(q_ear_set_prompt_alist)
}

///|
fn d_set_prompt(type_ : Value, value : Value, args : Value) -> Value raise {
  if !(
      symbolp(type_) &&
      memq(type_, list([q_d_prefix, q_d_suffix, q_d_general, q_d_prolog, q_d_epilog])).truthy() &&
      (stringp(value) || value is Nil)
    ) {
    massert(Nil, list([type_, value]), list1(
      d_printf(
        Nil,
        Str(
          "set_prompt(type, value): type must be one of prefix, suffix, general, prolog or epilog; value must be a string or false.~%type=~a value=~a",
        ),
        list([type_, value]),
      ),
    ))
    |> ignore
  }
  set(
    cdr(assoc(type_, share_alt_display__set_prompt_alist())),
    if value.truthy() {
      value
    } else {
      Str("")
    },
  )
  |> ignore
  if args is Nil {
    q_d_done
  } else if listp(args) && length(args) > 1 {
    d_set_prompt(car(args), cadr(args), cddr(args))
  } else {
    merr("set_prompt(type,value): missing value.", [])
  }
}

///|
fn d_reset_prompts() -> Value raise {
  for v in share_alt_display__set_prompt_alist().iter() {
    let init = gethash(cdr(v), symval(q_ear_variable_initial_values))
    d_set_prompt(
      car(v),
      if init.truthy() {
        init
      } else {
        Str("")
      },
      Nil,
    )
    |> ignore
  }
  q_d_done
}

///|
fn d_set_alt_display(
  type_ : Value,
  f? : Value = Nil,
  warn? : Value = Nil,
) -> Value raise {
  let ok = (eql(type_, int(1)) || eql(type_, int(2))) &&
    (
      (symbolp(f) && (fboundp(f) || mfboundp(f).truthy())) ||
      (consp(f) && memq(caar(f), list([q_lambda, q_mfexpr])).truthy()) ||
      f is Nil
    )
  if !ok {
    massert(Nil, list([type_, f]), list1(
      Str(
        "set_alt_display(type,f): type must equal 1 or 2, f must be a function, lambda expression or false.",
      ),
    ))
    |> ignore
  }
  let alt_display = if eql(type_, int(1)) {
    q_ear_alt_display1d
  } else if eql(type_, int(2)) {
    q_ear_alt_display2d
  } else {
    raise LispError::SimpleError(
      format_to_string("~S fell through ECASE expression.", [type_]),
    )
  }
  if f.truthy() {
    if warn.truthy() {
      format(error_output, "~&WARNING: Setting ~dd-display to ~(~a~).~%", [
        type_,
        d_printf(Nil, Str("~a"), list1(f)),
      ])
      |> ignore
    }
    // the CL name of the special, as PRINC prints it
    let alt_name : Value = Str(invert_case(symbol_name(alt_display)))
    let error_handler = () => merr("Error in ~a.~%Message: ~a~a reset to default.", [
      alt_name,
      Str(
        with_output_to_string(s => with_special(standard_output, s, () => d_errormsg())
        |> ignore),
      ),
      alt_name,
    ])
    let alt_display_fun = lfunc("alt-display-fun", args => {
      let form = arg(args, 0)
      // convert maxima errors to maxima-$error conditions (a type of error)
      // we can't use handler case to forcibly reset *alt-display[12]d*,
      // because of dynamic scope so we manually keep track of whether an
      // error occurs.
      let mut error_q = true
      errset(() => {
        with_special(q_ear_merror_signals__dolerror_p, t, () => mfuncall(
          f,
          list1(form),
        ))
        |> ignore
        error_q = false
        Nil
      })
      |> ignore
      if error_q {
        d_set_alt_display(type_, f=Nil) |> ignore
        error_handler()
      } else {
        Nil
      }
    })
    set(alt_display, alt_display_fun) |> ignore
  } else {
    if warn.truthy() {
      format(error_output, "~&WARNING: Resetting ~dd-display to default.~%", [
        type_,
      ])
      |> ignore
    }
    set(alt_display, Nil) |> ignore
  }
  q_d_done
}
