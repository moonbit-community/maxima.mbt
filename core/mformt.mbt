// Port of src/mformt.lisp: MFORMAT, a mini version of FORMAT for Maxima
// error messages and other user interaction, with the ~M directive for
// displaying Maxima expressions. The interpreter loop is the expansion of
// the MFORMAT-LOOP / DEF-MFORMAT-OP / DEF-MFORMAT-VAR macros of mforma.lisp.

///|
fn mformt__white_space_p(c : Value) -> Bool {
  match c {
    Char('\n' | '\r' | ' ' | '\t' | '\u{c}' | '\u{b}') => true
    _ => false
  }
}

///|
fn mformt__text_string(chars : Value) -> Value {
  cons(list1(q_text_string), chars)
}

///|
/// MFORMAT is a Maclisp lexpr: N is the list of all arguments,
/// (STREAM CONTROL-STRING . ARGS).
fn mformat(n : Value) -> Value raise {
  let args = list_to_array(n)
  let count = args.length()
  if !(count > 1) {
    // make error message without new symbols.
    maxima_error(Str("MFORMAT: expected two or more arguments."), Nil)
    |> ignore
  }
  let mut stream = args[0]
  let mut sstring = exploden(args[1])
  let mut arg_index = 2
  if stream is Nil || eq(t, stream) {
    stream = symval(standard_output)
  }
  // state variables (DEF-MFORMAT-VAR)
  let mut colon_flag = false
  let mut at_flag = false
  let mut parameter = 0
  let mut text : Value = Nil
  let mut text_temp : Value = Nil
  let mut displa_p = false
  let mut pre_pct_p = false
  let mut post_pct_p = false
  let pop_mformat_arg = fn() -> Value raise {
    if arg_index == count {
      maxima_error(
        Str("POP-MFORMAT-ARG: ran out of mformat args ~a"),
        list1(n),
      )
    } else {
      arg_index += 1
      args[arg_index - 1]
    }
  }
  let push_text_temp = fn() {
    if text_temp.truthy() {
      text = cons(mformt__text_string(nreverse(text_temp)), text)
      text_temp = Nil
    }
  }
  let output_text = fn() raise {
    push_text_temp()
    output_text_star(
      stream,
      text,
      lbool(displa_p),
      lbool(pre_pct_p),
      lbool(post_pct_p),
    )
    |> ignore
    text = Nil
    displa_p = false
    pre_pct_p = false
    post_pct_p = false
  }
  while sstring.truthy() {
    let mut char = car(sstring)
    sstring = cdr(sstring)
    if nparse__chr(char, '~') {
      while true {
        if sstring is Nil {
          maxima_error(
            Str("POP-MFORMAT-STRING: 'mformat' string already exhausted."),
            Nil,
          )
          |> ignore
        }
        char = car(sstring)
        sstring = cdr(sstring)
        let c = match char {
          Char(c) => c
          _ => ' '
        }
        if c == '@' {
          at_flag = true
        } else if c == ':' {
          colon_flag = true
        } else if c == '~' {
          text_temp = cons(char, text_temp)
          break
        } else if mformt__white_space_p(char) {
          while true {
            if sstring is Nil {
              maxima_error(
                Str("TOP-MFORMAT-STRING: 'mformat' string already exhausted."),
                Nil,
              )
              |> ignore
            }
            if !mformt__white_space_p(car(sstring)) {
              break
            }
            sstring = cdr(sstring)
          }
          break
        } else if c < '0' || c > '9' {
          // MFORMAT-DISPATCH-ON-CHAR
          let uc = char_upcase(c)
          if uc == '%' || uc == '&' {
            if text.truthy() || text_temp.truthy() {
              // there is text to output.
              post_pct_p = true
              output_text()
            } else {
              pre_pct_p = true
            }
          } else if uc == 'M' {
            push_text_temp()
            let mut arg = pop_mformat_arg()
            if at_flag && atom(arg) {
              let o = if symbolp(arg) { get(arg, q_op) } else { Nil }
              if o.truthy() {
                arg = o
              }
            }
            if colon_flag {
              text = cons(mformt__text_string(mstring(arg)), text)
            } else {
              displa_p = true
              text = cons(arg, text)
            }
          } else if uc == 'A' {
            push_text_temp()
            text = cons(mformt__text_string(exploden(pop_mformat_arg())), text)
          } else if uc == 'S' {
            push_text_temp()
            let l = explode(pop_mformat_arg())
            let mut c = l
            while consp(c) {
              rplaca(c, get_first_char(car(c))) |> ignore
              c = cdr(c)
            }
            text = cons(mformt__text_string(l), text)
          } else {
            maxima_error(
              Str("MFORMAT-DISPATCH-ON-CHAR: unknown format op. _~a_ ~a"),
              list2(sym(""), ascii(char)),
            )
            |> ignore
          }
          // reset the state variables whose init condition is T
          colon_flag = false
          at_flag = false
          parameter = 0
          break
        } else {
          parameter = c.to_int() - '0'.to_int() + 10 * parameter
        }
      }
    } else {
      text_temp = cons(char, text_temp)
    }
  }
  // (leftover-mformat-args?)
  if arg_index != count {
    maxima_error(
      Str("LEFTOVER-MFORMAT-ARGS?: extra mformat args ~a"),
      list1(n),
    )
    |> ignore
  }
  output_text()
  // Keep from getting bitten by buffering.
  finish_output(stream~)
  ignore(parameter)
  Nil
}

///|
/// Basically the same as MFORMAT, but when DESTINATION is NIL, the function
/// writes its result to a string.
fn aformat(
  destination : Value,
  control_string : Value,
  arguments : Value,
) -> Value raise {
  if destination.truthy() {
    mformat(list_star([destination, control_string, arguments]))
  } else {
    Str(
      with_output_to_string(st => with_special(standard_output, st, fn() raise {
        mformat(list_star([t, control_string, arguments])) |> ignore
      })),
    )
  }
}

///|
/// outputs a META-LINE of text.
fn output_text_star(
  stream : Value,
  text : Value,
  displa_p : Value,
  pre__pct_p : Value,
  post__pct_p : Value,
) -> Value raise {
  let text = nreverse(text)
  if displa_p.truthy() {
    displaf(cons(list1(q_mtext), text), stream) |> ignore
  } else {
    if pre__pct_p.truthy() {
      terpri(stream~)
    }
    for item in text.iter() {
      for c in cdr(item).iter() {
        match c {
          Char(ch) => write_char(ch, stream~)
          _ => ()
        }
      }
    }
    if post__pct_p.truthy() {
      terpri(stream~)
    }
  }
  Nil
}

///|
/// (defun-prop (text-string dimension) (form result) ...)
fn mformt__text_string_dimension(form : Value, result : Value) -> Value raise {
  dimension_atom(maknam(cdr(form)), result)
}

///|
/// for DISPLA to a file.
fn displaf(object_ : Value, stream : Value) -> Value raise {
  if stream is Nil || eq(stream, symval(standard_output)) {
    displa(object_)
  } else {
    with_specials([(standard_output, stream), (q_d_ttyoff, Nil)], fn() raise {
      displa(object_)
    })
  }
}

///|
fn mtell(l : Value) -> Value raise {
  mformat(cons(Nil, l))
}

///|
/// `(def-mformat-op char . body)`: compile-time definition of an MFORMAT
/// directive (the interpreter above has them built in).
fn def_mformat_op(char_ : Value, body : Value) -> Value raise {
  n_plusdef_mformat_op(sym(""), char_, body)
}

///|
fn def_mformat_var(var_ : Value, val : Value, init_ : Value) -> Value raise {
  n_plusdef_mformat_var(sym(""), var_, val, init_)
}

///|
fn mformat_loop(endcode : Value) -> Value raise {
  n_plusmformat_loop(sym(""), endcode)
}

///|
/// The expansion of the PUSH-TEXT-TEMP macro (it refers to the local state
/// of the MFORMAT loop, so only its code can be returned here).
fn push_text_temp() -> Value raise {
  lread(
    "(when text-temp (push (cons '(text-string) (nreverse text-temp)) text) (setq text-temp nil))",
  )
}

///|
/// The expansion of the OUTPUT-TEXT macro (see PUSH-TEXT-TEMP).
fn output_text() -> Value raise {
  lread(
    "(progn (push-text-temp) (output-text* stream text displa-p pre-%-p post-%-p) (setq text nil displa-p nil pre-%-p nil post-%-p nil))",
  )
}

///|
fn init_mformt() -> Unit raise {
  setf_get(sym(""), q_mformat_ops, Nil) |> ignore
  setf_get(sym(""), q_mformat_state_vars, Nil) |> ignore
  putprop(
    q_text_string,
    lfunc("text-string-dimension", args => mformt__text_string_dimension(
      arg(args, 0),
      arg(args, 1),
    )),
    q_dimension,
  )
  |> ignore
}
