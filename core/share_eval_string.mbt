// Port of share/stringproc/eval_string.lisp: parse a string as a Maxima
// expression and evaluate it, or just parse it.

///|
/// eval_string (s) -- parse the string s as a Maxima expression and
/// evaluate it. Only the first expression is parsed and evaluated.
fn d_eval_string(s : Value) -> Value raise {
  if stringp(s) {
    meval(parse_string(s))
  } else {
    merr("eval_string: ~M is not a string.", [s])
  }
}

///|
/// parse_string (s) -- parse the string s as a Maxima expression (do not
/// evaluate it).
fn d_parse_string(s : Value) -> Value raise {
  if stringp(s) {
    parse_string(s)
  } else {
    merr("parse_string: ~M is not a string.", [s])
  }
}

///|
/// (PARSE-STRING S) -- parse the string as a Maxima expression.
fn parse_string(s : Value) -> Value raise {
  set(
    q_ear_parse_string_input_stream,
    make_string_input_stream(lstring(ensure_terminator(s))),
  )
  |> ignore
  with_special(q_ear_mread_prompt, Str(""), () => caddr(
    mread(list1(symval(q_ear_parse_string_input_stream))),
  ))
}

///|
/// Always concatenate a dollar sign to the end of S; PARSE-STRING only
/// parses the first expression in a string.
fn ensure_terminator(s : Value) -> Value raise {
  Str(lstring(s) + "$")
}
