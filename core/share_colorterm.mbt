// Port of share/contrib/colorterm.lisp (James F. Amundson, 2008): colored
// prompt, input and output in terminal mode via ANSI escape sequences.
// Default colors (*prompt-color* 31, *input-color* 34, *output-color* 30)
// are literal defvars.

///|
fn d_colorterm() -> Value raise {
  let escape_char : Value = Char(code_char(27))
  set(
    q_ear_prompt_prefix,
    format(Nil, "~a[00;~am", [escape_char, symval(q_ear_prompt_color)]),
  )
  |> ignore
  set(
    q_ear_prompt_suffix,
    format(Nil, "~a[00;~am", [escape_char, symval(q_ear_input_color)]),
  )
  |> ignore
  set(
    q_ear_general_display_prefix,
    format(Nil, "~a[00;~am", [escape_char, symval(q_ear_output_color)]),
  )
  |> ignore
  set(q_ear_maxima_epilog, format(Nil, "~a[00m", [escape_char]))
}
