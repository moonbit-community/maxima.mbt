// Port of share/contrib/smath/smath.lisp (Leo Butler, 2013): display
// output after applying the rules in sm_rules (apply1), via the 1d
// alternative display hook.

///|
fn d_smath_displa(form : Value, sm_rules? : Value) -> Value raise {
  let sm_rules = match sm_rules {
    Some(r) => r
    None => if boundp(q_d_sm_rules) { symval(q_d_sm_rules) } else { Nil }
  }
  if sm_rules.truthy() {
    let rules = cdr(sm_rules)
    with_special(q_ear_alt_display1d, Nil, () => {
      let mut expr = third(form)
      for rule in rules.iter() {
        expr = mfuncall(q_d_apply1, list([expr, rule]))
      }
      funcall(symval(q_ear_displa), [list([first(form), second(form), expr])])
    })
  } else {
    d_to_mx_display() |> ignore
    funcall(symval(q_ear_displa), [form])
  }
}

///|
/// Set-up Maxima to use SMATH_DISPLA to display output.
fn d_to_sm_display() -> Value raise {
  set(q_ear_alt_display1d, symbol_function(q_d_smath_displa)) |> ignore
  set(q_d_outchar, symval(q_ear_smath_outchar))
}

///|
/// Return Maxima to use standard DISPLA for 1d output.
fn d_to_mx_display() -> Value raise {
  set(q_ear_alt_display1d, Nil) |> ignore
  set(q_d_outchar, symval(q_ear_maxima_outchar))
}

///|
/// Execute KILL(S), then re-LOAD smath and set display.
fn d_smkill(s? : Value = Nil) -> Value raise {
  mfuncall(q_d_kill, list1(s)) |> ignore
  mfuncall(q_d_load, list1(Str("smath.mac"))) |> ignore
  d_to_sm_display()
}

///|
fn init_share_smath() -> Unit raise {
  defvar_init(q_ear_displa, symbol_function(q_displa))
  defvar_init(q_ear_maxima_outchar, symval(q_d_outchar))
}
