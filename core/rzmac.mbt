// Port of src/rzmac.lisp: assorted macros for the general representation
// (as functions). Macros taking `&rest body` receive the Lisp list of their
// arguments. (*BIND* is a body macro; callers expand it by hand.)

///|
/// Returns the negation of VALUE if PREDICATE is true. Otherwise, just
/// returns VALUE.
fn negate_if(predicate : Value, value : Value) -> Value raise {
  if predicate.truthy() {
    neg(value)
  } else {
    value
  }
}

///|
/// Setq's the first variable to VALUE if SWITCH is true, and sets the second
/// variable otherwise. As a function this can only assign special variables:
/// FIRST-VAR and SECOND-VAR are the variables' symbols. (Call sites setting
/// lexical variables must be translated inline.)
fn set_either(
  first_var : Value,
  second_var : Value,
  switch : Value,
  value : Value,
) -> Value raise {
  if switch.truthy() {
    set(first_var, value)
  } else {
    set(second_var, value)
  }
}

///|
/// symbolic arithmetic macros: (m+ . body) = (add* . body)
fn m_plus(body : Value) -> Value raise {
  add_star(body)
}

///|
fn m_star(body : Value) -> Value raise {
  mul_star(body)
}

///|
fn m1_plus(x : Value) -> Value raise {
  add_star(list2(Fix(1L), x))
}

///|
fn m1_(x : Value) -> Value raise {
  add_star(list2(Fix(-1L), x))
}

///|
fn m_sl_sl(a1 : Value, a2? : Value) -> Value raise {
  match a2 {
    Some(a2) => div_star(a1, a2)
    None => inv_star(a1)
  }
}

///|
fn m_(a1 : Value, a2? : Value) -> Value raise {
  match a2 {
    Some(a2) => sub_star(a1, a2)
    None => mul_star(list2(Fix(-1L), a1))
  }
}

///|
fn m_hat(b : Value, e : Value) -> Value raise {
  power_star(b, e)
}

///|
fn m_plusl(l : Value) -> Value raise {
  addn(l, Nil)
}

///|
fn m_starl(l : Value) -> Value raise {
  muln(l, Nil)
}

///|
fn m_plust(body : Value) -> Value raise {
  add(body)
}

///|
fn m_start(body : Value) -> Value raise {
  mul(body)
}

///|
fn m1_plust(x : Value) -> Value raise {
  add(list2(Fix(1L), x))
}

///|
fn m1_t(x : Value) -> Value raise {
  add(list2(Fix(-1L), x))
}

///|
fn m_sl_slt(a1 : Value, a2? : Value) -> Value raise {
  match a2 {
    Some(a2) => div(a1, a2)
    None => inv(a1)
  }
}

///|
fn m_t(a1 : Value, a2? : Value) -> Value raise {
  match a2 {
    Some(a2) => sub(a1, a2)
    None => neg(a1)
  }
}

///|
fn m_hatt(b : Value, e : Value) -> Value raise {
  power(b, e)
}

///|
fn m_pluslt(l : Value) -> Value raise {
  addn(l, t)
}

///|
fn m_starlt(l : Value) -> Value raise {
  muln(l, t)
}
