// Port of src/displm.lisp: macros for the DISPLA package (as functions).

///|
/// (PUSH-STRING "foo" RESULT) --> (SETQ RESULT (APPEND '(#/o #/o #/f) RESULT))
///
/// As a function it cannot assign the caller's variable: it returns the new
/// value, so `(push-string s result)` becomes
/// `result = push_string(s, result)`. If SYMBOL is a symbol it is taken as
/// a special variable and assigned as well.
fn push_string(string_ : Value, symbol : Value) -> Value raise {
  if symbol is Sym(_) && !(symbol is Nil) {
    set(symbol, append(nreverse(exploden(string_)), symval(symbol)))
  } else {
    append(nreverse(exploden(string_)), symbol)
  }
}

///|
/// (DISPLA-DEF [<operator>] [<dissym> | <l-dissym> <r-dissym>] [<lbp>] [<rbp>])
/// Sets up the display dispatch properties of OPERATOR. If only one integer
/// appears in REST, then it is taken to be an RBP.
fn displa_def(operator : Value, dim_function : Value, rest_ : Value) -> Value raise {
  let mut l_dissym : Value = Nil
  let mut r_dissym : Value = Nil
  let mut lbp : Value = Nil
  let mut rbp : Value = Nil
  for x in rest_.iter() {
    if stringp(x) {
      if l_dissym.truthy() {
        r_dissym = x
      } else {
        l_dissym = x
      }
    } else if integerp(x) {
      if rbp.truthy() {
        lbp = rbp
      }
      rbp = x
    } else {
      merror(Str("DISPLA-DEF: unrecognized object: ~a"), list1(x)) |> ignore
    }
  }
  if l_dissym.truthy() {
    l_dissym = if r_dissym.truthy() {
      cons(exploden(l_dissym), exploden(r_dissym))
    } else {
      exploden(l_dissym)
    }
  }
  putprop(operator, dim_function, q_dimension) |> ignore
  if l_dissym.truthy() {
    putprop(operator, l_dissym, q_dissym) |> ignore
  }
  if lbp.truthy() {
    putprop(operator, lbp, q_lbp) |> ignore
  }
  if rbp.truthy() {
    putprop(operator, rbp, q_rbp) |> ignore
  }
  operator
}
