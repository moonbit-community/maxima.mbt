// Port of src/var-predicate.lisp: VARP / FREEVAR and their two-argument forms.

///|
fn varp(x : Value) -> Value raise {
  alike1(x, symval(q_var))
}

///|
fn freevar(a : Value) -> Value raise {
  if atom(a) {
    lbool(!eq(a, symval(q_var)))
  } else if varp(a).truthy() {
    Nil
  } else if !atom(car(a)) && memq(q_array, cdar(a)).truthy() {
    if freevar(cdr(a)).truthy() {
      t
    } else {
      merr("~&FREEVAR: variable of integration appeared in subscript.", [])
    }
  } else if freevar(car(a)).truthy() {
    freevar(cdr(a))
  } else {
    Nil
  }
}

///|
/// Same as varp, but the second arg specifies the variable to be tested
/// instead of using the special variable VAR.
fn varp2(x : Value, var2 : Value) -> Value raise {
  alike1(x, var2)
}

///|
/// Like freevar but the second arg specifies the variable to be tested
/// instead of using the special variable VAR.
fn freevar2(a : Value, var2 : Value) -> Value raise {
  if atom(a) {
    lbool(!eq(a, var2))
  } else if varp2(a, var2).truthy() {
    Nil
  } else if !atom(car(a)) && memq(q_array, cdar(a)).truthy() {
    if freevar2(cdr(a), var2).truthy() {
      t
    } else {
      merr("~&FREEVAR: variable of integration appeared in subscript.", [])
    }
  } else if freevar2(car(a), var2).truthy() {
    freevar2(cdr(a), var2)
  } else {
    Nil
  }
}
