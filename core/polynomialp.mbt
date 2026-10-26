// Port of src/polynomialp.lisp: polynomial predicate function.

///|
/// Return true iff n is an integer and n >= 0.
fn d_nonnegintegerp(n : Value) -> Value raise {
  lbool(integerp(n) && num_ge(n, int(0)))
}

///|
/// Returns true if P is a polynomial in the variables in the list VARS.
/// The predicate COEFFP must be a function that evaluates to T for each
/// coefficient, and similarly EXPONP must evaluate to T for all exponents
/// of the variables in VARS.
fn d_polynomialp(
  p : Value,
  vars : Value,
  coeffp? : Value = q_d_constantp,
  exponp? : Value = q_d_nonnegintegerp,
) -> Value raise {
  let mut vars = require_list_or_set(vars, q_d_polynomialp)
  vars = mapcar(x => d_ratdisrep(x), vars)
  if every(s => d_symbolp(s).truthy() || d_subvarp(s).truthy(), vars) {
    polynomialp(d_ratdisrep(p), vars, coeffp, exponp)
  } else {
    merr(
      "~M: The second argument to polynomialp must be a list of symbols: ~M",
      [q_d_polynomialp, cons(list1(q_mlist), vars)],
    )
  }
}

///|
fn polynomialp(p : Value, vars : Value, coeffp : Value, exponp : Value) -> Value raise {
  let c = mfuncall(coeffp, list1(p))
  if c.truthy() {
    return c
  }
  if memalike(p, vars).truthy() {
    return t
  }
  if op_equalp(p, list2(q_mtimes, q_mplus)).truthy() &&
    every(s => polynomialp(s, vars, coeffp, exponp).truthy(), margs(p)) {
    return t
  }
  if op_equalp(p, list1(q_mexpt)).truthy() &&
    polynomialp(car(margs(p)), vars, coeffp, exponp).truthy() {
    return mfuncall(exponp, list1(cadr(margs(p))))
  }
  Nil
}
