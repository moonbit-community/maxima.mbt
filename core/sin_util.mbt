// Port of src/sin-util.lisp: small predicates used by the integrator.

///|
/// Returns x if x is an integer, else false.
fn integerp2(x : Value) -> Value raise {
  if !numberp(x) {
    Nil
  } else if !floatp(x) {
    x
  } else {
    let u = maxima_rationalize(x)
    if equal(cdr(u), Fix(1L)) {
      car(u)
    } else {
      Nil
    }
  }
}

///|
/// Returns 2*x if 2*x is an integer, else nil.
fn integerp1(x : Value) -> Value raise {
  integerp2(mul2_star(Fix(2L), x))
}

///|
fn zerp(a : Value) -> Value raise {
  lbool(equal(a, Fix(0L)))
}

///|
fn nonzerp(a : Value) -> Value raise {
  lbool(!equal(a, Fix(0L)))
}
