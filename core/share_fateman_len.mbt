// Port of share/algebra/charsets/fateman-len.lisp (from Fateman): the size
// of a rational function, a ranking of complexity for the characteristic
// set method.

///|
fn d_charsets_polylength(x : Value) -> Value raise {
  let y = ratf(x)
  // numerator + denominator
  num_add(cp1(cadr(y)), cp1(cddr(y)))
}

///|
/// sum up the sizes of the terms in the rational form polynomial p
fn cp1(p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    // a constant's length in decimal chars
    flatsize(p)
  } else {
    let mut count : Value = Fix(0L)
    let mut i = cdr(p)
    while i.truthy() {
      count = num_add(count, flatsize(car(i))) // length of exponent
      count = num_add(count, cp1(cadr(i))) // length of coefficient, recursively
      i = cddr(i)
    }
    // one more for the variable name
    num_add(count, Fix(1L))
  }
}
