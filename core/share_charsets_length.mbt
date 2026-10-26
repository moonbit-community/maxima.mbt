// Port of share/algebra/charsets/charsets_length.lisp: a length function
// similar to the one in Maple, at least on polynomials. Symbols have length
// equal to the number of characters, etc. Composite objects have length
// given by the sum of lengths of atoms plus length of structures as
// discovered with Maple's dismantle.
//
// This file's $CHARSETS_POLYLENGTH is private
// (charsets_length__d_charsets_polylength): the contract name belongs to
// fateman-len.lisp. Loading the file installs it in the function cell, as
// the Lisp DEFUN does.

///|
/// `(length (write-to-string x))`
fn charsets_length__wlen(x : Value) -> Int {
  prin1_to_string(x).length()
}

// The cases where mapatom returns T
// For a rational the header adds 2, length(3/5)=5
// In maxima 32/76 is represented as ((RAT SIMP) 8 19), simplified
// For a float the header adds 3, length(5.67)=7
// For a subscripted variable, the header adds 3, length(x[12])=8
// If x[12] is assigned, one gets the length of the assignment

///|
fn charsets_atomlength(x : Value) -> Value raise {
  if integerp(x) {
    int(charsets_length__wlen(x))
  } else if d_ratnump(x).truthy() {
    int(charsets_length__wlen(x) - 11)
  } else if floatp(x) {
    int(3 + charsets_length__wlen(x))
  } else if d_subvarp(x).truthy() {
    int(charsets_length__wlen(x) - 12)
  } else if symbolp(x) {
    // to remove the leading $
    int(symbol_name(x).length() - 1)
  } else {
    merr("Mapatom must send the argument on 1 here.", [])
  }
}

///|
/// Maxima atoms
fn charsets_maxatomp(x : Value) -> Value raise {
  if charsets_coeffp(x).truthy() || charsets_variap(x).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// Maxima atoms which can be coefficients
fn charsets_coeffp(x : Value) -> Value raise {
  if atom(x) {
    lbool(integerp(x) || floatp(x))
  } else if listp(car(x)) && d_ratnump(x).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// Maxima atoms which can be variables
fn charsets_variap(x : Value) -> Value raise {
  if symbolp(x) {
    t
  } else if listp(car(x)) && d_subvarp(x).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// An atom (symbol coeff or exponent) causes no problem at the higher level
/// (start) or in a power term. But a bare symbol in a sum or a prod needs to
/// add 1 for the coeff (=1) resp. the exponent (=1), a bare number in a sum
/// needs to add 1 as coeff. This has to be called only on sums and products
fn charsets_atomlength1(x : Value, insum : Value) -> Value raise {
  if insum.truthy() {
    // add 1 for bare numbers and symbols
    num_add(charsets_atomlength(x), Fix(1L))
  } else if symbolp(x) || d_subvarp(x).truthy() {
    // add 1 only for bare symbols in products
    num_add(charsets_atomlength(x), Fix(1L))
  } else {
    charsets_atomlength(x)
  }
}

///|
/// `(reduce #'+ l)`
fn charsets_length__sum(l : Value) -> Value raise {
  let mut s : Value = Fix(0L)
  for x in l.iter() {
    s = num_add(s, x)
  }
  s
}

// The case where mapatom returns false: the polynomial must first be
// expanded to distribute eventual coefficients.

///|
fn charsets_length__d_charsets_polylength(x : Value) -> Value raise {
  let y = d_expand(x)
  // We treat here the exceptional cases at start: isolated atoms, isolated
  // exponent x^m, isolated product like 2*x -> sum (2*x) of length 5 and
  // not sum(2*prod(x^1)) of length 9
  if atom(y) {
    // isolated integer, float or symbol
    charsets_atomlength(y)
  } else if listp(car(y)) && d_ratnump(y).truthy() {
    charsets_atomlength(y)
  } else if listp(car(y)) && d_subvarp(y).truthy() {
    charsets_atomlength(y)
  } else if listp(car(y)) &&
    eq(caar(y), q_mtimes) &&
    length(cdr(y)) == 2 &&
    charsets_coeffp(second(y)).truthy() &&
    charsets_variap(third(y)).truthy() {
    num_add(
      num_add(Fix(3L), charsets_atomlength(second(y))),
      charsets_atomlength(third(y)),
    )
  } else if listp(car(y)) && eq(caar(y), q_mexpt) {
    // isolated x^m
    num_add(
      Fix(3L),
      charsets_length__sum(mapcar(e => charsets_atomlength(e), cdr(y))),
    )
  } else {
    // Now we know we have a sum or a prod or a list of terms
    charsets_polyrecur(y, Nil)
  }
}

///|
/// Monomials at the top level with a coefficient require an extra sum
/// header. We call them impure. One then needs to add 3 to length and
/// reduce by 1 the number of terms
fn charsets_impuremonomialp(x : Value) -> Value raise {
  if charsets_coeffp(cadr(x)).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn charsets_partial_length(
  h_length : Value,
  n__terms : Value,
  x : Value,
  insum : Value,
) -> Value raise {
  num_add(
    num_add(num_add(h_length, Fix(1L)), num_mul(Fix(2L), n__terms)),
    charsets_length__sum(charsets_polyrecur(cdr(x), insum)),
  )
}

///|
/// MEXPT terms don't produce a new header when inside a prod
fn charsets_polyrecur(x : Value, insum : Value) -> Value raise {
  let mut insum = insum
  if charsets_maxatomp(x).truthy() {
    charsets_atomlength1(x, insum)
  } else if listp(car(x)) && eq(caar(x), q_mplus) {
    // sum
    insum = t
    charsets_partial_length(Fix(0L), int(length(cdr(x))), x, insum)
  } else if listp(car(x)) && eq(caar(x), q_mtimes) {
    // monomial
    let mut h_length : Value = Fix(0L)
    let mut n_terms = length(cdr(x))
    if charsets_impuremonomialp(x).truthy() {
      n_terms = n_terms - 1
    }
    if insum is Nil {
      // maple sees it as a sum
      h_length = Fix(3L)
    }
    insum = Nil
    charsets_partial_length(h_length, int(n_terms), x, insum)
  } else if listp(car(x)) && eq(caar(x), q_mexpt) {
    if insum.truthy() {
      // isolated x^m
      num_add(
        Fix(4L),
        charsets_length__sum(mapcar(e => charsets_atomlength(e), cdr(x))),
      )
    } else {
      // x^m in a product
      charsets_length__sum(mapcar(e => charsets_atomlength(e), cdr(x)))
    }
  } else {
    // list of monomials or list of terms
    let ins = insum
    mapcar(y => charsets_polyrecur(y, ins), x)
  }
}

///|
/// Length function similar to maple one for lists of polynomials. In maple
/// there is a header of length n+3 where n is the length or the set or list.
fn d_charsets_length(x : Value) -> Value raise {
  if listp(x) &&
    listp(car(x)) &&
    (eq(caar(x), q_mlist) || eq(caar(x), q_d_set)) {
    num_add(
      int(3 + length(cdr(x))),
      charsets_length__sum(
        mapcar(e => funcall(q_d_charsets_polylength, [e]), cdr(x)),
      ),
    )
  } else if d_charsets_polynomialp(x).truthy() {
    funcall(q_d_charsets_polylength, [x])
  } else {
    merr("Only lists or sets of polynomials supported.", [])
  }
}

///|
/// Top-level forms of charsets_length.lisp: the DEFUN of
/// $CHARSETS_POLYLENGTH.
fn init_share_charsets_length() -> Unit raise {
  defun(q_d_charsets_polylength, args => charsets_length__d_charsets_polylength(
    arg(args, 0),
  ))
}
