// Port of src/ratmac.lisp: accessor macros for the canonical rational
// expression (CRE) representation used by the rational function package.
//
// Polynomials
// ===========
// A polynomial in a single variable is a sparse list whose first element is
// the main variable (a gensym from GENVAR); the rest is a plist mapping powers
// (in descending order) to coefficients, e.g. 42*x^2+1 is (x 2 42 0 1).
// Coefficients may themselves be polynomials in variables that come later in
// the POINTERGP order. A bare number (an atom) is a degree-zero polynomial;
// test with PCOEFP.
//
// Rational expressions
// ====================
// A rational expression p/q is the cons (p . q); zero is (0 . 1).
//
// This file also holds small private helpers shared by the rat3*/nrat4/
// ratout ports (all prefixed `ratmac__`).

///|
/// `(pzerop x)`: true iff X is syntactically the zero polynomial.
fn pzerop(x : Value) -> Value raise {
  lbool(ratmac__pz(x))
}

///|
/// Bool version of PZEROP.
fn ratmac__pz(x : Value) -> Bool {
  match x {
    Fix(n) => n == 0L
    Flo(d) => d == 0.0
    _ => false
  }
}

///|
/// `(pointergp a b)`: (> (symbol-value a) (symbol-value b))
fn pointergp(a : Value, b : Value) -> Value raise {
  lbool(ratmac__pgp(a, b))
}

///|
/// Bool version of POINTERGP.
fn ratmac__pgp(a : Value, b : Value) -> Bool raise {
  match (symbol_value(a), symbol_value(b)) {
    (Fix(x), Fix(y)) => x > y
    (x, y) => num_gt(x, y)
  }
}

///|
fn pcoefp(e : Value) -> Value raise {
  lbool(atom(e))
}

///|
fn pzero() -> Value raise {
  Fix(0L)
}

///|
fn ptzerop(terms : Value) -> Value raise {
  lbool(terms is Nil)
}

///|
fn ptzero() -> Value raise {
  Nil
}

///|
fn cminus(c : Value) -> Value raise {
  num_neg(c)
}

///|
fn cminusp(c : Value) -> Value raise {
  lbool(minusp(c))
}

///|
fn valget(item : Value) -> Value raise {
  symbol_value(item)
}

///|
fn valput(item : Value, val : Value) -> Value raise {
  set(item, val)
}

///|
/// `(algv v)` = (and $algebraic (get v 'tellrat))
fn algv(v : Value) -> Value raise {
  ratmac__algv(v)
}

///|
fn ratmac__algv(v : Value) -> Value {
  if symval(q_d_algebraic).truthy() {
    get(v, q_tellrat)
  } else {
    Nil
  }
}

///|
/// `(rzero)` expands to the quoted constant '(0 . 1); a fresh cons here.
fn rzero() -> Value raise {
  cons(Fix(0L), Fix(1L))
}

///|
fn rzerop(a : Value) -> Value raise {
  lbool(ratmac__pz(car(a)))
}

///|
/// `(primpart p)` = (second (oldcontent p))
fn primpart(p : Value) -> Value raise {
  second(oldcontent(p))
}

///|
/// `(make-poly var)` = (var 1 1); `(make-poly var terms)` = (psimp var terms);
/// `(make-poly var e c)` = (var e c); `(make-poly var e c terms)` =
/// (psimp var (list* e c terms)).
fn make_poly(
  var_ : Value,
  terms_or_e? : Value,
  c? : Value,
  terms? : Value,
) -> Value raise {
  match (terms_or_e, c, terms) {
    (None, _, _) => cons(var_, list2(Fix(1L), Fix(1L)))
    (Some(t), None, _) => psimp(var_, t)
    (Some(e), Some(c), None) => list3(var_, e, c)
    (Some(e), Some(c), Some(ts)) => psimp(var_, cons(e, cons(c, ts)))
  }
}

///|
fn p__var(p : Value) -> Value raise {
  car(p)
}

///|
fn p__terms(p : Value) -> Value raise {
  cdr(p)
}

///|
fn p__lc(p : Value) -> Value raise {
  caddr(p)
}

///|
fn p__le(p : Value) -> Value raise {
  cadr(p)
}

///|
fn p__red(p : Value) -> Value raise {
  cdddr(p)
}

///|
fn pt_lc(terms : Value) -> Value raise {
  cadr(terms)
}

///|
fn pt_le(terms : Value) -> Value raise {
  car(terms)
}

///|
fn pt_red(terms : Value) -> Value raise {
  cddr(terms)
}

// ---------------------------------------------------------------------------
// Shared private helpers.

///|
/// `(ignore-rat-err body)`: run F with the RAT-ERR tag established; a throw
/// to RAT-ERR (from RAT-ERROR) makes the form evaluate to NIL.
fn ratmac__ignore_rat_err(f : () -> Value raise) -> Value raise {
  let mut result : Value = Nil
  let mut error_p = true
  catch_tag(q_rat_err, () => {
    result = f()
    error_p = false
    Nil
  })
  |> ignore
  if error_p {
    Nil
  } else {
    result
  }
}

///|
/// `(rat-error msg)`
fn ratmac__rat_error(msg : String) -> Value raise {
  rat_error(list1(Str(msg)))
}

///|
/// Lisp `(= a b)` on numbers.
fn ratmac__eqn(a : Value, b : Value) -> Bool raise {
  match (a, b) {
    (Fix(x), Fix(y)) => x == y
    _ => num_eq(a, b)
  }
}

///|
/// Lisp `(> a b)` on numbers.
fn ratmac__gt(a : Value, b : Value) -> Bool raise {
  match (a, b) {
    (Fix(x), Fix(y)) => x > y
    _ => num_gt(a, b)
  }
}

///|
/// Lisp `(< a b)` on numbers.
fn ratmac__lt(a : Value, b : Value) -> Bool raise {
  match (a, b) {
    (Fix(x), Fix(y)) => x < y
    _ => num_lt(a, b)
  }
}

///|
/// Lisp `(+ a b)` on numbers.
fn ratmac__add(a : Value, b : Value) -> Value raise {
  num_add(a, b)
}

///|
/// Lisp `(- a b)` on numbers.
fn ratmac__sub(a : Value, b : Value) -> Value raise {
  num_sub(a, b)
}

///|
/// Lisp `(* a b)` on numbers.
fn ratmac__mul(a : Value, b : Value) -> Value raise {
  num_mul(a, b)
}

///|
/// `(member x l :test #'equal)` as a Bool.
fn ratmac__member_equal(x : Value, l : Value) -> Bool {
  member_equal(x, l).truthy()
}

///|
/// Bind several specials for the dynamic extent of F.
fn[T] ratmac__let(bs : Array[(Value, Value)], f : () -> T raise) -> T raise {
  with_specials(bs, f)
}
