// Port of src/sqrtdenest.lisp: denest an expression containing square
// roots of square roots.
//
// This implementation uses the same algorithm as the maxima language
// SQRTDENEST in share package sqdnst.mac.  It only handles simple cases.
//
// Reference: Jeffrey, David J. and Rich, Albert D. (1999), Simplifying
// Square Roots of Square Roots by Denesting.

///|
/// Denest square roots in expression e
fn d_sqrtdenest(e : Value) -> Value raise {
  sqrtdenest1(e)
}

///|
/// Denest square roots in expression e
fn sqrtdenest1(e : Value) -> Value raise {
  if mapatom(e).truthy() {
    e
  } else if eq(mop(e), q_mexpt) {
    sqrtdenest2(e)
  } else {
    cons(list1(mop(e)), mapcar(x => sqrtdenest1(x), rest(e)))
  }
}

///|
/// Denest square roots in maxima expression e of form a^b.
///
/// Theorem 4.12: Let X,Y real with X > Y > 0
/// sqrt(X +/- Y) = sqrt(X/2+sqrt(X^2-Y^2)/2) +/- sqrt(X/2-sqrt(X^2-Y^2)/2)
///
/// Apply this by testing discriminant D = sqrt(1-(Y/X)^2)
///   If $numberp(D) then theorem 4.12 denests the square-root as
///   sqrt(X +/- Y) =  sqrt(X*(1+D)/2) +/- *sqrt(X*(1-D)/2)
fn sqrtdenest2(e : Value) -> Value raise {
  let a = simplify(sqrtdenest1(second(e)))
  let b = simplify(sqrtdenest1(third(e)))
  let mut x : Value = Nil
  let mut y : Value = Nil
  let mut d : Value = Nil
  if d_evenp(d_denom(b)).truthy() &&
    !mapatom(a).truthy() &&
    eq(mop(a), q_mplus) &&
    {
      // maximum of args(a)
      x = simplify(cons(list1(q_d_max), rest(a)))
      // a-x
      y = sub(a, x)
      // sqrt(1-(y/x)^2)
      d = root(sub(Fix(1L), power(div(y, x), Fix(2L))), Fix(2L))
      d_numberp(d).truthy()
    } {
    // (sqrt(x*(1+D)/2)+signum(y)*sqrt(x*(1-D)/2))^(2*b)
    let half = symval(q_n1_sl_sl2)
    power(
      add2(
        root(mul3(half, x, add2(Fix(1L), d)), Fix(2L)),
        mul2(
          take(list1(q_p_signum), [y]),
          root(mul3(half, x, sub(Fix(1L), d)), Fix(2L)),
        ),
      ),
      mul2(Fix(2L), b),
    )
  } else {
    // Didn't denest at this level, but may have at a lower level.
    power(a, b)
  }
}

///|
fn init_sqrtdenest() -> Unit raise {
  ()
}
