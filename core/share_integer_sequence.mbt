// Port of share/integer_sequence/integer_sequence.lisp (Barton Willis,
// 2008): the dot-dot operator a .. b and a .. h .. b generating the terms
// of an arithmetic sequence.

///|
fn simp_integer_sequence(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let mut e = cdr(e)
  let i = if e is Cons(_) {
    let v = car(e)
    e = cdr(e)
    simpcheck(v, z)
  } else {
    merr("The '..' operator needs 2 or 3 arguments, not 0", [])
  }
  let j = if e is Cons(_) {
    let v = car(e)
    e = cdr(e)
    simpcheck(v, z)
  } else {
    merr("The '..' operator needs 2 or 3 arguments, not 1", [])
  }
  let k = if e is Cons(_) {
    let v = car(e)
    e = cdr(e)
    simpcheck(v, z)
  } else {
    Nil
  }
  if e is Cons(_) {
    merr("The '..' operator needs 3 or fewer arguments", []) |> ignore
  }
  let (lo, hi, h) = if k.truthy() { (i, k, j) } else { (i, j, Fix(1L)) }
  if zerop1(h).truthy() {
    merr("The step argument to '..' must be nonzero", []) |> ignore
  }
  let sgn = if like(hi, lo).truthy() { q_d_zero } else { csign(sub(hi, lo)) }
  let sgn_h = csign(h)
  let mut n : Value = if eq(sgn, q_d_zero) {
    Fix(0L)
  } else {
    take(list1(q_d_floor), [div(sub(hi, lo), h)])
  }
  if integerp(n) &&
    (eq(sgn_h, q_d_neg) || eq(sgn_h, q_d_pos) || eq(sgn_h, q_d_pn)) {
    let mut acc : Value = Nil
    while num_ge(n, Fix(0L)) {
      acc = cons(add(list2(lo, mul(list2(n, h)))), acc)
      n = num_sub(n, Fix(1L))
    }
    simplify(cons(list1(q_mlist), acc))
  } else if (eq(q_d_neg, sgn) && eq(q_d_pos, sgn_h)) ||
    (eq(q_d_pos, sgn) && eq(q_d_neg, sgn_h)) {
    simplify(list1(list1(q_mlist)))
  } else if !k.truthy() {
    list3(list2(q_d_op_dot_dot, q_simp), i, j)
  } else if eql(Fix(1L), j) {
    // a .. 1 .. b == a .. b
    list3(list2(q_d_op_dot_dot, q_simp), i, k)
  } else {
    list4(list2(q_d_op_dot_dot, q_simp), i, j, k)
  }
}

///|
fn init_share_integer_sequence() -> Unit raise {
  // These binding powers make a .. b op c == a .. (b op c), where op = +,
  // -, *, /, or ^.
  d_nary(Str(".."), bp=Fix(80L)) |> ignore
  putprop(q_d_op_dot_dot, q_simp_integer_sequence, q_operators) |> ignore
}
