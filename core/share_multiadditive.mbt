// Port of share/multiadditive/multiadditive.lisp (Barton Willis, 2006):
// the operator properties multiadditive, threadable, idempotent and
// involution (installed by multiadditive.mac via define_opproperty).

///|
/// When e is a mapatom, oper-apply would signal an error.
fn protected_oper_apply(e : Value, z : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    e
  } else {
    oper_apply(e, z)
  }
}

///|
fn multiadditive(e : Value) -> Value raise {
  if !d_subvarp(e).truthy() &&
    some(s => op_equalp(s, list1(q_mplus)).truthy(), margs(e)) {
    let op = mop(e)
    let mut args = margs(e)
    args = mapcar(
      s => if op_equalp(s, list1(q_mplus)).truthy() { margs(s) } else { list1(s) },
      args,
    )
    args = cartesian_product(args)
    args = mapcar(s => simplify(cons(list1(op), s)), args)
    reduce((a, b) => add(list2(a, b)), args)
  } else {
    e
  }
}

///|
/// ((op) bag) --> map(op bag).
fn threadable(e : Value) -> Value raise {
  let mut arg = margs(e)
  if length(arg) == 1 &&
    !d_subvarp(e).truthy() &&
    (mbagp(car(arg)).truthy() || op_equalp(car(arg), list1(q_d_set)).truthy()) {
    arg = car(arg)
    let fop = mop(e)
    let bop = mop(arg)
    cons(list1(bop), mapcar(s => mfuncall(fop, list1(s)), margs(arg)))
  } else {
    e
  }
}

///|
/// ((op) ((op) x)) --> ((op) x).
fn idempotent(e : Value) -> Value raise {
  if !d_subvarp(e).truthy() &&
    length(margs(e)) == 1 &&
    !d_mapatom(car(margs(e))).truthy() &&
    eq(mop(e), mop(car(margs(e)))) {
    car(margs(e))
  } else {
    e
  }
}

///|
/// ((op) ((op) x)) --> x.
fn involution(e : Value) -> Value raise {
  if !d_subvarp(e).truthy() &&
    length(margs(e)) == 1 &&
    !d_mapatom(car(margs(e))).truthy() &&
    eq(mop(e), mop(car(margs(e)))) &&
    length(margs(car(margs(e)))) == 1 {
    car(margs(car(margs(e))))
  } else {
    e
  }
}

///|
fn init_share_multiadditive() -> Unit raise {

}
