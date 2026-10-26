// Port of src/opers.lisp: the run-time half of the OPERS package -- the
// general-representation expression constructors ADD, SUB, MUL, DIV, POWER,
// NCMUL, NCPOWER, INV and friends. Each assumes simplified arguments unless
// its name ends in `_star` (Lisp `*`).

///|
fn add2(x : Value, y : Value) -> Value raise {
  if numberp(x) {
    if numberp(y) {
      num_add(x, y)
    } else if eq0(x) {
      y
    } else {
      simplifya(mk(q_mplus, [x, y]), t)
    }
  } else if eq0(y) {
    x
  } else {
    simplifya(mk(q_mplus, [x, y]), t)
  }
}

///|
fn add2_star(x : Value, y : Value) -> Value raise {
  if numberp(x) && numberp(y) {
    num_add(x, y)
  } else if eq0(x) {
    simplifya(y, Nil)
  } else if eq0(y) {
    simplifya(x, Nil)
  } else {
    simplifya(mk(q_mplus, [x, y]), Nil)
  }
}

///|
fn addn(terms : Value, simp_flag : Value) -> Value raise {
  if terms is Nil {
    Fix(0L)
  } else {
    simplifya(cons(list1(q_mplus), terms), simp_flag)
  }
}

///|
fn neg(x : Value) -> Value raise {
  if numberp(x) {
    num_neg(x)
  } else {
    with_special(q_d_negdistrib, t, () => simplifya(
      mk(q_mtimes, [Fix(-1L), x]),
      t,
    ))
  }
}

///|
fn sub(x : Value, y : Value) -> Value raise {
  if numberp(x) && numberp(y) {
    num_sub(x, y)
  } else if eq0(y) {
    x
  } else if eq0(x) {
    neg(y)
  } else {
    add2(x, neg(y))
  }
}

///|
fn sub_star(x : Value, y : Value) -> Value raise {
  if numberp(x) && numberp(y) {
    num_sub(x, y)
  } else if eq0(y) {
    x
  } else if eq0(x) {
    neg(y)
  } else {
    add2(simplifya(x, Nil), mul2(Fix(-1L), simplifya(y, Nil)))
  }
}

///|
fn mul2(x : Value, y : Value) -> Value raise {
  if numberp(x) && numberp(y) {
    num_mul(x, y)
  } else if eq1(x) {
    y
  } else if eq1(y) {
    x
  } else {
    simplifya(mk(q_mtimes, [x, y]), t)
  }
}

///|
fn mul2_star(x : Value, y : Value) -> Value raise {
  if numberp(x) && numberp(y) {
    num_mul(x, y)
  } else if eq1(x) {
    simplifya(y, Nil)
  } else if eq1(y) {
    simplifya(x, Nil)
  } else {
    simplifya(mk(q_mtimes, [x, y]), Nil)
  }
}

///|
fn mul3(x : Value, y : Value, z : Value) -> Value raise {
  if eq1(x) {
    mul2(y, z)
  } else if eq1(y) {
    mul2(x, z)
  } else if eq1(z) {
    mul2(x, y)
  } else {
    simplifya(mk(q_mtimes, [x, y, z]), t)
  }
}

///|
fn muln(factors : Value, simp_flag : Value) -> Value raise {
  match factors {
    Nil => Fix(1L)
    Cons(_) => simplifya(cons(list1(q_mtimes), factors), simp_flag)
    _ => factors
  }
}

///|
fn div(x : Value, y : Value) -> Value raise {
  if eq1(x) {
    inv(y)
  } else if floatp(x) && floatp(y) {
    num_div(x, y)
  } else if d_bfloatp(x).truthy() && d_bfloatp(y).truthy() {
    // Call BIGFLOATP to ensure that arguments have same precision.
    bcons(fpquotient(cdr(bigfloatp(x)), cdr(bigfloatp(y))))
  } else {
    mul2(x, inv(y))
  }
}

///|
fn div_star(x : Value, y : Value) -> Value raise {
  if eq1(x) {
    inv_star(y)
  } else if floatp(x) && floatp(y) {
    num_div(x, y)
  } else if d_bfloatp(x).truthy() && d_bfloatp(y).truthy() {
    bcons(fpquotient(cdr(bigfloatp(x)), cdr(bigfloatp(y))))
  } else {
    mul2(simplifya(x, Nil), inv_star(y))
  }
}

///|
fn ncmul2(x : Value, y : Value) -> Value raise {
  simplifya(mk(q_mnctimes, [x, y]), t)
}

///|
fn ncmuln(factors : Value, flag : Value) -> Value raise {
  simplifya(cons(list1(q_mnctimes), factors), flag)
}

///|
fn power(n_starbase : Value, power : Value) -> Value raise {
  if eq1(power) {
    n_starbase
  } else {
    simplifya(mk(q_mexpt, [n_starbase, power]), t)
  }
}

///|
fn power_star(n_starbase : Value, power : Value) -> Value raise {
  if eq1(power) {
    simplifya(n_starbase, Nil)
  } else {
    simplifya(mk(q_mexpt, [n_starbase, power]), Nil)
  }
}

///|
fn ncpower(x : Value, y : Value) -> Value raise {
  simplifya(mk(q_mncexpt, [x, y]), t)
}

///|
/// (ROOT X N) takes the Nth root of X.
fn root(x : Value, n : Value) -> Value raise {
  if eq0(x) {
    Fix(0L)
  } else if eq1(x) {
    Fix(1L)
  } else {
    simplifya(mk(q_mexpt, [x, mk_simp(q_rat, [Fix(1L), n])]), t)
  }
}

///|
/// (PORM flag expr) is +expr if flag is true, and -expr otherwise.
fn porm(s : Value, x : Value) -> Value raise {
  if s.truthy() {
    x
  } else {
    neg(x)
  }
}

///|
fn morp(s : Value, x : Value) -> Value raise {
  if s.truthy() {
    neg(x)
  } else {
    x
  }
}
