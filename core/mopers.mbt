// Port of src/mopers.lisp: the compile-time half of the OPERS package, an
// interface to the Maxima general representation simplifier.
//
// glue.mbt provides the ergonomic versions used by translated code:
// take/take_star/ftake/ftake_star/fapply/fapply_star (with MoonBit arrays),
// inv/inv_star, eq0/eq1 (returning Bool), addn_/muln_/ncmul_.  The
// declared macro functions below are the Lisp-value equivalents (taking
// `&rest` arguments as Lisp lists), implemented in terms of the same
// functions.
//
// DEFGRAD (a body macro) is expanded at its call sites as
//   set(q_ear_defgrad_syms, cons(q_p_foo, symval(q_ear_defgrad_syms)))
//   setf_get(q_p_foo, q_grad, cons(arguments, list([deriv1, deriv2, ...])))
// in the defining file's init function; PROCESS-DEFGRAD later simplifies
// the derivatives.

///|
/// `(=0 x)` = `(equal x 0)`
fn n_eq0(x : Value) -> Value raise {
  lbool(eq0(x))
}

///|
/// `(=1 x)` = `(equal x 1)`
fn n_eq1(x : Value) -> Value raise {
  lbool(eq1(x))
}

///|
/// Addition -- call ADD with simplified operands, ADD* with unsimplified
/// operands.
fn add(terms : Value) -> Value raise {
  if length(terms) == 2 {
    add2(car(terms), cadr(terms))
  } else {
    addn(terms, t)
  }
}

///|
fn add_star(terms : Value) -> Value raise {
  if length(terms) == 2 {
    add2_star(car(terms), cadr(terms))
  } else {
    addn(terms, Nil)
  }
}

///|
/// Multiplication -- call MUL or NCMUL with simplified operands, MUL* or
/// NCMUL* with unsimplified operands.
fn mul(factors : Value) -> Value raise {
  match length(factors) {
    2 => mul2(car(factors), cadr(factors))
    3 => mul3(car(factors), cadr(factors), caddr(factors))
    _ => muln(factors, t)
  }
}

///|
fn mul_star(factors : Value) -> Value raise {
  if length(factors) == 2 {
    mul2_star(car(factors), cadr(factors))
  } else {
    muln(factors, Nil)
  }
}

///|
/// `(inv x)` = `(power x -1)`
fn inv_(x : Value) -> Value raise {
  inv(x)
}

///|
/// `(inv* x)` = `(power* x -1)`
fn inv_star_(x : Value) -> Value raise {
  inv_star(x)
}

///|
/// `(ncmul &rest factors)`
fn ncmul(factors : Value) -> Value raise {
  if length(factors) == 2 {
    ncmul2(car(factors), cadr(factors))
  } else {
    ncmuln(factors, t)
  }
}

///|
/// (TAKE '(%TAN) X) = tan(x): `(simplifya (list operator args...) t)`
fn take_(operator : Value, args : Value) -> Value raise {
  simplifya(cons(operator, args), t)
}

///|
/// take* does not assume that the arguments are simplified.
fn take_star_(operator : Value, args : Value) -> Value raise {
  simplifya(cons(operator, args), Nil)
}

///|
/// Like TAKE, but you only need to specify the name:
/// (ftake name x y) => (take '(name) x y).  The name should be the noun
/// form, like %foo.
fn ftake_(name : Value, args : Value) -> Value raise {
  simplifya(cons(list1(name), args), t)
}

///|
fn ftake_star_(name : Value, args : Value) -> Value raise {
  simplifya(cons(list1(name), args), Nil)
}

///|
/// Apply a function f to a list of its arguments 'args' and simplify the
/// result.  Assume that the list args is simplified.
fn fapply_(f : Value, args : Value) -> Value raise {
  simplifya(cons(list1(f), args), t)
}

///|
/// Same as fapply, but don't assume that the list of arguments is
/// simplified.
fn fapply_star_(f : Value, args : Value) -> Value raise {
  simplifya(cons(list1(f), args), Nil)
}

///|
fn simplify(x : Value) -> Value raise {
  simplifya(x, Nil)
}

// A hand-made DEFSTRUCT for dealing with the Maxima MDO structure.  Used
// in GRAM, etc. for storing/retrieving from DO structures.

///|
fn make_mdo() -> Value raise {
  list([list1(q_mdo), Nil, Nil, Nil, Nil, Nil, Nil, Nil])
}

///|
fn mdo_op(x : Value) -> Value raise {
  car(car(x))
}

///|
fn mdo_for(x : Value) -> Value raise {
  second(x)
}

///|
fn mdo_from(x : Value) -> Value raise {
  third(x)
}

///|
fn mdo_step(x : Value) -> Value raise {
  fourth(x)
}

///|
fn mdo_next(x : Value) -> Value raise {
  fifth(x)
}

///|
fn mdo_thru(x : Value) -> Value raise {
  nth(5, x)
}

///|
fn mdo_unless(x : Value) -> Value raise {
  nth(6, x)
}

///|
fn mdo_body(x : Value) -> Value raise {
  nth(7, x)
}

///|
/// See if the arg A exists somewhere in the expression G.
fn check_defgrad(a : Value, g : Value) -> Value raise {
  if atom(g) {
    lbool(eq(a, g))
  } else {
    // (some #'identity (mapcar ... g))
    let rs = mapcar(g => check_defgrad(a, g), g)
    some_value(x => x, rs)
  }
}

///|
/// When DEFGRAD uses #$$ to define derivatives, we MUST call MEVAL* on
/// them to get them simplified appropriately.  It's ok to call MEVAL* if we
/// didn't use #$$.
fn process_defgrad() -> Value raise {
  for sym_ in symval(q_ear_defgrad_syms).iter() {
    let grad = get(sym_, q_grad)
    let args = car(grad)
    let glist = cdr(grad)
    setf_get(sym_, q_grad, cons(args, mapcar(g => meval_star(g), glist)))
    |> ignore
  }
  Nil
}

///|
fn init_mopers() -> Unit raise {
  macsyma_module(sym("mopers"), list1(q_macro)) |> ignore
}
