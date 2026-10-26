// Port of share/algebra/charsets/charsets_flatten.lisp (Barton Willis,
// 2002): charsets_flatten, a clone of Macsyma's flatten, and
// charsets_every.

///|
/// Return the operator and argument of the expression e.
fn get_op_and_arg(e : Value) -> (Value, Value) raise {
  if d_atom(e).truthy() || d_subvarp(e).truthy() {
    (Nil, Nil)
  } else if consp(car(e)) && d_subvarp(cadr(e)).truthy() {
    (list2(car(e), cadr(e)), cddr(e))
  } else {
    (car(e), cdr(e))
  }
}

///|
fn d_charsets_flatten(e : Value) -> Value raise {
  let e = ratdisrep(e)
  if d_atom(e).truthy() ||
    d_subvarp(e).truthy() ||
    member_equal(d_inpart(list2(e, Fix(0L))), list2(Str("^"), Str("="))).truthy() {
    e
  } else {
    let (op, args) = get_op_and_arg(e)
    let mut e = mapcar(x => flatten_op(x, op), args)
    e = reduce((a, b) => append(a, b), e)
    if consp(car(op)) && eq(caar(op), q_mqapply) {
      append(op, e)
    } else {
      cons(op, e)
    }
  }
}

///|
/// Returns T if X and Y (returned by GET-OP-AND-ARG) are the same
/// operator. ALIKE1 is used in order to ignore things like SIMP flags.
fn same_op_p(x : Value, y : Value) -> Value raise {
  alike1(
    if atom(car(x)) { list1(x) } else { x },
    if atom(car(y)) { list1(y) } else { y },
  )
}

///|
fn flatten_op(e : Value, op : Value) -> Value raise {
  let (e_op, e_arg) = get_op_and_arg(e)
  if same_op_p(e_op, op).truthy() {
    mapcan(x => flatten_op(x, op), e_arg)
  } else {
    list1(e)
  }
}

///|
/// Works like the every function in lisp: takes a list, or a positive
/// number of arguments, returning true if all its arguments are not false.
fn d_charsets_every(args : Value) -> Value raise {
  let n = length(args)
  if n == 0 {
    merr("Every must have at least 1 argument", [])
  } else if n == 1 {
    let args = car(args)
    if d_listp(args).truthy() && num_gt(d_length(args), Fix(0L)) {
      lbool(every(x => x.truthy(), margs(args)))
    } else if d_listp(args).truthy() && num_eq(d_length(args), Fix(0L)) {
      Nil
    } else {
      args
    }
  } else {
    lbool(every(x => x.truthy(), args))
  }
}

///|
fn init_share_charsets_flatten() -> Unit raise {
  d_put(q_d_charsets_flatten, Fix(1L), q_d_version) |> ignore
}
