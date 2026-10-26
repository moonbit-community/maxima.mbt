// Port of share/contrib/opsubst.lisp (Barton Willis, 2006): opsubst,
// opsubstif, gatherargs and gatherops -- substitution for the operators of
// an expression.

///|
/// Applies op to args and simplifies the result; handles subscripted
/// operators.
fn my_take(op : Value, args : Value) -> Value raise {
  simplify(
    if consp(op) && memq(q_array, car(op)).truthy() {
      cons(list1(q_mqapply), cons(op, args))
    } else {
      cons(list1(op), args)
    },
  )
}

///|
fn d_opsubst(q : Value) -> Value raise {
  let n = length(q)
  if n == 3 {
    op_subst(car(q), cadr(q), caddr(q))
  } else if n == 2 {
    let mut e = cadr(q)
    let qs = if d_listp(car(q)).truthy() { margs(car(q)) } else { list1(car(q)) }
    for qi in qs.iter() {
      if op_equalp(qi, list1(q_mequal)).truthy() {
        e = op_subst(d_rhs(qi), d_lhs(qi), e)
      } else {
        merr("Expected an expression of the form `a = b'; instead found ~:M", [
          qi,
        ])
        |> ignore
      }
    }
    e
  } else {
    wna_err(q_d_opsubst)
  }
}

///|
/// If op is a string, verbify it; otherwise, return op.
fn verbify_string(op : Value) -> Value raise {
  if stringp(op) {
    d_verbify(op)
  } else {
    op
  }
}

///|
/// If op is a symbol, verbify it; otherwise, return op.
fn safe_verbify(op : Value) -> Value raise {
  if symbolp(op) {
    d_verbify(op)
  } else {
    op
  }
}

///|
fn op_subst(f : Value, g : Value, e : Value) -> Value raise {
  let f = verbify_string(f)
  let g = verbify_string(g)
  with_special(q_d_inflag, t, () => if d_mapatom(e).truthy() {
    e
  } else {
    my_take(
      if like(safe_verbify(g), safe_verbify(mop(e))).truthy() {
        f
      } else {
        mop(e)
      },
      mapcar(s => op_subst(f, g, s), margs(d_args(e))),
    )
  })
}

///|
/// If prd(e) evaluates to true, do the substitution opsubst(id, e).
fn d_opsubstif(id : Value, prd : Value, e : Value) -> Value raise {
  let ids = if d_listp(id).truthy() { margs(id) } else { list1(id) }
  let mut e = e
  for qi in ids.iter() {
    if op_equalp(qi, list1(q_mequal)).truthy() {
      e = op_subst_if(
        verbify_string(d_rhs(qi)),
        verbify_string(d_lhs(qi)),
        prd,
        e,
      )
    } else {
      merr("Expected an expression of the form `a = b'; instead found ~:M", [
        qi,
      ])
      |> ignore
    }
  }
  e
}

///|
fn op_subst_if(fn_ : Value, fo : Value, prd : Value, e : Value) -> Value raise {
  with_specials([(q_d_inflag, t), (q_d_prederror, Nil)], () => if d_mapatom(e).truthy() {
    e
  } else {
    my_take(
      if like(safe_verbify(fo), safe_verbify(mop(e))).truthy() &&
        eq(t, mevalp(mfuncall(prd, list1(d_args(e))))) {
        fn_
      } else {
        mop(e)
      },
      mapcar(s => op_subst_if(fn_, fo, prd, s), margs(d_args(e))),
    )
  })
}

///|
/// Return a list of all the arguments to the operator 'op'.
fn d_gatherargs(e : Value, op : Value) -> Value raise {
  cons(list1(q_mlist), gatherargs(e, op))
}

///|
fn gatherargs(e : Value, op : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    Nil
  } else {
    append(
      if op_equalp(e, list3(op, d_nounify(op), d_verbify(op))).truthy() {
        list1(cons(list1(q_mlist), margs(e)))
      } else {
        Nil
      },
      mapcan(s => gatherargs(s, op), margs(e)),
    )
  }
}

///|
fn d_gatherops(e : Value) -> Value raise {
  d_setify(cons(list1(q_mlist), gatherops(e)))
}

///|
fn gatherops(e : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    Nil
  } else {
    cons(d_op(e), mapcan(s => gatherops(s), margs(e)))
  }
}

///|
fn init_share_opsubst() -> Unit raise {

}
