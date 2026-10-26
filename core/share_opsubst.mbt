// Port of share/contrib/opsubst.lisp (Barton Willis, 2006).
//
// The function 'opsubst' is similar to the function 'subst', except that
// 'opsubst' only makes substitutions for the operators in an expression:
//
//  opsubst(f,g,e) --> When 'f' is an operator in the expression e,
//                     substitute 'g' for 'f' in the expression 'e'.
//  opsubst(g=f,e) --> opsubst(f,g,e).
//  opsubst([],e) --> e.
//  opsubst([g1=f1, g2=f2, ..., gn=fn],e) -->
//                     opsubst([g2=f2,...,gn=fn], opsubst(f1=f1, e)).
//
// To determine the operator, 'opsubst' sets 'inflag' to true: it
// substitutes for the internal, not the displayed, operator.

///|
/// Applies op to args and simplifies the result. It does not evaluate
/// args, and handles subscripted operators.
fn my_take(op : Value, args : Value) -> Value raise {
  simplify(
    if consp(op) && member(q_array, car(op)).truthy() {
      cons(list1(q_mqapply), cons(op, args))
    } else {
      cons(list1(op), args)
    },
  )
}

///|
fn d_opsubst(q : Value) -> Value raise {
  if length(q) == 3 {
    op_subst(first(q), second(q), third(q))
  } else if length(q) == 2 {
    let mut e = second(q)
    let q = if d_listp(first(q)).truthy() {
      margs(first(q))
    } else {
      list1(first(q))
    }
    for qi in q.iter() {
      if op_equalp(qi, list1(q_mequal)).truthy() {
        e = op_subst(d_rhs(qi), d_lhs(qi), e)
      } else {
        merror(
          Str("Expected an expression of the form `a = b'; instead found ~:M"),
          list1(qi),
        )
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
/// If prd(e) evaluates to true, do the substitution opsubst(id, e). The
/// first argument should be an equation of the form symbol = symbol |
/// lambda form or a list of such equations.
fn d_opsubstif(id : Value, prd : Value, e : Value) -> Value raise {
  let id = if d_listp(id).truthy() { margs(id) } else { list1(id) }
  let mut e = e
  for qi in id.iter() {
    if op_equalp(qi, list1(q_mequal)).truthy() {
      e = op_subst_if(
        verbify_string(d_rhs(qi)),
        verbify_string(d_lhs(qi)),
        prd,
        e,
      )
    } else {
      merror(
        Str("Expected an expression of the form `a = b'; instead found ~:M"),
        list1(qi),
      )
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
/// Return a list of all the arguments to the operator 'op.' Each argument
/// is a list (what 'args' would return).
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
