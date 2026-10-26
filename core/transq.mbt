// Port of src/transq.lisp: compile-time macros for TRANSLATEd code.
//
// The macros (DEF-MTRVAR, M-TLAMBDA, M-TLAMBDA&, SET-VALS-INTO-LIST) are
// declared functions implemented as macro EXPANDERS: they take the
// unevaluated argument forms and return the expansion, for the Lisp
// evaluator. The M-TLAMBDA&ENV macros have destructuring lambda lists and
// are not declared: their expansion is `transq__m_tlambda_ampenv`.

///|
/// DEF-MTRVAR expander: `(def-mtrvar v a &optional priority)`.
fn def_mtrvar(v : Value, a : Value, priority? : Value = Fix(1L)) -> Value raise {
  ignore(priority)
  // ignored variable around for TRANSLATED files pre 3:03pm Thursday, 11
  // March 1982 -gjc
  list3(
    q_progn,
    list2(q_declare_top, list2(q_special, v)),
    list3(
      q_if,
      list3(
        q_or,
        list2(q_not, list2(q_boundp, transl__quote(v))),
        // a SYMBOL SET to ITSELF is considered to be UNBOUND for our
        // purposes in Macsyma.
        list3(q_eq, v, transl__quote(v)),
      ),
      list3(q_setq, v, a),
    ),
  )
}

///|
/// SKIP-DECLARE-EXPRS
fn skip_declare_exprs(l : Value) -> Value raise {
  let mut l = l
  while consp(car(l)) && eq(caar(l), q_declare) {
    l = cdr(l)
  }
  l
}

///|
/// VANILLA-LAMBDA
fn vanilla_lambda(bvl : Value, body : Value) -> Value raise {
  cons(
    q_lambda,
    cons(bvl, cons(cons(q_declare, list1(cons(q_special, bvl))), skip_declare_exprs(body))),
  )
}

///|
/// REST-ARG-LAMBDA
fn rest_arg_lambda(bvl : Value, body : Value) -> Value raise {
  let req_args = butlast(bvl)
  let rest_arg = car(last(bvl))
  cons(
    q_lambda,
    cons(
      append(req_args, list2(q_n_amprest, rest_arg)),
      cons(
        list2(q_declare, cons(q_special, bvl)),
        cons(
          list3(q_push, transl__quote(list1(q_mlist)), rest_arg),
          skip_declare_exprs(body),
        ),
      ),
    ),
  )
}

///|
/// LAMBDA-WITH-FREE-VARS
fn lambda_with_free_vars(
  bvl : Value,
  fvl : Value,
  cfvl : Value,
  lambda_header : Value,
  body : Value,
) -> Value raise {
  let lfvl = set_difference(fvl, cfvl)
  let lexicals = mapcar(x => gensym(prefix=symbol_name(x)), cfvl)
  let symevals = mapcar(x => list2(q_maybe_msymeval, transl__quote(x)), lfvl)
  let pairs = fn(a : Value, b : Value) -> Value raise {
    let c = Collector::new()
    let mut a = a
    let mut b = b
    while a is Cons(_) && b is Cons(_) {
      c.add(list2(car(a), car(b)))
      a = cdr(a)
      b = cdr(b)
    }
    c.result()
  }
  list3(
    q_let,
    pairs(lexicals, cfvl),
    funcall(lambda_header, [
      bvl,
      list1(
        cons(
          q_let,
          cons(
            append(pairs(cfvl, lexicals), pairs(lfvl, symevals)),
            cons(list2(q_declare, cons(q_special, append(cfvl, lfvl))), body),
          ),
        ),
      ),
    ]),
  )
}

///|
/// MAKE-TLAMBDA
fn make_tlambda(
  bvl : Value,
  fvl : Value,
  cfvl : Value,
  rest_p : Value,
  body : Value,
) -> Value raise {
  let lambda_header = if rest_p.truthy() {
    q_rest_arg_lambda
  } else {
    q_vanilla_lambda
  }
  if fvl is Nil {
    funcall(lambda_header, [bvl, body])
  } else {
    lambda_with_free_vars(bvl, fvl, cfvl, lambda_header, body)
  }
}

///|
/// M-TLAMBDA expander: lambda([u,...],...) where any free unquoted
/// variable in the body is either unbound or globally bound or locally
/// bound in some non-enclosing block.
fn m_tlambda(bvl : Value, body : Value) -> Value raise {
  make_tlambda(bvl, Nil, Nil, Nil, body)
}

///|
/// M-TLAMBDA& expander: lambda([u,...,[v]],...) with the same condition as
/// above.
fn m_tlambda_amp(bvl : Value, body : Value) -> Value raise {
  make_tlambda(bvl, Nil, Nil, t, body)
}

///|
/// M-TLAMBDA&ENV / M-TLAMBDA&ENV& expander: `((bvl fvl cfvl) . body)`:
/// lambda([u,...],...) with free unquoted variables in the body which have
/// a local binding in some enclosing block, but no global one. fvl is a
/// list of all free vars. cfvl is a list of the free vars to capture.
fn transq__m_tlambda_ampenv(spec : Value, body : Value, rest_p : Value) -> Value raise {
  make_tlambda(car(spec), cadr(spec), caddr(spec), rest_p, body)
}

///|
/// SET-VALS-INTO-LIST expander: `(set-vals-into-list argl var)`.
fn set_vals_into_list(argl : Value, var_ : Value) -> Value raise {
  let mut j = 0
  let mut argl = argl
  let mut l : Value = Nil
  while argl is Cons(_) {
    l = cons(list3(q_setf, list3(q_nth, int(j), var_), car(argl)), l)
    j += 1
    argl = cdr(argl)
  }
  cons(q_progn, l)
}
