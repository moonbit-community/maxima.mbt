// Port of share/contrib/boolsimp/boolsimp.lisp (Robert Dodier, 2006):
// simplification and evaluation of Boolean and conditional expressions.

///|
/// (defmspec mcond (x) ...): evaluation of conditional expressions.
///
/// If any B evaluates to T, then append B and G to the list of evaluated
/// arguments, and ignore any remaining arguments. If any B evaluates to
/// NIL, then ignore B and G, and continue processing arguments. Otherwise,
/// append B and G to the list of evaluated arguments, and continue.
///
/// If the first element of the list of evaluated arguments is T, return
/// the second element. Otherwise, construct a new conditional expression
/// from the evaluated arguments.
fn share_boolsimp__mcond(x : Value) -> Value raise {
  let op = car(x)
  let mut args = cdr(x)
  let conditions = Collector::new()
  let consequences = Collector::new()
  while length(args) > 0 {
    let b = car(args)
    let g = cadr(args)
    let v = mevalp(b)
    if eq(v, t) {
      conditions.add(v)
      consequences.add(g)
      args = Nil
    } else if v is Nil {
      ()
    } else {
      conditions.add(v)
      consequences.add(g)
    }
    args = cddr(args)
  }
  let conditions = conditions.result()
  let consequences = consequences.result()
  if eq(car(conditions), t) {
    meval(car(consequences))
  } else {
    let consequences = mapcar(
      e => mcond_eval_symbols(q_meval1, e),
      consequences,
    )
    // Burn off SIMP flag, if any, when constructing the new CAAR.
    let acc = Collector::new()
    let mut pc = conditions
    let mut pg = consequences
    while pc is Cons(_) && pg is Cons(_) {
      acc.add(car(pc))
      acc.add(car(pg))
      pc = cdr(pc)
      pg = cdr(pg)
    }
    cons(list1(car(op)), acc.result())
  }
}

///|
/// Simplification of conditional expressions.
///
/// If any B simplifies to T or $TRUE, then append B and G to the list of
/// simplified arguments, and ignore any remaining arguments. If any B
/// simplifies to NIL or $FALSE, then ignore B and G, and continue.
/// Otherwise, append B and G to the list of simplified arguments.
///
/// If there are no arguments remaining return $FALSE. If the first element
/// of the list of simplified arguments is T or $TRUE, return the second
/// element. Otherwise, construct a new conditional expression from the
/// simplified arguments.
fn simp_mcond_shorten(x : Value, z : Value) -> Value raise {
  let op = car(x)
  let mut args = cdr(x)
  let args_simplified = Collector::new()
  while length(args) > 0 {
    let b = maybe_simplifya(car(args), z)
    let g = cadr(args)
    if b is Nil || eq(b, q_d_false) {
      ()
    } else if eq(b, t) || eq(b, q_d_true) {
      args_simplified.add(b)
      args_simplified.add(maybe_simplifya(g, z))
      args = Nil
    } else {
      args_simplified.add(b)
      args_simplified.add(maybe_simplifya(g, z))
    }
    args = cddr(args)
  }
  let args_simplified = args_simplified.result()
  if args_simplified is Nil {
    Nil
  } else if eq(car(args_simplified), t) {
    cadr(args_simplified)
  } else {
    // Indicate that the return value has been simplified.
    cons(list2(car(op), q_simp), args_simplified)
  }
}

///|
fn simp_mcond(x : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  simp_mcond_shorten(x, z)
}

///|
/// Redefinition of PARSE-CONDITION (src/nparse.lisp): append NIL instead
/// of $FALSE when input is like "if foo then bar" (without else).
fn share_boolsimp__parse_condition(op : Value) -> Value raise {
  let c = parse(rpos(op), rbp(op))
  let then_ = if eq(first_c(), q_d_then) {
    parse(q_d_any, rbp(pop_c()))
  } else {
    mread_synerr(Str("Missing `then'"), Nil)
  }
  let fc = first_c()
  let else_ = if eq(fc, q_d_else) {
    list2(t, parse(q_d_any, rbp(pop_c())))
  } else if eq(fc, q_d_elseif) {
    funcall(q_parse_condition, [pop_c()])
  } else {
    list2(t, Nil)
  }
  list_star([c, then_, else_])
}

///|
/// (def%tr mcond (form) ...): the translation of conditional expressions;
/// an unknown condition gives an unevaluated MCOND.
fn share_boolsimp__tr_mcond(form : Value) -> Value raise {
  let q_unevaluated_mcond = sym("unevaluated-mcond")
  let q_translated_mcond = sym("translated-mcond")
  let g = tr_gensym()
  let mut nl : Value = Nil
  let mut mode : Value = Nil
  // build up list nl from l; nl is in reverse order from l; each two items
  // in nl are a body followed by a corresponding condition
  let mut l = cdr(form)
  while l is Cons(_) {
    // Optimize the else-if case: if we're at the else case at the end and
    // the body is just another conditional, then we just continue directly
    // with the clauses of the inner conditional instead of nesting.
    if cddr(l) is Nil &&
      eq(car(l), t) &&
      consp(cadr(l)) &&
      eq(car(car(car(cdr(l)))), q_mcond) {
      l = cdr(cadr(l))
    }
    let (pr, br) = with_special(q_wrap_a_pred, q_mcond, () => {
      let p = translate_predicate(car(l))
      let b = translate(cadr(l))
      (p, b)
    })
    let pred_mode = car(pr)
    let pred_tr = cdr(pr)
    let body_tr = cdr(br)
    mode = n_starunion_mode(mode, car(br))
    // a clause in the original mcond is translated into two (body,
    // condition) pairs in nl: one to execute if the original condition is
    // true, and one to add a clause to the unevaluated mcond if the
    // condition is unknown
    let c = if eq(pred_mode, q_d_boolean) { pred_tr } else { g }
    nl = list_star([
      list3(
        q_setq,
        q_unevaluated_mcond,
        list3(
          q_append,
          q_unevaluated_mcond,
          list3(
            q_list,
            c,
            list2(q_mcond_eval_symbols_tr, list2(q_quote, cadr(l))),
          ),
        ),
      ),
      c,
      list3(q_return_from, q_translated_mcond, body_tr),
      list3(
        q_and,
        if eq(pred_mode, q_d_boolean) {
          pred_tr
        } else {
          list3(q_eq, t, list3(q_setq, g, pred_tr))
        },
        list2(q_null, q_unevaluated_mcond),
      ),
      nl,
    ])
    l = cddr(l)
  }
  // We leave off the final clause if the condition is true and the
  // consequent is false.
  if eq(t, cadr(nl)) && car(nl) is Nil {
    nl = cddr(nl)
  }
  // build up a block in the translated routine; each (body, condition)
  // pair in nl is translated into an "if"
  let mut form : Value = Nil
  let mut l = nl
  while l is Cons(_) {
    let clause_body = if !atom(car(l)) && cdr(l).truthy() && eq(caar(l), q_progn) {
      cdar(l)
    } else if equal(car(l), cadr(l)) && atom(car(l)) {
      Nil
    } else {
      list1(car(l))
    }
    form = cons(cons(q_if, cons(cadr(l), clause_body)), form)
    l = cddr(l)
  }
  let block = list_star([
    q_block,
    q_translated_mcond,
    append(form, list1(list3(q_cons, list2(q_quote, list1(q_mcond)), q_unevaluated_mcond))),
  ])
  if among(g, form).truthy() {
    cons(q_d_any, list3(q_let, list2(g, q_unevaluated_mcond), block))
  } else {
    cons(mode, list3(q_let, list1(q_unevaluated_mcond), block))
  }
}

///|
fn init_share_boolsimp() -> Unit raise {
  register_mspec(q_mcond, share_boolsimp__mcond)
  putprop(q_mcond, q_simp_mcond, q_operators) |> ignore
  putprop(q_p_mcond, q_simp_mcond, q_operators) |> ignore
  defun(
    q_parse_condition,
    args => share_boolsimp__parse_condition(arg(args, 0)),
    name="parse-condition",
  )
  transl__deftr(q_mcond, share_boolsimp__tr_mcond)
}
