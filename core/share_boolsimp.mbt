// Port of share/contrib/boolsimp/boolsimp.lisp (Robert Dodier, 2006):
// simplification and evaluation of Boolean and conditional expressions.
// The translator rule (def%tr mcond ...) is not ported: the Maxima to Lisp
// translator is not part of the port.

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
fn init_share_boolsimp() -> Unit raise {
  register_mspec(q_mcond, share_boolsimp__mcond)
  putprop(q_mcond, q_simp_mcond, q_operators) |> ignore
  putprop(q_p_mcond, q_simp_mcond, q_operators) |> ignore
  defun(
    q_parse_condition,
    args => share_boolsimp__parse_condition(arg(args, 0)),
    name="parse-condition",
  )
}
