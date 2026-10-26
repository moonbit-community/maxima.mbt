// Port of src/compar.lisp, part 1: contexts, boolean simplification and
// evaluation, assume/forget, and the asksign/sign entry points.
//
// SIGN, MINUS, ODDS and EVENS are set together by the sign code (SIGN1 and
// the SIGN-<OP> handlers) and must be kept mutually consistent. Model the
// expression whose sign was just computed as
//     (MINUS ? -1 : 1) * product(ODDS) * product(EVENS)^2,
// so that SIGN = (MINUS ? flip) sign(product(ODDS) * product(EVENS)^2).
// ASKSIGN1 questions the user about product(ODDS) * product(EVENS)^2 and then
// flips by MINUS.

// --- small helpers shared by the compar_*.mbt files --------------------------

///|
fn compar__in(x : Value, xs : Array[Value]) -> Bool {
  for y in xs {
    if eq(x, y) {
      return true
    }
  }
  false
}

///|
fn compar__cs() -> Bool {
  symval(q_ear_complexsign).truthy()
}

///|
fn compar__sign() -> Value {
  symval(q_sign)
}

///|
/// `(setq sign s minus m odds o evens e)`
fn compar__set4(s : Value, m : Value, o : Value, e : Value) -> Unit {
  set(q_sign, s) |> ignore
  set(q_minus, m) |> ignore
  set(q_odds, o) |> ignore
  set(q_evens, e) |> ignore
}

///|
/// `(let (sign minus odds evens) ...)`
fn[T] compar__with_signs(f : () -> T raise) -> T raise {
  with_specials([(q_sign, Nil), (q_minus, Nil), (q_odds, Nil), (q_evens, Nil)], f)
}

///|
/// `(unwind-protect body cleanup)` where the cleanup may itself raise.
fn compar__unwind(body : () -> Value raise, cleanup : () -> Unit raise) -> Value raise {
  let r : Result[Value, Error] = try Ok(body()) catch { e => Err(e) }
  cleanup()
  match r {
    Ok(v) => v
    Err(e) => raise e
  }
}

///|
fn compar__hide_prompt() -> Value {
  if symval(q_d_ask_hide_prompt).truthy() {
    q_noprint
  } else {
    Nil
  }
}

// -----------------------------------------------------------------------------

///|
fn lmul(l : Value) -> Value raise {
  simplify(cons(list1(q_mtimes), l))
}

///|
fn conssize(x : Value) -> Value raise {
  if atom(x) {
    return Fix(0L)
  }
  let mut sz = 1L
  for y in cdr(x).iter() {
    sz = sz + 1L + to_int64(conssize(y))
  }
  Fix(sz)
}

// Functions for creating, activating, manipulating, and killing contexts

///|
/// This "turns on" a context, making its facts visible.
fn d_activate(args : Value) -> Value raise {
  for c in args.iter() {
    if !symbolp(c) {
      nc_err(q_d_activate, c) |> ignore
    } else if memq(c, cdr(symval(q_d_activecontexts))).truthy() {
      ()
    } else if memq(c, cdr(symval(q_d_contexts))).truthy() {
      set(q_d_activecontexts, mcons(c, symval(q_d_activecontexts))) |> ignore
      activate(list1(c)) |> ignore
    } else {
      merr("activate: no such context ~:M", [c]) |> ignore
    }
  }
  q_d_done
}

///|
/// This "turns off" a context, keeping the facts, but making them invisible
fn d_deactivate(args : Value) -> Value raise {
  for c in args.iter() {
    if !symbolp(c) {
      nc_err(q_d_deactivate, c) |> ignore
    } else if memq(c, cdr(symval(q_d_contexts))).truthy() {
      set(q_d_activecontexts, d_delete(c, symval(q_d_activecontexts))) |> ignore
      deactivate(list1(c)) |> ignore
    } else {
      merr("deactivate: no such context ~:M", [c]) |> ignore
    }
  }
  q_d_done
}

///|
/// The list of the facts in the specified context (default: the current one).
fn d_facts(ctxt? : Value) -> Value raise {
  let ctxt = match ctxt {
    Some(c) => c
    None => symval(q_d_context)
  }
  if member(ctxt, cdr(symval(q_d_contexts))).truthy() {
    facts1(ctxt)
  } else {
    facts2(ctxt)
  }
}

///|
fn facts1(con : Value) -> Value raise {
  contextmark() |> ignore
  let mut nl : Value = Nil
  for d in zl_get(con, q_data).iter() {
    if visiblep(d).truthy() {
      nl = cons(intext(caar(d), cdar(d)), nl)
    }
  }
  cons(list1(q_mlist), nl)
}

///|
fn compar__among(x : Value, l : Value) -> Bool raise {
  if l is Nil {
    false
  } else if atom(l) || mnump(l).truthy() {
    alike1(x, l).truthy()
  } else if alike1(x, l).truthy() {
    true
  } else {
    for y in cdr(l).iter() {
      if compar__among(x, y) {
        return true
      }
    }
    false
  }
}

///|
/// Look up facts from the database which contain expr. expr can be a symbol
/// or a more general expression.
fn facts2(expr : Value) -> Value raise {
  let ans = []
  for f in cdr(d_facts(ctxt=symval(q_d_context))).iter() {
    if compar__among(expr, cadr(f)) || compar__among(expr, caddr(f)) {
      ans.push(f)
    }
  }
  cons(list1(q_mlist), list(ans))
}

///|
fn intext(rel : Value, body : Value) -> Value raise {
  let body = mapcar(x => doutern(x), body)
  if eq(q_kind, rel) {
    cons(list1(q_d_kind), body)
  } else if eq(q_par, rel) {
    cons(list1(q_d_par), body)
  } else if eq(q_mgrp, rel) {
    cons(list1(q_mgreaterp), body)
  } else if eq(q_mgqp, rel) {
    cons(list1(q_mgeqp), body)
  } else if eq(q_meqp, rel) {
    cons(list1(q_d_equal), body)
  } else if eq(q_mnqp, rel) {
    list2(list1(q_mnot), cons(list1(q_d_equal), body))
  } else {
    Nil
  }
}

///|
/// This function switches contexts, creating one if necessary.
fn asscontext(xx : Value, y : Value) -> Value raise {
  ignore(xx)
  if !symbolp(y) {
    nc_err(Str("context assignment"), y)
  } else if eq(y, q_d_global) {
    merr("context: ~M cannot be made the current context.", [y])
  } else if memq(y, symval(q_d_contexts)).truthy() {
    set(q_context, y) |> ignore
    set(q_d_context, y)
  } else {
    d_newcontext(list1(y))
  }
}

///|
/// This function actually creates a context whose subcontext is $GLOBAL.
/// It also switches contexts to the newly created one.
fn d_newcontext(args : Value) -> Value raise {
  if args is Nil {
    // make up a name and try again
    d_newcontext(list1(d_gensym(x=Str("context"))))
  } else if length(args) > 1 {
    merr("newcontext: found more than one argument.", [])
  } else {
    let x = car(args)
    if !symbolp(x) {
      nc_err(q_d_newcontext, x)
    } else if memq(x, symval(q_d_contexts)).truthy() {
      mtell(list([Str("newcontext: context ~M already exists."), x])) |> ignore
      Nil
    } else {
      set(q_d_contexts, mcons(x, symval(q_d_contexts))) |> ignore
      putprop_(x, list1(q_d_global), q_subc) |> ignore
      set(q_context, x) |> ignore
      set(q_d_context, x)
    }
  }
}

///|
/// This function creates a supercontext. With one argument, the current
/// context becomes its subcontext; with two, the second is the subcontext.
fn d_supcontext(x : Value) -> Value raise {
  if x is Nil {
    d_supcontext(list1(d_gensym(x=Str("context"))))
  } else if caddr(x).truthy() {
    merr("supcontext: found more than two arguments.", [])
  } else if !symbolp(car(x)) {
    nc_err(q_d_supcontext, car(x))
  } else if memq(car(x), symval(q_d_contexts)).truthy() {
    merr("supcontext: context ~M already exists.", [car(x)])
  } else if cadr(x).truthy() && memq(cadr(x), symval(q_d_contexts)) is Nil {
    merr("supcontext: no such context ~M", [cadr(x)])
  } else {
    set(q_d_contexts, mcons(car(x), symval(q_d_contexts))) |> ignore
    let sub = if cadr(x).truthy() { cadr(x) } else { symval(q_d_context) }
    putprop_(car(x), list1(sub), q_subc) |> ignore
    set(q_context, car(x)) |> ignore
    set(q_d_context, car(x))
  }
}

///|
/// This function kills a context or a list of contexts
fn d_killcontext(args : Value) -> Value raise {
  let mut done = true
  for c in args.iter() {
    if symbolp(c) {
      if killcontext(c) is Nil {
        done = false
      }
    } else {
      nc_err(q_d_killcontext, c) |> ignore
    }
  }
  db_gc() |> ignore
  if done {
    q_d_done
  } else {
    q_d_not_done
  }
}

///|
fn killallcontexts() -> Value raise {
  mapcar(c => killcontext(c), cdr(symval(q_d_contexts))) |> ignore
  set(q_d_context, q_d_initial) |> ignore
  set(q_context, q_d_initial) |> ignore
  set(q_current, q_d_initial) |> ignore
  set(q_d_contexts, list([list1(q_mlist), q_d_initial, q_d_global])) |> ignore
  // The DB variables conmark, conunmrk, conindex, connumber, and contexts
  // concern garbage-collectible contexts, so they are not reset.
  putprop(q_d_global, Fix(1L), q_cmark) |> ignore
  putprop(q_d_initial, Fix(1L), q_cmark) |> ignore
  putprop(q_d_initial, list1(q_d_global), q_subc) |> ignore
  db_gc()
}

///|
/// Kills the context X and returns T. Complains and returns NIL when X is not
/// a context or is currently active, and returns NIL for the global context.
fn killcontext(x : Value) -> Value raise {
  if memq(x, symval(q_d_contexts)) is Nil {
    mtell(list([Str("killcontext: no such context ~M."), x])) |> ignore
    Nil
  } else if eq(x, q_d_global) {
    Nil
  } else if eq(x, q_d_initial) {
    mapc(d => remov(d) |> ignore, zl_get(q_d_initial, q_data)) |> ignore
    remprop(q_d_initial, q_data) |> ignore
    t
  } else if !eq(symval(q_d_context), x) &&
    {
      // Refuse killing X if the current context or another activated
      // context is built on it. After CONTEXTMARK, the CMARK of X counts the
      // current and the activated contexts that are X or built on X.
      contextmark() |> ignore
      let own = if member(x, cdr(symval(q_d_activecontexts))).truthy() {
        1L
      } else {
        0L
      }
      let cm = zl_get(x, q_cmark)
      num_lt(Fix(own), if cm.truthy() { cm } else { Fix(0L) })
    } {
    mtell(list([Str("killcontext: context ~M is currently active."), x]))
    |> ignore
    Nil
  } else {
    if member(x, symval(q_d_activecontexts)).truthy() {
      // X may have been activated. Deactivate it before deleting.
      d_deactivate(list1(x)) |> ignore
    }
    set(q_d_contexts, d_delete(x, symval(q_d_contexts))) |> ignore
    if eq(x, symval(q_d_context)) && equal(zl_get(x, q_subc), list1(q_d_global)) {
      set(q_d_context, q_d_initial) |> ignore
      set(q_context, q_d_initial) |> ignore
    } else if eq(x, symval(q_d_context)) {
      set(q_d_context, car(zl_get(x, q_subc))) |> ignore
      set(q_context, car(zl_get(x, q_subc))) |> ignore
    }
    killc(x) |> ignore
    t
  }
}

///|
fn nc_err(fn_ : Value, x : Value) -> Value raise {
  merr("~M: context name must be a symbol; found ~M", [fn_, x])
}

// Simplification and evaluation of boolean expressions.
//
// and: if any argument simplifies to false, return false; otherwise omit
// arguments which simplify to true; one remaining -> it; none -> true.
// or: dually. not: true/false -> false/true, otherwise reverse the sense of
// comparisons, otherwise not <simplified argument>.
// is/maybe: evaluate; is complains under prederror, maybe returns unknown.

///|
fn maybe_simplifya(x : Value, z : Value) -> Value raise {
  if z.truthy() {
    x
  } else {
    simplifya(x, z)
  }
}

///|
fn maybe_simplifya_protected(x : Value, z : Value) -> Value raise {
  with_specials([(q_errcatch, t), (q_d_errormsg, Nil)], fn() {
    match errset(fn() {
      maybe_simplifya(x, z) |> ignore
      x
    }) {
      Some(v) => v
      None => Nil
    }
  })
}

///|
fn simp__dolis(x : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let a = maybe_simplifya(cadr(x), z)
  if eq(a, t) || a is Nil {
    a
  } else {
    list2(list2(caar(x), q_simp), a)
  }
}

///|
fn d_is(form : Value) -> Value raise {
  oneargcheck(form) |> ignore
  let r = mevalp1(cadr(form))
  let answer = car(r)
  let patevalled = cadr(r)
  if eq(answer, t) || answer is Nil {
    answer
  } else if symval(q_d_prederror).truthy() {
    pre_err(patevalled)
  } else {
    q_d_unknown
  }
}

///|
fn d_maybe(form : Value) -> Value raise {
  oneargcheck(form) |> ignore
  let pat = cadr(form)
  let x = with_special(q_d_prederror, Nil, () => mevalp1(pat))
  let ans = car(x)
  if eq(ans, t) || ans is Nil {
    ans
  } else {
    q_d_unknown
  }
}

///|
fn is_(pred : Value) -> Value raise {
  with_special(q_d_prederror, t, () => mevalp(pred))
}

///|
fn simp_mand(x : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let simplified = []
  for e in cdr(x).iter() {
    let a = maybe_simplifya(e, z)
    if a is Nil {
      return Nil
    } else if eq(a, q_d_unknown) {
      if !compar__in(q_d_unknown, simplified) {
        simplified.push(a)
      }
    } else if !eq(a, t) {
      simplified.push(a)
    }
  }
  match simplified.length() {
    0 => t
    1 => simplified[0]
    _ => cons(list2(q_mand, q_simp), list(simplified))
  }
}

///|
fn simp_mor(x : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let simplified = []
  for e in cdr(x).iter() {
    let a = maybe_simplifya(e, z)
    if eq(a, t) {
      return t
    } else if eq(a, q_d_unknown) {
      if !compar__in(q_d_unknown, simplified) {
        simplified.push(a)
      }
    } else if !(a is Nil) {
      simplified.push(a)
    }
  }
  match simplified.length() {
    0 => Nil
    1 => simplified[0]
    _ => cons(list2(q_mor, q_simp), list(simplified))
  }
}

///|
fn simp_mnot(x : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let arg = maybe_simplifya(cadr(x), z)
  if atom(arg) {
    if eq(arg, t) || eq(arg, q_d_true) {
      Nil
    } else if arg is Nil || eq(arg, q_d_false) {
      t
    } else if eq(arg, q_d_unknown) {
      q_d_unknown
    } else {
      list2(list2(q_mnot, q_simp), arg)
    }
  } else {
    let arg_op = caar(arg)
    let arg_arg = cdr(arg)
    if eq(arg_op, q_mlessp) {
      simplify(cons(list1(q_mgeqp), arg_arg))
    } else if eq(arg_op, q_mleqp) {
      simplify(cons(list1(q_mgreaterp), arg_arg))
    } else if eq(arg_op, q_mequal) {
      simplify(cons(list1(q_mnotequal), arg_arg))
    } else if eq(arg_op, q_d_equal) {
      simplify(cons(list1(q_d_notequal), arg_arg))
    } else if eq(arg_op, q_mnotequal) {
      simplify(cons(list1(q_mequal), arg_arg))
    } else if eq(arg_op, q_d_notequal) {
      simplify(cons(list1(q_d_equal), arg_arg))
    } else if eq(arg_op, q_mgeqp) {
      simplify(cons(list1(q_mlessp), arg_arg))
    } else if eq(arg_op, q_mgreaterp) {
      simplify(cons(list1(q_mleqp), arg_arg))
    } else if eq(arg_op, q_mnot) {
      car(arg_arg)
    } else if eq(arg_op, q_mand) {
      // Distribute negation over conjunction and disjunction.
      let l = mapcar(e => list2(list1(q_mnot), e), arg_arg)
      simplifya(cons(list1(q_mor), l), Nil)
    } else if eq(arg_op, q_mor) {
      let l = mapcar(e => list2(list1(q_mnot), e), arg_arg)
      simplifya(cons(list1(q_mand), l), Nil)
    } else {
      list2(list2(q_mnot, q_simp), arg)
    }
  }
}

///|
fn mevalp(pat : Value) -> Value raise {
  let x = mevalp1(pat)
  let ans = car(x)
  let patevalled = cadr(x)
  if eq(ans, t) || ans is Nil {
    ans
  } else if symval(q_d_prederror).truthy() {
    pre_err(patevalled)
  } else if patevalled.truthy() {
    patevalled
  } else {
    ans
  }
}

///|
fn compar__boolop(x : Value) -> Bool {
  let o = caar(x)
  eq(o, q_mnot) || eq(o, q_mand) || eq(o, q_mor)
}

///|
fn mevalp1(pat : Value) -> Value raise {
  let mut patevalled : Value = Nil
  let ans = if !atom(pat) && compar__boolop(pat) {
    if eq(q_mnot, caar(pat)) {
      is_mnot(q_mevalp, cadr(pat))
    } else if eq(q_mand, caar(pat)) {
      is_mand(q_mevalp, cdr(pat))
    } else {
      is_mor(q_mevalp, cdr(pat))
    }
  } else {
    patevalled = specrepcheck(meval(pat))
    if atom(patevalled) {
      patevalled
    } else if compar__boolop(patevalled) {
      return mevalp1(patevalled)
    } else {
      mevalp2(patevalled, caar(patevalled), cadr(patevalled), caddr(patevalled))
    }
  }
  list2(ans, patevalled)
}

///|
fn mevalp2(
  patevalled : Value,
  pred : Value,
  arg1 : Value,
  arg2 : Value,
) -> Value raise {
  if eq(q_mequal, pred) {
    like(arg1, arg2)
  } else if eq(q_d_equal, pred) {
    meqp(arg1, arg2)
  } else if eq(q_mnotequal, pred) {
    lbool(like(arg1, arg2) is Nil)
  } else if eq(q_d_notequal, pred) {
    mnqp(arg1, arg2)
  } else if eq(q_mgreaterp, pred) {
    mgrp(arg1, arg2)
  } else if eq(q_mlessp, pred) {
    mgrp(arg2, arg1)
  } else if eq(q_mgeqp, pred) {
    mgqp(arg1, arg2)
  } else if eq(q_mleqp, pred) {
    mgqp(arg2, arg1)
  } else {
    isp(munformat(patevalled))
  }
}

///|
fn pre_err(pat : Value) -> Value raise {
  merr("Unable to evaluate predicate ~M", [pat])
}

///|
fn is_mnot(pred_eval : Value, pred : Value) -> Value raise {
  let pred = funcall(pred_eval, [pred])
  if eq(t, pred) {
    Nil
  } else if pred is Nil {
    t
  } else {
    pred_reverse(pred)
  }
}

///|
fn pred_reverse(pred : Value) -> Value raise {
  take(list1(q_mnot), [pred])
}

///|
fn is_mand(pred_eval : Value, pl : Value) -> Value raise {
  let npl = []
  for p in pl.iter() {
    let dummy = funcall(pred_eval, [p])
    if eq(t, dummy) {
      ()
    } else if dummy is Nil {
      return Nil
    } else {
      npl.push(dummy)
    }
  }
  match npl.length() {
    0 => t
    1 => npl[0]
    _ => cons(list1(q_mand), list(npl))
  }
}

///|
fn is_mor(pred_eval : Value, pl : Value) -> Value raise {
  let npl = []
  for p in pl.iter() {
    let dummy = funcall(pred_eval, [p])
    if eq(t, dummy) {
      return t
    } else if dummy is Nil {
      ()
    } else {
      npl.push(dummy)
    }
  }
  match npl.length() {
    0 => Nil
    1 => npl[0]
    _ => cons(list1(q_mor), list(npl))
  }
}

///|
fn d_assume(x : Value) -> Value raise {
  let nl = []
  for e in cdr(x).iter() {
    if atom(e) {
      nl.push(assume(meval(e)))
    } else if eq(q_mand, caar(e)) {
      for l in cdr(e).iter() {
        nl.push(assume(meval(l)))
      }
    } else if eq(q_mnot, caar(e)) {
      nl.push(assume(meval(pred_reverse(cadr(e)))))
    } else if eq(q_mor, caar(e)) {
      merr("assume: argument cannot be an 'or' expression; found ~M", [e])
      |> ignore
    } else if eq(caar(e), q_mequal) {
      merr(
        "assume: argument cannot be an '=' expression; found ~M~%assume: maybe you want 'equal'.",
        [e],
      )
      |> ignore
    } else if eq(caar(e), q_mnotequal) {
      merr(
        "assume: argument cannot be a '#' expression; found ~M~%assume: maybe you want 'not equal'.",
        [e],
      )
      |> ignore
    } else {
      nl.push(assume(meval(e)))
    }
  }
  cons(list1(q_mlist), list(nl))
}

///|
fn compar__not_equal_to_notequal(pat : Value) -> Value {
  if !atom(pat) &&
    eq(caar(pat), q_mnot) &&
    !atom(cadr(pat)) &&
    eq(caaadr(pat), q_d_equal) {
    cons(list1(q_d_notequal), cdadr(pat))
  } else {
    pat
  }
}

///|
fn assume(pat : Value) -> Value raise {
  let pat = compar__not_equal_to_notequal(pat)
  if !learnablep(pat).truthy() {
    q_d_meaningless
  } else if eq(caar(pat), q_d_kind) {
    assume_kind(pat)
  } else {
    let dummy = with_special(q_d_assume_pos, Nil, () => car(mevalp1(pat)))
    if eq(dummy, t) {
      q_d_redundant
    } else if dummy is Nil {
      q_d_inconsistent
    } else if atom(dummy) {
      q_d_meaningless
    } else {
      learn(pat, t)
    }
  }
}

///|
/// assume() on a kind(x, property) expression, restricted to the features
/// that facts() can emit, so that the output of facts() can be fed back.
fn assume_kind(pat : Value) -> Value raise {
  let var_ = getopr(cadr(pat))
  let prop = caddr(pat)
  if memq(prop, cdr(symval(q_d_features))) is Nil {
    q_d_meaningless
  } else if truep(list3(q_kind, var_, prop)).truthy() {
    q_d_redundant
  } else if declaration_inconsistent_p(var_, prop).truthy() {
    q_d_inconsistent
  } else {
    meval(mk(q_d_declare, [var_, prop])) |> ignore
    pat
  }
}

///|
fn learnablep(pat : Value) -> Value raise {
  lbool(
    !atom(pat) &&
    !atom(car(pat)) &&
    (memq(caar(pat), symval(q_ear_learnable_operators)).truthy() ||
    zl_get(caar(pat), q_learn).truthy() ||
    zl_get(caar(pat), q_unlearn).truthy()),
  )
}

///|
fn learn(pat : Value, flag : Value) -> Value raise {
  if atom(pat) {
    return t
  }
  // Check for abs function in pattern.
  if !symval(q_limitp).truthy() {
    let v = learn_abs(pat, flag)
    if v.truthy() {
      return v
    }
  }
  // Check for constant expression in pattern.
  if !symval(q_limitp).truthy() {
    let v = learn_numer(pat, flag)
    if v.truthy() {
      return v
    }
  }
  let ind = if flag.truthy() { q_learn } else { q_unlearn }
  let op = caar(pat)
  if zl_get(op, ind).truthy() {
    funcall(zl_get(op, ind), [pat])
  } else if eq(op, q_mgreaterp) {
    daddgr(flag, sub(cadr(pat), caddr(pat)))
  } else if eq(op, q_mgeqp) {
    daddgq(flag, sub(cadr(pat), caddr(pat)))
  } else if eq(op, q_mequal) || eq(op, q_d_equal) {
    daddeq(flag, sub(cadr(pat), caddr(pat)))
  } else if eq(op, q_mnotequal) || eq(op, q_d_notequal) {
    daddnq(flag, sub(cadr(pat), caddr(pat)))
  } else if eq(op, q_mleqp) {
    daddgq(flag, sub(caddr(pat), cadr(pat)))
  } else if eq(op, q_mlessp) {
    daddgr(flag, sub(caddr(pat), cadr(pat)))
  } else if eq(op, q_d_kind) {
    if flag is Nil {
      unkind(getopr(second(pat)), third(pat)) |> ignore
    }
    pat
  } else {
    Nil
  }
}

///|
/// When abs(x)<a is in the pattern, where a is a positive expression, then
/// learn x<a and -x<a too. The additional facts are put into the context
/// $learndata if the current context is the user context initial.
fn learn_abs(pat : Value, flag : Value) -> Value raise {
  let tmp = isinop(pat, q_mabs)
  if tmp.truthy() &&
    (
      (
        (eq(caar(pat), q_mlessp) || eq(caar(pat), q_mleqp)) &&
        isinop(cadr(pat), q_mabs).truthy() &&
        compar__in(d_sign(caddr(pat)), [q_d_pos, q_d_pz])
      ) ||
      (
        (eq(caar(pat), q_mgreaterp) || eq(caar(pat), q_mgeqp)) &&
        compar__in(d_sign(cadr(pat)), [q_d_pos, q_d_pz]) &&
        isinop(caddr(pat), q_mabs).truthy()
      )
    ) &&
    // abs(x) < a holds iff x < a and -x < a both hold: always learn, but
    // unlearn only if the abs() relation is itself known.
    (flag.truthy() ||
    eq(t, mevalp2(pat, caar(pat), cadr(pat), caddr(pat)))) {
    let oldcontext = symval(q_context)
    if eq(oldcontext, q_d_initial) {
      asscontext(Nil, q_d_learndata) |> ignore // switch to context $learndata
    }
    // learn additional facts
    learn(d_substitute(cadr(tmp), tmp, expr=pat), flag) |> ignore
    learn(d_substitute(mul2(Fix(-1L), cadr(tmp)), tmp, expr=pat), flag)
    |> ignore
    if eq(oldcontext, q_d_initial) {
      asscontext(Nil, oldcontext) |> ignore // switch back to context on entry
      d_activate(list1(q_d_learndata)) |> ignore // $learndata is active
    }
  }
  Nil
}

///|
/// The numerical value of a constant expression in PAT is learned in context
/// $learndata.
fn learn_numer(pat : Value, flag : Value) -> Value raise {
  let acc = []
  for a in cdr(pat).iter() {
    let mut dum = constp(a)
    let mut expr = a
    if numberp(a) || ratnump(a).truthy() {
      ()
    } else if eq(dum, q_bigfloat) {
      dum = d_bfloat(a)
      if d_bfloatp(dum).truthy() {
        expr = dum
      }
    } else if eq(dum, q_float) {
      dum = numer(a)
      if dum.truthy() && numberp(dum) {
        expr = dum
      }
    } else if (eq(dum, q_numer) || eq(dum, q_symbol)) &&
      {
        dum = numer(a)
        dum is Nil ||
        (numberp(dum) &&
        {
          expr = dum
          num_lt(num_abs(dum), Flo(1.0e-6))
        })
      } {
      if symval(q_d_signbfloat).truthy() {
        dum = d_bfloat(a)
        if dum.truthy() && d_bfloatp(dum).truthy() {
          expr = dum
        }
      }
    }
    acc.push(expr)
  }
  let patnew = cons(car(pat), list(acc))
  if !alike(cdr(pat), cdr(patnew)).truthy() &&
    (!mnump(cadr(patnew)).truthy() || !mnump(caddr(patnew)).truthy()) {
    // not both sides of the relation can be numbers
    let oldcontext = symval(q_d_context)
    if eq(oldcontext, q_d_initial) {
      asscontext(Nil, q_d_learndata) |> ignore
    }
    learn(patnew, flag) |> ignore // learn additional fact
    if eq(oldcontext, q_d_initial) {
      asscontext(Nil, oldcontext) |> ignore
      d_activate(list1(q_d_learndata)) |> ignore
    }
  }
  Nil
}

///|
fn d_forget(x : Value) -> Value raise {
  let nl = []
  for e in cdr(x).iter() {
    if atom(e) {
      nl.push(forget(meval(e)))
    } else if eq(q_mand, caar(e)) {
      for l in cdr(e).iter() {
        nl.push(forget(meval(l)))
      }
    } else if eq(q_mnot, caar(e)) {
      nl.push(forget(meval(pred_reverse(cadr(e)))))
    } else if eq(q_mor, caar(e)) {
      merr("forget: argument cannot be an 'or' expression; found ~M", [e])
      |> ignore
    } else {
      nl.push(forget(meval(e)))
    }
  }
  db_gc() |> ignore
  cons(list1(q_mlist), list(nl))
}

///|
fn forget(pat : Value) -> Value raise {
  if d_listp(pat).truthy() {
    cons(list2(q_mlist, q_simp), mapcar(p => forget1(p), cdr(pat)))
  } else {
    forget1(pat)
  }
}

///|
fn forget1(pat : Value) -> Value raise {
  let pat = compar__not_equal_to_notequal(pat)
  if learnablep(pat).truthy() {
    with_specials([(q_ear_fact_removed, Nil), (q_ear_fact_protected, Nil)], fn() {
      let result = learn(pat, Nil)
      if symval(q_ear_fact_removed).truthy() {
        result
      } else if symval(q_ear_fact_protected).truthy() {
        q_d_not_done
      } else {
        q_d_redundant
      }
    })
  } else {
    q_d_meaningless
  }
}

///|
/// used by SAVE
fn restore_facts(factl : Value) -> Value raise {
  for fact in factl.iter() {
    if eq(caar(fact), q_d_kind) {
      declarekind(cadr(fact), caddr(fact)) |> ignore
      add2lnc(getop(cadr(fact)), symval(q_d_props)) |> ignore
    } else if eq(caar(fact), q_d_par) {
      ()
    } else {
      assume(fact) |> ignore
    }
  }
  Nil
}

///|
/// `(compare a b)` = `(sign1 (sub* a b))`
fn compare(a : Value, b : Value) -> Value raise {
  sign1(sub_star(a, b))
}

///|
fn maximum(l : Value) -> Value raise {
  maximin(l, q_d_max)
}

///|
fn minimum(l : Value) -> Value raise {
  maximin(l, q_d_min)
}

///|
fn mand(form : Value) -> Value raise {
  let unevaluated = []
  for e in cdr(form).iter() {
    let x = mevalp(e)
    if x is Nil {
      return Nil
    } else if !eq(x, t) {
      unevaluated.push(x)
    }
  }
  match unevaluated.length() {
    0 => t
    1 => unevaluated[0]
    _ => cons(list1(q_mand), list(unevaluated))
  }
}

///|
fn mor(form : Value) -> Value raise {
  let unevaluated = []
  for e in cdr(form).iter() {
    let x = mevalp(e)
    if eq(x, t) {
      return t
    } else if !(x is Nil) {
      unevaluated.push(x)
    }
  }
  match unevaluated.length() {
    0 => Nil
    1 => unevaluated[0]
    _ => cons(list1(q_mor), list(unevaluated))
  }
}

///|
fn mnot(form : Value) -> Value raise {
  let x = mevalp(cadr(form))
  if eq(x, t) || x is Nil {
    lbool(x is Nil)
  } else {
    list2(list1(q_mnot), x)
  }
}

// Toplevel functions $askequal, $asksign, and $sign.
// Switch LIMITP: if true, $ASKSIGN and $SIGN look for special symbols such as
// EPSILON, $INF, $MINF and attempt to do the correct thing; $REALPART and
// $IMAGPART are used to assure that the expression is real. If NIL they
// assume the expression is real unless it contains %i, in which case they
// call $RECTFORM.

///|
fn d_askequal(a : Value, b : Value) -> Value raise {
  // presumably handles mbags and extended reals.
  let answer = meqp(sratsimp(a), sratsimp(b))
  if eq(answer, t) {
    q_d_yes
  } else if answer is Nil {
    q_d_no
  } else {
    let answer = retrieve(
      mk(q_mtext, [Str("Is "), a, Str(" equal to "), b, Str("?")]),
      compar__hide_prompt(),
    )
    if eq(answer, q_d_no) || eq(answer, q_d_n) || eq(answer, q_d__cn_) {
      tdpn(sub(b, a)) |> ignore
      q_d_no
    } else if eq(answer, q_d_yes) || eq(answer, q_d_y) || eq(answer, q_d__cy_) {
      tdzero(sub(a, b)) |> ignore
      q_d_yes
    } else {
      mtell(list1(Str("Acceptable answers are yes, y, Y, no, n, N. ~%")))
      |> ignore
      d_askequal(a, b)
    }
  }
}

///|
fn d_asksign(exp_ : Value) -> Value raise {
  with_specials(
    [
      (q_sign, Nil),
      (q_minus, Nil),
      (q_odds, Nil),
      (q_evens, Nil),
      (q_factored, Nil),
    ],
    () => asksign01(
      if symval(q_limitp).truthy() {
        restorelim(exp_)
      } else if among(q_d__pcti, exp_).truthy() {
        d_rectform(exp_)
      } else {
        exp_
      },
    ),
  )
}

///|
fn asksign_p_or_n(e : Value) -> Value raise {
  let fact = assume(mk(q_d_notequal, [e, Fix(0L)]))
  compar__unwind(() => d_asksign(e), () => forget(fact) |> ignore)
}

///|
fn asksign01(a : Value) -> Value raise {
  let e = sign_prep(a)
  if eq(e, q_d_pnz) {
    q_d_pnz
  } else {
    let e = asksign1(e)
    if eq(e, q_d_pos) || eq(e, q_d_neg) {
      e
    } else if symval(q_limitp).truthy() {
      eps_sign(a)
    } else {
      q_d_zero
    }
  }
}

///|
/// Return T if %i occurs in X outside of abs(...), whose value is always real.
fn p_i_outside_abs_p(x : Value) -> Value raise {
  if atom(x) {
    lbool(eq(x, q_d__pcti))
  } else if specrepp(x).truthy() {
    lbool(!free(x, q_d__pcti).truthy())
  } else if eq(caar(x), q_mabs) {
    Nil
  } else {
    lbool(some(y => p_i_outside_abs_p(y).truthy(), cdr(x)))
  }
}

///|
/// csign returns t if x appears to be complex. Else, it returns the sign.
fn csign(x : Value) -> Value raise {
  let v = p_i_outside_abs_p(x)
  if v.truthy() {
    return v
  }
  with_specials([(q_sign_imag_errp, Nil), (q_limitp, Nil)], () => catch_tag(
    q_sign_imag_err,
    () => d_sign(x),
  ))
}

///|
/// $csign works like $sign but switches the sign-functions into a complex
/// mode, in which complex and imaginary expressions give the results
/// imaginary or complex.
fn d_csign(z : Value) -> Value raise {
  with_specials([(q_ear_complexsign, t), (q_limitp, Nil)], () => d_sign(z))
}

///|
fn d_sign(x : Value) -> Value raise {
  let x = specrepcheck(x)
  with_specials(
    [
      (q_sign, Nil),
      (q_minus, Nil),
      (q_odds, Nil),
      (q_evens, Nil),
      (q_factored, Nil),
    ],
    fn() {
      sign01(
        if symval(q_limitp).truthy() {
          restorelim(x)
        } else if compar__cs() {
          // No rectform in complex mode: it asks unnecessary questions about
          // complex expressions and cannot handle imaginary ones completely.
          if symval(q_ear_debug_compar).truthy() {
            format(t, "~&$SIGN with ~A~%", [x]) |> ignore
          }
          x
        } else if !free(x, q_d__pcti).truthy() {
          d_rectform(x)
        } else {
          x
        },
      )
    },
  )
}

///|
fn sign01(a : Value) -> Value raise {
  let e = sign_prep(a)
  if eq(e, q_d_pnz) {
    q_d_pnz
  } else {
    let e = sign1(e)
    if symval(q_limitp).truthy() && eq(e, q_d_zero) {
      eps_sign(a)
    } else {
      e
    }
  }
}

///|
/// Preparation for asking questions from DEFINT or LIMIT.
fn sign_prep(x : Value) -> Value raise {
  if symval(q_limitp).truthy() {
    let ri = trisplit(x)
    let rpart = car(ri)
    let ipart = cdr(ri)
    if equal(sratsimp(ipart), Fix(0L)) && free(rpart, q_d_infinity).truthy() {
      let x = nmr(sratsimp(rpart))
      if free(x, q_prin_inf).truthy() {
        x
      } else {
        d_limit(list([x, q_prin_inf, q_d_inf, q_d_minus]))
      }
    } else {
      q_d_pnz // Confess ignorance if COMPLEX.
    }
  } else {
    x
  }
}

///|
/// don't ask about internal variables created by gruntz
fn has_int_symbols(e : Value) -> Value raise {
  if symbolp(e) && get(e, q_internal).truthy() {
    t
  } else if atom(e) {
    Nil
  } else if has_int_symbols(car(e)).truthy() {
    t
  } else {
    has_int_symbols(cdr(e))
  }
}

///|
/// The limit of A as EPS ($ZEROA or $ZEROB) goes to 0 from direction DIR,
/// using a fresh variable since limit() rejects those constants.
fn infinitesimal_limit(a : Value, eps : Value, dir : Value) -> Value raise {
  let v = gensym()
  maxima_substitute(
    eps,
    v,
    d_limit(list([maxima_substitute(v, eps, a), v, Fix(0L), dir])),
  )
}

///|
/// Do substitutions for special symbols.
fn nmr(a : Value) -> Value raise {
  let mut a = a
  if !free(a, q_d_zeroa).truthy() {
    a = infinitesimal_limit(a, q_d_zeroa, q_d_plus)
  }
  if !free(a, q_d_zerob).truthy() {
    a = infinitesimal_limit(a, q_d_zerob, q_d_minus)
  }
  if !free(a, q_z_star_star).truthy() {
    a = d_limit(list([a, q_z_star_star, Fix(0L), q_d_plus]))
  }
  if !free(a, q_ear_z).truthy() {
    a = d_limit(list([a, q_ear_z, Fix(0L), q_d_plus]))
  }
  if !free(a, q_epsilon).truthy() {
    a = d_limit(list([a, q_epsilon, Fix(0L), q_d_plus]))
  }
  a
}

///|
/// Get the sign of EPSILON-like terms. Could be made MUCH hairier.
fn eps_sign(b : Value) -> Value raise {
  // unset limitp to prevent infinite recursion
  with_special(q_limitp, Nil, fn() {
    let mut temp1 : Value = Nil
    let mut temp2 : Value = Nil
    let mut temp3 : Value = Nil
    let mut free1 = false
    let mut free2 = false
    let mut free3 = false
    if !free(b, q_d_zeroa).truthy() {
      temp1 = eps_coef_sign(b, q_d_zeroa)
    } else {
      free1 = true
    }
    if !free(b, q_d_zerob).truthy() {
      temp2 = eps_coef_sign(b, q_d_zerob)
    } else {
      free2 = true
    }
    if !free(b, q_epsilon).truthy() {
      temp3 = eps_coef_sign(b, q_epsilon)
    } else {
      free3 = true
    }
    if free1 && free2 && free3 {
      q_d_zero
    } else if temp1.truthy() || temp2.truthy() || temp3.truthy() {
      if temp1 is Nil && temp2 is Nil {
        temp3
      } else if temp2 is Nil && temp3 is Nil {
        temp1
      } else if temp1 is Nil && temp3 is Nil {
        temp2
      } else {
        merr("asksign: internal error.", [])
      }
    } else {
      Nil
    }
  })
}

///|
fn eps_coef_sign(exp_ : Value, epskind : Value) -> Value raise {
  // $LOPOW is defined inside a LET in comm.lisp and has no declaration;
  // reach it through its function cell.
  let eps_power = funcall(q_d_lopow, [exp_, epskind])
  let mut eps_coef : Value = Nil
  if !equal(eps_power, Fix(0L)) &&
    {
      eps_coef = ratcoeff(exp_, epskind, eps_power)
      !equal(eps_coef, Fix(0L))
    } &&
    eq(ask_integer(eps_power, q_d_integer), q_d_yes) {
    if eq(ask_integer(eps_power, q_d_even), q_d_yes) {
      d_sign(eps_coef)
    } else if eq(ask_integer(eps_power, q_d_odd), q_d_yes) {
      eps_coef = d_sign(eps_coef)
      if (
          eq(eps_coef, q_d_pos) &&
          (eq(epskind, q_epsilon) || eq(epskind, q_d_zeroa))
        ) ||
        (
          eq(eps_coef, q_d_neg) &&
          (
            alike1(epskind, mul2_star(Fix(-1L), q_epsilon)).truthy() ||
            eq(epskind, q_d_zerob)
          )
        ) {
        q_d_pos
      } else {
        q_d_neg
      }
    } else {
      merr("sign or asksign: insufficient information.", [])
    }
  } else {
    let deriv = sdiff(exp_, epskind)
    let deriv_sign = d_sign(deriv)
    if !eq(deriv_sign, q_d_zero) {
      total_sign(epskind, deriv_sign)
    } else {
      let deriv_sign = d_sign(sdiff(deriv, epskind))
      if !eq(deriv_sign, q_d_zero) {
        deriv_sign
      } else {
        merr("sign or asksign: insufficient data.", [])
      }
    }
  }
}

///|
/// The above code does a partial Taylor series analysis of something that
/// isn't a polynomial.
fn total_sign(epskind : Value, factor_sign : Value) -> Value raise {
  if eq(epskind, q_d_zeroa) || eq(epskind, q_epsilon) {
    if eq(factor_sign, q_d_pos) {
      q_d_pos
    } else if eq(factor_sign, q_d_neg) {
      q_d_neg
    } else if eq(factor_sign, q_d_zero) {
      q_d_zero
    } else {
      Nil
    }
  } else if eq(epskind, q_d_zerob) {
    if eq(factor_sign, q_d_pos) {
      q_d_neg
    } else if eq(factor_sign, q_d_neg) {
      q_d_pos
    } else if eq(factor_sign, q_d_zero) {
      q_d_zero
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn asksign(x : Value) -> Value raise {
  let x = d_asksign(x)
  if eq(q_d_pos, x) {
    q_d_positive
  } else if eq(q_d_neg, x) {
    q_d_negative
  } else if eq(q_d_pnz, x) {
    q_d_pnz // COMPLEX expression encountered here.
  } else {
    q_d_zero
  }
}

///|
/// When asksign is called on an expression that involves a symbol with the
/// internal property and sign can only determine pnz, nz, or similar,
/// asksign1 returns $pnz.
fn asksign1(d_askexp : Value) -> Value raise {
  // The parameter is the special $ASKEXP.
  let b = bind(q_d_askexp, d_askexp)
  defer unbind(b)
  with_special(q_d_radexpand, Nil, () => sign1(symval(q_d_askexp))) |> ignore
  let sg = compar__sign()
  if compar__in(sg, [q_d_pos, q_d_neg, q_d_zero, q_d_imaginary]) {
    return sg
  }
  if has_int_symbols(symval(q_d_askexp)).truthy() {
    return q_d_pnz
  }
  let mut domain = sg
  let mut squared : Value = Nil
  if symval(q_odds) is Nil {
    set(q_d_askexp, lmul(symval(q_evens))) |> ignore
    domain = q_d_znz
    squared = t
  } else {
    if symval(q_minus).truthy() {
      set(q_sign, flip(compar__sign())) |> ignore
      domain = flip(domain)
    }
    set(
      q_d_askexp,
      lmul(
        nconc(symval(q_odds), mapcar(l => power(l, Fix(2L)), symval(q_evens))),
      ),
    )
    |> ignore
  }
  set(q_sign, cdr(assol(symval(q_d_askexp), symval(q_ear_local_signs))))
  |> ignore
  ensure_sign(symval(q_d_askexp), domain=domain, squared=squared)
}

///|
/// If SGN makes sense for DOMAIN store the result (see ENSURE-SIGN) and
/// return it. Otherwise, return NIL. If SQUARED is true, we are actually
/// looking for the sign of the square, so any negative results are converted
/// to positive.
fn match_sign(
  sgn : Value,
  domain : Value,
  expression : Value,
  squared : Value,
) -> Value raise {
  // Entries: (MATCH DOMAINS REGISTRAR SIGN SIGN-SQ)
  let behaviour : Array[(Array[Value], Array[Value], Int, Value, Value)] = [
    (
      [q_d_pos, q_d__cp_, q_d_p, q_d_positive],
      [Nil, q_d_znz, q_d_pz, q_d_pn, q_d_pnz],
      0,
      q_d_pos,
      q_d_pos,
    ),
    (
      [q_d_neg, q_d__cn_, q_d_n, q_d_negative],
      [Nil, q_d_znz, q_d_nz, q_d_pn, q_d_pnz],
      1,
      q_d_neg,
      q_d_pos,
    ),
    (
      [q_d_zero, q_d__cz_, q_d_z, Fix(0L), Flo(0.0)],
      [Nil, q_d_znz, q_d_pz, q_d_nz, q_d_pnz],
      2,
      q_d_zero,
      q_d_zero,
    ),
    (
      [q_d_pn, q_d_nonzero, q_d_nz, q_d_nonz, q_d_non0],
      [q_d_znz],
      3,
      q_d_pn,
      q_d_pos,
    ),
  ]
  for bh in behaviour {
    let (matches, domains, registrar, sign_, sign_sq) = bh
    if matches.iter().any(m => equal(sgn, m)) && compar__in(domain, domains) {
      let found_sign = if squared.truthy() { sign_sq } else { sign_ }
      let _ = match registrar {
        0 => tdpos(expression)
        1 => tdneg(expression)
        2 => tdzero(expression)
        _ => tdpn(expression)
      }
      return set(
        q_sign,
        if symval(q_minus).truthy() {
          flip(found_sign)
        } else {
          found_sign
        },
      )
    }
  }
  Nil
}

///|
/// Try to determine the sign of EXPR, asking the user. DOMAIN may restrict
/// the question ($pz, $nz, $pn, $znz); SQUARED means the sign of EXPR^2 is
/// wanted. The special SIGN holds the best current guess; the result is
/// stored with TDPOS/TDNEG/TDZERO/TDPN and SIGN is set.
fn ensure_sign(
  expr : Value,
  domain? : Value = Nil,
  squared? : Value = Nil,
) -> Value raise {
  while true {
    let new_sign = match_sign(compar__sign(), domain, expr, squared)
    if new_sign.truthy() {
      return new_sign
    }
    let question = if eq(domain, q_d_znz) {
      " zero or nonzero?"
    } else if eq(domain, q_d_pz) {
      " positive or zero?"
    } else if eq(domain, q_d_nz) {
      " negative or zero?"
    } else if eq(domain, q_d_pn) {
      " positive or negative?"
    } else {
      " positive, negative or zero?"
    }
    set(
      q_sign,
      retrieve(
        list([list1(q_mtext), Str("Is "), expr, Str(question)]),
        compar__hide_prompt(),
      ),
    )
    |> ignore
  }
  Nil
}

///|
/// During one evaluation phase asksign writes answers from the user into the
/// global context $initial. clearsign removes them after the evaluation
/// phase (called from meval*); they are recorded in *LOCAL-SIGNS*.
fn clearsign() -> Value raise {
  with_special(q_context, q_d_initial, fn() {
    for cons_pair in symval(q_ear_local_signs).iter() {
      let x = car(cons_pair)
      let sgn = cdr(cons_pair)
      if eq(q_d_pos, sgn) {
        daddgr(Nil, x) |> ignore
      } else if eq(q_d_neg, sgn) {
        daddgr(Nil, neg(x)) |> ignore
      } else if eq(q_d_zero, sgn) {
        daddeq(Nil, x) |> ignore
      } else if eq(q_d_pn, sgn) {
        daddnq(Nil, x) |> ignore
      } else if eq(q_d_pz, sgn) {
        daddgq(Nil, x) |> ignore
      } else if eq(q_d_nz, sgn) {
        daddgq(Nil, neg(x)) |> ignore
      }
    }
  })
  set(q_ear_local_signs, Nil)
}
