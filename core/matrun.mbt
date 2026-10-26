// Port of src/matrun.lisp: run-time support for the rules compiled by
// matcom (disprule, remrule, apply1, applyb1, apply2, applyb2) and the
// matching helpers called from compiled match programs (FINDFUN, FINDEXPON,
// FINDBASE, PART+, PART*).

///|
fn d_disprule(l : Value) -> Value raise {
  let l = cdr(l)
  if eq(car(l), q_d_all) && cdr(l) is Nil {
    disprule1(cdr(symval(q_d_rules)))
  } else {
    disprule1(l)
  }
}

///|
fn disprule1(l : Value) -> Value raise {
  cons(
    list2(q_mlist, q_simp),
    mapcar(r => cadr(d_ldisp(list1(consrule(r)))), l),
  )
}

///|
fn consrule(x : Value) -> Value raise {
  let rule = mget(x, q_d_rule)
  if rule.truthy() {
    list3(list2(q_msetq, q_simp), x, cons(list2(q_marrow, q_simp), cdr(rule)))
  } else {
    merr("disprule: ~:M is not a user rule.", [x])
  }
}

///|
fn d_remrule(op : Value, rule : Value) -> Value raise {
  let op = getopr(op)
  if !eq(rule, q_d_all) {
    removerule(op, rule) |> ignore
    return getop(op)
  }
  let mut rules = mget(op, q_oldrules)
  if rules is Nil {
    merr("remrule: no rules known for operator ~:@M", [op]) |> ignore
  }
  while true {
    if rules is Nil || cdr(rules) is Nil {
      mputprop(op, Fix(1L), q_rulenum) |> ignore
      return getop(op)
    }
    removerule(op, car(rules)) |> ignore
    rules = cdr(rules)
  }
  Nil
}

///|
/// `(delete x l :count 1 :test #'eq)`
fn matrun__delete1(x : Value, l : Value) -> Value {
  match l {
    Cons(c) if eq(c.car, x) => c.cdr
    Cons(_) => {
      let mut p = l
      while cdr(p) is Cons(n) {
        if eq(n.car, x) {
          rplacd(p, n.cdr) |> ignore
          break
        }
        p = cdr(p)
      }
      l
    }
    _ => l
  }
}

///|
fn removerule(op : Value, rule : Value) -> Value raise {
  if memq(rule, symval(q_ear_builtin__dolrules)).truthy() {
    return mget(op, q_oldrules)
  }
  let mut oldrules = mget(op, q_oldrules)
  let mut othrulename : Value = Nil
  let mut othrule : Value = Nil
  if rule is Nil ||
    ({
      oldrules = member_equal(rule, oldrules)
      oldrules is Nil
    }) {
    merr("remrule: no such rule: ~:M", [rule]) |> ignore
  } else if ({
      oldrules = cdr(oldrules)
      car(oldrules) is Nil
    }) {
    oldrules = cdr(oldrules)
    othrulename = Nil
    othrule = lfunc("lambda", fn(args) raise {
      simpargs(arg(args, 0), arg(args, 2))
    })
  } else {
    othrulename = car(oldrules)
    othrule = cadr(getl(car(oldrules), list2(q_expr, q_subr)))
  }
  putprop_or_remprop(rule, othrule, q_expr) |> ignore
  let old = cdr(member_equal(rule, reverse(mget(op, q_oldrules))))
  if old.truthy() {
    putprop_or_remprop(
      car(old),
      subst(othrulename, rule, get(car(old), q_expr)),
      q_expr,
    )
    |> ignore
  }
  if boundp(rule) {
    makunbound(rule) |> ignore
  }
  mremprop(rule, q_d_rule) |> ignore
  mremprop(rule, q_d_ruletype) |> ignore
  mremprop(rule, q_ruleof) |> ignore
  remprop(rule, q_expr) |> ignore
  set(q_d_rules, matrun__delete1(rule, symval(q_d_rules))) |> ignore
  putprop_or_remprop(rule, othrulename, q_expr) |> ignore
  if eq(get(op, q_operators), rule) {
    putprop_or_remprop(op, othrulename, q_operators) |> ignore
  }
  let l = delete(rule, mget(op, q_oldrules))
  if equal(l, list1(Nil)) {
    mremprop(op, q_oldrules) |> ignore
  } else {
    mputprop(op, l, q_oldrules) |> ignore
  }
  l
}

///|
fn putprop_or_remprop(x : Value, y : Value, z : Value) -> Value raise {
  if y.truthy() {
    putprop(x, y, z)
  } else {
    remprop(x, z)
  }
}

///|
fn findbe(e : Value) -> Value raise {
  if equal(e, Fix(1L)) {
    cons(Fix(1L), Fix(0L))
  } else if equal(e, Fix(0L)) {
    cons(Fix(0L), Fix(1L))
  } else if atom(e) {
    cons(e, Fix(1L))
  } else if eq(caar(e), q_mexpt) {
    cons(cadr(e), caddr(e))
  } else {
    cons(e, Fix(1L))
  }
}

///|
fn matrun__plustimes(c : Value) -> Bool {
  eq(c, q_mplus) || eq(c, q_mtimes)
}

///|
fn findfun(e : Value, p : Value, c : Value) -> Value raise {
  let mut e = e
  if !atom(e) && eq(caar(e), p) {
    return e
  } else if atom(e) || !eq(caar(e), c) {
    matcherr() |> ignore
  } else if symval(q_matchreverse) is Nil && matrun__plustimes(c) {
    e = reverse(cdr(e))
  } else {
    e = cdr(e)
  }
  while true {
    // b
    if e is Nil {
      matcherr() |> ignore
    } else if !atom(car(e)) && eq(caaar(e), p) {
      return car(e)
    }
    e = cdr(e)
  }
  Nil
}

///|
fn findexpon(e1 : Value, base_star : Value, c : Value) -> Value raise {
  let mut e = e1
  let mut go_c = false
  if mexptp(e).truthy() && alike1(base_star, cadr(e)).truthy() {
    return caddr(e)
  } else if atom(e) || !eq(caar(e), c) {
    go_c = true
  } else if symval(q_matchreverse) is Nil && matrun__plustimes(c) {
    e = reverse(cdr(e))
  } else {
    e = cdr(e)
  }
  if !go_c {
    while true {
      if e is Nil {
        break
      } else if mexptp(car(e)).truthy() && alike1(base_star, cadar(e)).truthy() {
        return caddar(e)
      }
      e = cdr(e)
    }
  }
  // c
  if (
      !atom(e1) &&
      matrun__plustimes(c) &&
      eq(c, caar(e1)) &&
      memalike(base_star, e1).truthy()
    ) ||
    alike1(e1, base_star).truthy() ||
    (!atom(base_star) && eq(c, caar(base_star))) {
    Fix(1L)
  } else if eq(c, q_mexpt) {
    matcherr()
  } else {
    Fix(0L)
  }
}

///|
fn findbase(e : Value, expon : Value, c : Value) -> Value raise {
  let mut e = e
  if equal(expon, Fix(0L)) {
    if eq(c, q_mexpt) && !equal(Fix(1L), e) {
      matcherr() |> ignore
    }
    return Fix(1L)
  } else if equal(expon, Fix(1L)) {
    return e
  } else if numberp(expon) && num_gt(expon, Fix(0L)) && equal(e, Fix(0L)) {
    return Fix(0L)
  } else if mexptp(e).truthy() && alike1(expon, caddr(e)).truthy() {
    return cadr(e)
  } else if atom(e) || !eq(caar(e), c) {
    matcherr() |> ignore
  } else if symval(q_matchreverse) is Nil && matrun__plustimes(c) {
    e = reverse(cdr(e))
  } else {
    e = cdr(e)
  }
  while true {
    if e is Nil {
      return if realp(expon) && minusp(expon) { Fix(1L) } else { Fix(0L) }
    } else if mexptp(car(e)).truthy() && alike1(expon, caddar(e)).truthy() {
      return cadar(e)
    }
    e = cdr(e)
  }
  Nil
}

///|
fn part_plus(e : Value, p : Value, preds : Value) -> Value raise {
  if consp(e) && eq(caar(e), q_mplus) {
    part_plus_mplus(e, p, preds)
  } else {
    part_plus_not_mplus(e, p, preds)
  }
}

///|
fn part_plus_not_mplus(e : Value, p : Value, preds : Value) -> Value raise {
  part_plus_mplus(list3(list1(q_mplus), Fix(0L), e), p, preds)
}

///|
fn part_plus_mplus(e : Value, p : Value, preds : Value) -> Value raise {
  matrun__part(e, p, preds, true)
}

///|
fn part_star(e : Value, p : Value, preds : Value) -> Value raise {
  if consp(e) && eq(caar(e), q_mtimes) {
    part_star_mtimes(e, p, preds)
  } else {
    part_star_not_mtimes(e, p, preds)
  }
}

///|
fn part_star_not_mtimes(e : Value, p : Value, preds : Value) -> Value raise {
  part_star_mtimes(list3(list1(q_mtimes), Fix(1L), e), p, preds)
}

///|
fn part_star_mtimes(e : Value, p : Value, preds : Value) -> Value raise {
  matrun__part(e, p, preds, false)
}

///|
/// `(catch 'match (mcall pred z))`
fn matrun__catch_mcall(pred : Value, z : Value) -> Value raise {
  catch_tag(q_match, () => mcall(pred, list1(z)))
}

///|
/// `(delete z e :count 1 :test #'equal)`
fn matrun__delete1_equal(x : Value, l : Value) -> Value {
  match l {
    Cons(c) if equal(c.car, x) => c.cdr
    Cons(_) => {
      let mut p = l
      while cdr(p) is Cons(n) {
        if equal(n.car, x) {
          rplacd(p, n.cdr) |> ignore
          break
        }
        p = cdr(p)
      }
      l
    }
    _ => l
  }
}

///|
/// PART+-MPLUS (PLUS = true) and PART*-MTIMES (PLUS = false).
fn matrun__part(
  e : Value,
  p : Value,
  preds : Value,
  plus : Bool,
) -> Value raise {
  let mut e = e
  let mut p = p
  let mut preds = preds
  let mut flag = false
  if plus {
    if mplusp(e) is Nil {
      matcherr() |> ignore
    }
  } else if mtimesp(e) is Nil {
    matcherr() |> ignore
  }
  if length(p) > length(preds) {
    p = reverse(p)
    p = nthkdr(p, int(length(p) - length(preds)))
    p = nreverse(p)
  }
  e = copy_tree(e)
  e = cdr(e)
  let ident : Value = if plus { Fix(0L) } else { Fix(1L) }
  while true {
    // a
    if p is Nil {
      if e is Nil {
        return t
      } else {
        matcherr() |> ignore
      }
    }
    let mut goto_b = false
    if cdr(preds).truthy() &&
      ({
        let o = car(caddar(preds))
        eq(o, q_msetq) || eq(o, q_setq)
      }) {
      if flag {
        if plus {
          merr("PART+: two or more pattern variables match anything.", [])
          |> ignore
        } else {
          merr("PART*: two or more pattern variables match anything.", [])
          |> ignore
        }
      } else {
        flag = true
        p = reverse(p)
        preds = reverse(preds)
        continue
      }
    } else if !atom(car(p)) {
      let mut mye = e
      while true {
        if mye is Nil {
          matcherr() |> ignore
        }
        let val = matrun__catch_mcall(car(preds), car(mye))
        if val is Nil {
          mye = cdr(mye)
        } else {
          e = matrun__delete1_equal(car(mye), e)
          break
        }
      }
      goto_b = true
    } else {
      mset(car(p), ident) |> ignore
    }
    if !goto_b {
      let mut saved = ident
      let pred = car(preds)
      // MAPC over the original list while E is destructively modified.
      let mut zs = e
      while zs is Cons(zc) {
        let z = zc.car
        let val = matrun__catch_mcall(pred, z)
        if val.truthy() {
          saved = if plus {
            add2_star(saved, val)
          } else {
            mul2_star(saved, val)
          }
          e = matrun__delete1_equal(z, e)
        }
        zs = zc.cdr
      }
      if equal(saved, ident) && matrun__catch_mcall(pred, ident) is Nil {
        matcherr() |> ignore
      }
      mset(car(p), saved) |> ignore
    }
    // b
    preds = cdr(preds)
    p = cdr(p)
  }
  Nil
}

///|
fn d_apply1(l : Value) -> Value raise {
  let l = cdr(l)
  let mut expr = meval(car(l))
  for z in cdr(l).iter() {
    expr = apply1(expr, z, Fix(0L))
  }
  expr
}

///|
fn apply1(expr : Value, n_starrule : Value, depth : Value) -> Value raise {
  if num_gt(depth, symval(q_d_maxapplydepth)) {
    return expr
  }
  n_starrulechk(n_starrule) |> ignore
  let mut expr = rule_apply(n_starrule, expr)
  while true {
    if atom(expr) || mnump(expr).truthy() {
      return expr
    } else if eq(caar(expr), q_mrat) {
      expr = ratdisrep(expr)
    } else {
      let d1 = one_plus(depth)
      return simplifya(
        cons(
          delsimp(car(expr)),
          mapcar(z => apply1(z, n_starrule, d1), cdr(expr)),
        ),
        t,
      )
    }
  }
  expr
}

///|
fn d_applyb1(l : Value) -> Value raise {
  let l = cdr(l)
  let mut expr = meval(car(l))
  for z in cdr(l).iter() {
    expr = car(apply1hack(expr, z))
  }
  expr
}

///|
fn apply1hack(expr : Value, n_starrule : Value) -> Value raise {
  let mut expr = expr
  n_starrulechk(n_starrule) |> ignore
  while true {
    if atom(expr) {
      let (ans, rule_hit) = matcom__mcall_mv(n_starrule, [expr])
      return cons(if rule_hit.truthy() { ans } else { expr }, Fix(0L))
    } else if specrepp(expr).truthy() {
      expr = specdisrep(expr)
    } else {
      break
    }
  }
  let pairs = mapcar(z => apply1hack(z, n_starrule), cdr(expr))
  let mut max : Value = Fix(0L)
  for l in pairs.iter() {
    max = num_max(max, cdr(l))
  }
  expr = simplifya(cons(delsimp(car(expr)), mapcar(x => car(x), pairs)), t)
  if num_eq(max, symval(q_d_maxapplyheight)) {
    return cons(expr, max)
  }
  expr = rule_apply(n_starrule, expr)
  cons(expr, one_plus(max))
}

///|
fn n_starrulechk(n_starrule : Value) -> Value raise {
  if symbolp(n_starrule) && !fboundp(n_starrule) && mfboundp(n_starrule) is Nil {
    merr("apply1: no such rule: ~:M", [n_starrule])
  } else {
    Nil
  }
}

///|
fn rule_apply(n_starrule : Value, expr : Value) -> Value raise {
  let mut expr = expr
  while true {
    let (ans, rule_hit) = matcom__mcall_mv(n_starrule, [expr])
    if rule_hit.truthy() && alike1(ans, expr) is Nil {
      expr = ans
    } else {
      return expr
    }
  }
  expr
}

///|
fn d_apply2(l : Value) -> Value raise {
  let l = cdr(l)
  let rulelist = cdr(l)
  apply2(rulelist, meval(car(l)), Fix(0L))
}

///|
fn apply2(rulelist : Value, expr : Value, depth : Value) -> Value raise {
  if num_gt(depth, symval(q_d_maxapplydepth)) {
    return expr
  }
  let mut expr = expr
  let mut ruleptr = rulelist
  while true {
    // b
    if ruleptr is Nil {
      if atom(expr) {
        return expr
      } else if eq(caar(expr), q_mrat) {
        expr = ratdisrep(expr)
        continue
      } else {
        let d1 = one_plus(depth)
        return simplifya(
          cons(
            delsimp(car(expr)),
            mapcar(z => apply2(rulelist, z, d1), cdr(expr)),
          ),
          t,
        )
      }
    }
    let (ans, rule_hit) = matcom__mcall_mv(car(ruleptr), [expr])
    if rule_hit.truthy() {
      expr = ans
      ruleptr = rulelist // a
    } else {
      ruleptr = cdr(ruleptr)
    }
  }
  expr
}

///|
fn d_applyb2(l : Value) -> Value raise {
  let l = cdr(l)
  let rulelist = cdr(l)
  car(apply2hack(rulelist, meval(car(l))))
}

///|
fn apply2hack(rulelist : Value, e : Value) -> Value raise {
  if atom(e) {
    return cons(apply2(rulelist, e, Fix(-1L)), Fix(0L))
  } else if specrepp(e).truthy() {
    return apply2hack(rulelist, specdisrep(e))
  }
  let pairs = mapcar(x => apply2hack(rulelist, x), cdr(e))
  let mut max : Value = Fix(0L)
  for l in pairs.iter() {
    max = num_max(max, cdr(l))
  }
  let e = simplifya(cons(delsimp(car(e)), mapcar(x => car(x), pairs)), t)
  if num_eq(max, symval(q_d_maxapplyheight)) {
    cons(e, max)
  } else {
    cons(apply2(rulelist, e, Fix(-1L)), one_plus(max))
  }
}
