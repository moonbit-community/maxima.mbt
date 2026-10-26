// Port of share/contrib/gentran/allgentran.lisp (part 3): the Lisp ->
// Ratfor (lsprat.l) and Lisp -> C (lspc.l) translations, the user commands
// and control functions (intrfc.l), the preprocessor (pre.l) and the
// file's top-level forms.

// ---------------------------------------------------------------------------
// lsprat.l: Lisp -> Ratfor translation

///|
fn ratcode(forms : Value) -> Value raise {
  mapcan(
    f => if atom(f) {
      if equal(f, q_d_begin_group) {
        mkfratbegingp()
      } else if equal(f, q_d_end_group) {
        mkfratendgp()
      } else {
        ratexpgen(f)
      }
    } else if lispstmtp(f).truthy() || lispstmtgpp(f).truthy() {
      if symval(q_n_stargendecs).truthy() {
        let d = ratdecs(symtabget(q_ear_main, q_ear_decs))
        let r = append(d, ratstmt(f))
        symtabrem(q_ear_main, q_ear_decs) |> ignore
        r
      } else {
        ratstmt(f)
      }
    } else if lispdefp(f).truthy() {
      ratsubprog(f)
    } else {
      ratexpgen(f)
    },
    forms,
  )
}

///|
fn ratsubprog(def : Value) -> Value raise {
  let (type_, stype, name, params, body) = allgentran__subprog_parts(def)
  let mut r = mkfratsubprogdec(type_, stype, name, params)
  if symval(q_n_stargendecs).truthy() {
    r = append(r, ratdecs(symtabget(name, q_ear_decs)))
  }
  r = append(r, mapcan(s => ratstmt(s), body))
  if symval(q_n_stargendecs).truthy() {
    symtabrem(name, Nil) |> ignore
    symtabrem(name, q_ear_decs) |> ignore
  }
  r
}

///|
fn ratdecs(decs : Value) -> Value raise {
  mapcan(tl => mkfratdec(car(tl), cdr(tl)), formtypelists(decs))
}

///|
fn ratexpgen(exp_ : Value) -> Value raise {
  if symval(q_d_dblfloat).truthy() {
    mapcar(n => dbl(n), ratexpgen1(exp_, Fix(0L)))
  } else {
    ratexpgen1(exp_, Fix(0L))
  }
}

///|
fn ratexpgen1(exp_ : Value, wtin : Value) -> Value raise {
  if atom(exp_) {
    list1(ratforname(exp_))
  } else if eq(car(exp_), q_literal) {
    ratliteral(exp_)
  } else if onep(int(length(exp_))).truthy() {
    exp_
  } else if memq(car(exp_), list2(q_minus, q_not)).truthy() {
    allgentran__unary(exp_, wtin, ratexpgen1, ratforop, ratforprecedence)
  } else if allgentran__arith_or_log_op_p(car(exp_)) {
    allgentran__infix(exp_, wtin, ratexpgen1, ratforop, ratforprecedence)
  } else {
    allgentran__call(exp_, ratexpgen1)
  }
}

///|
fn ratforname(name : Value) -> Value raise {
  if symbolp(name) {
    let n = get(name, q_ear_ratforname)
    if n.truthy() {
      n
    } else {
      name
    }
  } else {
    name
  }
}

///|
fn ratforop(op : Value) -> Value raise {
  let o = get(op, q_ear_ratforop)
  if o.truthy() {
    o
  } else {
    op
  }
}

///|
fn ratforprecedence(op : Value) -> Value raise {
  let p = get(op, q_ear_ratforprecedence)
  if p.truthy() {
    p
  } else {
    Fix(9L)
  }
}

///|
fn ratstmt(stmt : Value) -> Value raise {
  if null(stmt) {
    Nil
  } else if equal(stmt, q_d_begin_group) {
    mkfratbegingp()
  } else if equal(stmt, q_d_end_group) {
    mkfratendgp()
  } else if lisplabelp(stmt).truthy() {
    ratstmtno(stmt)
  } else if equal(car(stmt), q_literal) {
    ratliteral(stmt)
  } else if lispreadp(stmt).truthy() {
    ratread(stmt)
  } else if lispassignp(stmt).truthy() {
    ratassign(stmt)
  } else if lispprintp(stmt).truthy() {
    ratwrite(stmt)
  } else if lispcondp(stmt).truthy() {
    ratif(stmt)
  } else if lispbreakp(stmt).truthy() {
    ratbreak(stmt)
  } else if lispgop(stmt).truthy() {
    ratgoto(stmt)
  } else if lispreturnp(stmt).truthy() {
    ratreturn(stmt)
  } else if lispstopp(stmt).truthy() {
    ratstop(stmt)
  } else if lispendp(stmt).truthy() {
    ratend(stmt)
  } else if lispdop(stmt).truthy() {
    ratloop(stmt)
  } else if lispstmtgpp(stmt).truthy() {
    ratstmtgp(stmt)
  } else if lispdefp(stmt).truthy() {
    ratsubprog(stmt)
  } else if lispcallp(stmt).truthy() {
    ratcall(stmt)
  } else {
    Nil
  }
}

///|
fn ratassign(stmt : Value) -> Value raise {
  mkfratassign(cadr(stmt), caddr(stmt))
}

///|
fn ratbreak(stmt : Value) -> Value raise {
  ignore(stmt)
  mkfratbreak()
}

///|
fn ratcall(stmt : Value) -> Value raise {
  mkfratcall(car(stmt), cdr(stmt))
}

///|
fn ratdo(
  var_ : Value,
  lo : Value,
  nextexp : Value,
  exitcond : Value,
  body : Value,
) -> Value raise {
  let hi = car(delete1(q_greaterp, delete1(q_lessp, delete1(var_, exitcond))))
  let incr = car(delete1(q_plus, delete1(var_, nextexp)))
  let mut r = mkfratdo(var_, lo, hi, incr)
  indentratlevel(Fix(1L)) |> ignore
  r = append(r, ratstmt(body))
  indentratlevel(Fix(-1L)) |> ignore
  r
}

///|
fn ratend(stmt : Value) -> Value raise {
  ignore(stmt)
  mkfratend()
}

///|
fn ratforfor(
  var_ : Value,
  lo : Value,
  nextexp : Value,
  cond : Value,
  body : Value,
) -> Value raise {
  let cond = if cond.truthy() { list2(q_not, cond) } else { cond }
  let mut r = if equal(nextexp, list1(Nil)) {
    mkfratfor(var_, lo, cond, var_, Nil)
  } else if nextexp.truthy() {
    mkfratfor(var_, lo, cond, var_, nextexp)
  } else {
    mkfratfor(var_, lo, cond, Nil, Nil)
  }
  indentratlevel(Fix(1L)) |> ignore
  r = append(r, ratstmt(body))
  indentratlevel(Fix(-1L)) |> ignore
  r
}

///|
fn ratgoto(stmt : Value) -> Value raise {
  mkfratgo(allgentran__label_stmtno(cadr(stmt)))
}

///|
/// The statement group of the statements of a cond clause: a lone
/// one-clause cond is wrapped so that a following else is unambiguous.
fn allgentran__clause_stmt(stmts : Value) -> Value raise {
  let st = seqtogp(stmts)
  if listp(st) && equal(car(st), q_cond) && length(st) == 2 {
    mkstmtgp(Fix(0L), list1(st))
  } else {
    st
  }
}

///|
fn ratif(stmt : Value) -> Value raise {
  let mut r = mkfratif(caadr(stmt))
  indentratlevel(Fix(1L)) |> ignore
  r = append(r, ratstmt(allgentran__clause_stmt(cdadr(stmt))))
  indentratlevel(Fix(-1L)) |> ignore
  let mut stmt = cdr(stmt)
  while true {
    stmt = cdr(stmt)
    if !(stmt.truthy() && !eq(caar(stmt), t)) {
      break
    }
    r = append(r, mkfratelseif(caar(stmt)))
    indentratlevel(Fix(1L)) |> ignore
    r = append(r, ratstmt(allgentran__clause_stmt(cdar(stmt))))
    indentratlevel(Fix(-1L)) |> ignore
  }
  if stmt.truthy() {
    r = append(r, mkfratelse())
    indentratlevel(Fix(1L)) |> ignore
    r = append(r, ratstmt(allgentran__clause_stmt(cdar(stmt))))
    indentratlevel(Fix(-1L)) |> ignore
  }
  r
}

///|
fn ratliteral(stmt : Value) -> Value raise {
  mkfratliteral(cdr(stmt))
}

///|
fn ratloop(stmt : Value) -> Value raise {
  if complexdop(stmt).truthy() {
    return ratstmt(seqtogp(simplifydo(stmt)))
  }
  let (var_, lo, nextexp, exitcond) = allgentran__loop_parts(stmt)
  let body = seqtogp(cdddr(stmt))
  if allgentran__do_loop_p(var_, lo, nextexp, exitcond) {
    ratdo(var_, lo, nextexp, exitcond, body)
  } else if exitcond.truthy() && !var_.truthy() {
    ratwhile(exitcond, body)
  } else if allgentran__repeat_loop_p(var_, lo, nextexp, exitcond) {
    ratrepeat(body, nextexp)
  } else {
    ratforfor(var_, lo, nextexp, exitcond, body)
  }
}

///|
fn ratread(stmt : Value) -> Value raise {
  mkfratread(cadr(stmt))
}

///|
fn ratrepeat(body : Value, exitcond : Value) -> Value raise {
  let mut r = mkfratrepeat()
  indentratlevel(Fix(1L)) |> ignore
  r = append(r, ratstmt(body))
  indentratlevel(Fix(-1L)) |> ignore
  append(r, mkfratuntil(exitcond))
}

///|
fn ratreturn(stmt : Value) -> Value raise {
  mkfratreturn(cadr(stmt))
}

///|
fn ratstmtgp(stmtgp : Value) -> Value raise {
  let stmts = if equal(car(stmtgp), q_progn) {
    cdr(stmtgp)
  } else {
    cddr(stmtgp)
  }
  let mut r = mkfratbegingp()
  indentratlevel(Fix(1L)) |> ignore
  r = append(r, mapcan(stmt => ratstmt(stmt), stmts))
  indentratlevel(Fix(-1L)) |> ignore
  append(r, mkfratendgp())
}

///|
fn ratstmtno(label : Value) -> Value raise {
  mkfratcontinue(allgentran__label_stmtno(label))
}

///|
fn ratstop(stmt : Value) -> Value raise {
  ignore(stmt)
  mkfratstop()
}

///|
fn ratwhile(cond : Value, body : Value) -> Value raise {
  let cond = if cond.truthy() { list2(q_not, cond) } else { cond }
  let mut r = mkfratwhile(cond)
  indentratlevel(Fix(1L)) |> ignore
  r = append(r, ratstmt(body))
  indentratlevel(Fix(-1L)) |> ignore
  r
}

///|
fn ratwrite(stmt : Value) -> Value raise {
  mkfratwrite(cdr(stmt))
}

///|
fn mkfratassign(lhs : Value, rhs : Value) -> Value raise {
  append(
    append(cons(mkrattab(), ratexpgen(lhs)), cons(q_op_eq, ratexpgen(rhs))),
    list1(mkterpri()),
  )
}

///|
fn mkfratbegingp() -> Value raise {
  list3(mkrattab(), q_op_lc, mkterpri())
}

///|
fn mkfratbreak() -> Value raise {
  list3(mkrattab(), q_break, mkterpri())
}

///|
fn mkfratcall(fname : Value, params : Value) -> Value raise {
  let mut params = params
  if params.truthy() {
    params = append(
      append(list1(q_op_u0028), allgentran__params(params, ratexpgen)),
      list1(q_op_u0029),
    )
  }
  append(
    append(list3(mkrattab(), q_call, q_op_sp), ratexpgen(fname)),
    append(params, list1(mkterpri())),
  )
}

///|
fn mkfratcontinue(stmtno : Value) -> Value raise {
  list([stmtno, q_op_sp, mkrattab(), q_continue, mkterpri()])
}

///|
fn mkfratdec(type_ : Value, varlist : Value) -> Value raise {
  let type_ = if type_.truthy() { type_ } else { q_dimension }
  let varlist = allgentran__params(varlist, ratexpgen)
  if implicitp(type_).truthy() {
    append(
      list([mkrattab(), type_, q_op_sp, q_op_u0028]),
      append(varlist, list2(q_op_u0029, mkterpri())),
    )
  } else {
    append(list3(mkrattab(), type_, q_op_sp), aconc(varlist, mkterpri()))
  }
}

///|
fn mkfratdo(var_ : Value, lo : Value, hi : Value, incr : Value) -> Value raise {
  let mut incr = incr
  if onep(incr).truthy() {
    incr = Nil
  } else if incr.truthy() {
    incr = cons(q_op_cm, ratexpgen(incr))
  }
  append(
    append(
      append(list3(mkrattab(), q_do, q_op_sp), ratexpgen(var_)),
      append(cons(q_op_eq, ratexpgen(lo)), cons(q_op_cm, ratexpgen(hi))),
    ),
    append(incr, list1(mkterpri())),
  )
}

///|
fn mkfratelse() -> Value raise {
  list3(mkrattab(), q_else, mkterpri())
}

///|
fn mkfratelseif(exp_ : Value) -> Value raise {
  append(
    append(
      list([mkrattab(), q_else, q_op_sp, q_if, q_op_sp, q_op_u0028]),
      ratexpgen(exp_),
    ),
    list2(q_op_u0029, mkterpri()),
  )
}

///|
fn mkfratend() -> Value raise {
  list3(mkrattab(), q_end, mkterpri())
}

///|
fn mkfratendgp() -> Value raise {
  list3(mkrattab(), q_op_rc, mkterpri())
}

///|
/// The tokens of `for (var1=lo; cond; var2=nextexp)`, translated by tr;
/// shared by Ratfor and C.
fn allgentran__for_header(
  tab : Value,
  var1 : Value,
  lo : Value,
  cond : Value,
  var2 : Value,
  nextexp : Value,
  tr : (Value) -> Value raise,
) -> Value raise {
  let mut var1 = var1
  let mut cond = cond
  let mut var2 = var2
  if var1.truthy() {
    var1 = append(tr(var1), cons(q_op_eq, tr(lo)))
  }
  if cond.truthy() {
    cond = tr(cond)
  }
  if var2.truthy() {
    var2 = append(tr(var2), cons(q_op_eq, tr(nextexp)))
  }
  let semicolon = symval(q_semicolon)
  append(
    append(append(list([tab, q_for, q_op_sp, q_op_u0028]), var1), cons(semicolon, cond)),
    append(cons(semicolon, var2), list2(q_op_u0029, mkterpri())),
  )
}

///|
fn mkfratfor(
  var1 : Value,
  lo : Value,
  cond : Value,
  var2 : Value,
  nextexp : Value,
) -> Value raise {
  allgentran__for_header(mkrattab(), var1, lo, cond, var2, nextexp, ratexpgen)
}

///|
fn mkfratgo(stmtno : Value) -> Value raise {
  list([mkrattab(), q_goto, q_op_sp, stmtno, mkterpri()])
}

///|
fn mkfratif(exp_ : Value) -> Value raise {
  append(
    append(list([mkrattab(), q_if, q_op_sp, q_op_u0028]), ratexpgen(exp_)),
    list2(q_op_u0029, mkterpri()),
  )
}

///|
fn mkfratliteral(args : Value) -> Value raise {
  mapcan(
    a => if equal(a, q_d_tab) {
      list1(mkrattab())
    } else if equal(a, q_d_cr) {
      list1(mkterpri())
    } else if listp(a) {
      ratexpgen(a)
    } else {
      list1(a)
    },
    args,
  )
}

///|
fn mkfratread(var_ : Value) -> Value raise {
  append(
    list([mkrattab(), q_read, q_op_u0028_star_cm_star_u0029, q_op_sp]),
    append(ratexpgen(var_), list1(mkterpri())),
  )
}

///|
fn mkfratrepeat() -> Value raise {
  list3(mkrattab(), q_repeat, mkterpri())
}

///|
fn mkfratreturn(exp_ : Value) -> Value raise {
  if exp_.truthy() {
    append(
      append(list3(mkrattab(), q_return, q_op_u0028), ratexpgen(exp_)),
      list2(q_op_u0029, mkterpri()),
    )
  } else {
    list3(mkrattab(), q_return, mkterpri())
  }
}

///|
fn mkfratstop() -> Value raise {
  list3(mkrattab(), q_stop, mkterpri())
}

///|
fn mkfratsubprogdec(
  type_ : Value,
  stype : Value,
  name : Value,
  params : Value,
) -> Value raise {
  let mut params = params
  if params.truthy() {
    params = aconc(
      cons(q_op_u0028, allgentran__params(params, ratexpgen)),
      q_op_u0029,
    )
  }
  let head = if type_.truthy() {
    list([mkrattab(), type_, q_op_sp, stype, q_op_sp])
  } else {
    list3(mkrattab(), stype, q_op_sp)
  }
  append(append(head, ratexpgen(name)), aconc(params, mkterpri()))
}

///|
fn mkfratuntil(logexp : Value) -> Value raise {
  append(
    list([mkrattab(), q_until, q_op_sp, q_op_u0028]),
    append(ratexpgen(logexp), list2(q_op_u0029, mkterpri())),
  )
}

///|
fn mkfratwhile(exp_ : Value) -> Value raise {
  append(
    append(list([mkrattab(), q_while, q_op_sp, q_op_u0028]), ratexpgen(exp_)),
    list2(q_op_u0029, mkterpri()),
  )
}

///|
fn mkfratwrite(arglist : Value) -> Value raise {
  append(
    append(
      list([mkrattab(), q_write, q_op_u0028_star_cm_star_u0029, q_op_sp]),
      allgentran__params(mapcar(a => quotstring(a), arglist), ratexpgen),
    ),
    list1(mkterpri()),
  )
}

///|
fn mkrattab() -> Value raise {
  list2(q_rattab, symval(q_d_ratcurrind))
}

///|
fn indentratlevel(n : Value) -> Value raise {
  set(
    q_d_ratcurrind,
    num_add(symval(q_d_ratcurrind), num_mul(n, symval(q_d_tablen))),
  )
}

// ---------------------------------------------------------------------------
// lspc.l: Lisp -> C translation

///|
fn ccode(forms : Value) -> Value raise {
  mapcan(
    f => if atom(f) {
      if equal(f, q_d_begin_group) {
        mkfcbegingp()
      } else if equal(f, q_d_end_group) {
        mkfcendgp()
      } else {
        cexp_(f)
      }
    } else if lispstmtp(f).truthy() || lispstmtgpp(f).truthy() {
      if symval(q_n_stargendecs).truthy() {
        let d = cdecs(symtabget(q_ear_main, q_ear_decs))
        let r = append(d, cstmt(f))
        symtabrem(q_ear_main, q_ear_decs) |> ignore
        r
      } else {
        cstmt(f)
      }
    } else if lispdefp(f).truthy() {
      cproc(f)
    } else {
      cexp_(f)
    },
    forms,
  )
}

///|
fn cproc(def : Value) -> Value raise {
  let name = cadr(def)
  let mut body = cdddr(def)
  if body.truthy() && equal(body, list1(Nil)) {
    body = Nil
  }
  if onep(int(length(body))).truthy() && lispstmtgpp(car(body)).truthy() {
    body = cdar(body)
    if null(car(body)) {
      body = cdr(body)
    }
  }
  let mut type_ = symtabget(name, name)
  if type_.truthy() {
    type_ = cadr(type_)
    symtabrem(name, name) |> ignore
  }
  let mut params = symtabget(name, q_ear_params)
  if !params.truthy() {
    params = caddr(def)
  }
  symtabrem(name, q_ear_params) |> ignore
  let mut paramtypes : Value = Nil
  let mut vartypes : Value = Nil
  for dec in symtabget(name, q_ear_decs).iter() {
    if member(car(dec), params).truthy() {
      paramtypes = aconc(paramtypes, dec)
    } else {
      vartypes = aconc(vartypes, dec)
    }
  }
  let mut r = append(mkfcprocdec(type_, name, params), cdecs(paramtypes))
  if body.truthy() {
    r = append(r, mkfcbegingp())
    indentclevel(Fix(1L)) |> ignore
    if symval(q_n_stargendecs).truthy() {
      r = append(r, cdecs(vartypes))
    }
    r = append(r, mapcan(s => cstmt(s), body))
    indentclevel(Fix(-1L)) |> ignore
    r = append(r, mkfcendgp())
  }
  if symval(q_n_stargendecs).truthy() {
    symtabrem(name, Nil) |> ignore
    symtabrem(name, q_ear_decs) |> ignore
  }
  r
}

///|
fn cdecs(decs : Value) -> Value raise {
  mapcan(tl => mkfcdec(car(tl), cdr(tl)), formtypelists(decs))
}

///|
fn cexp_(exp_ : Value) -> Value raise {
  if symval(q_d_dblfloat).truthy() {
    mapcar(n => dbl(n), cexp1(exp_, Fix(0L)))
  } else {
    cexp1(exp_, Fix(0L))
  }
}

///|
fn cexp1(exp_ : Value, wtin : Value) -> Value raise {
  if atom(exp_) {
    list1(cname(exp_))
  } else if eq(car(exp_), q_literal) {
    cliteral(exp_)
  } else if memq(car(exp_), list2(q_minus, q_not)).truthy() {
    allgentran__unary(exp_, wtin, cexp1, cop, cprecedence)
  } else if eq(car(exp_), q_expt) {
    append(
      cons(q_pow, cons(q_op_u0028, cexp1(cadr(exp_), Fix(0L)))),
      aconc(cons(q_op_cm, cexp1(caddr(exp_), Fix(0L))), q_op_u0029),
    )
  } else if allgentran__arith_or_log_op_p(car(exp_)) {
    allgentran__infix(exp_, wtin, cexp1, cop, cprecedence)
  } else if arrayeltp(exp_).truthy() {
    let mut res = list1(car(exp_))
    let mut exp_ = cdr(exp_)
    while exp_.truthy() {
      res = append(res, aconc(cons(q_op_lb, cexp1(car(exp_), Fix(0L))), q_op_rb))
      exp_ = cdr(exp_)
    }
    res
  } else if onep(int(length(exp_))).truthy() {
    aconc(aconc(exp_, q_op_u0028), q_op_u0029)
  } else {
    allgentran__call(exp_, cexp1)
  }
}

///|
fn cname(name : Value) -> Value raise {
  if symbolp(name) {
    let n = get(name, q_ear_cname)
    if n.truthy() {
      n
    } else {
      name
    }
  } else {
    name
  }
}

///|
fn cop(op : Value) -> Value raise {
  let o = get(op, q_ear_cop)
  if o.truthy() {
    o
  } else {
    op
  }
}

///|
fn cprecedence(op : Value) -> Value raise {
  let p = get(op, q_ear_cprecedence)
  if p.truthy() {
    p
  } else {
    Fix(8L)
  }
}

///|
fn cstmt(stmt : Value) -> Value raise {
  if null(stmt) {
    Nil
  } else if equal(stmt, q_d_begin_group) {
    mkfcbegingp()
  } else if equal(stmt, q_d_end_group) {
    mkfcendgp()
  } else if lisplabelp(stmt).truthy() {
    clabel(stmt)
  } else if equal(car(stmt), q_literal) {
    cliteral(stmt)
  } else if lispassignp(stmt).truthy() {
    cassign(stmt)
  } else if lispcondp(stmt).truthy() {
    cif(stmt)
  } else if lispbreakp(stmt).truthy() {
    cbreak(stmt)
  } else if lispgop(stmt).truthy() {
    cgoto(stmt)
  } else if lispreturnp(stmt).truthy() {
    creturn(stmt)
  } else if lispstopp(stmt).truthy() {
    cexit(stmt)
  } else if lispdop(stmt).truthy() {
    cloop(stmt)
  } else if lispstmtgpp(stmt).truthy() {
    cstmtgp(stmt)
  } else if lispdefp(stmt).truthy() {
    cproc(stmt)
  } else {
    cexpstmt(stmt)
  }
}

///|
fn cassign(stmt : Value) -> Value raise {
  mkfcassign(cadr(stmt), caddr(stmt))
}

///|
fn cbreak(stmt : Value) -> Value raise {
  ignore(stmt)
  mkfcbreak()
}

///|
fn cexit(stmt : Value) -> Value raise {
  ignore(stmt)
  mkfcexit()
}

///|
fn cexpstmt(exp_ : Value) -> Value raise {
  append(cons(mkctab(), cexp_(exp_)), list2(symval(q_semicolon), mkterpri()))
}

///|
fn cfor(
  var_ : Value,
  lo : Value,
  nextexp : Value,
  cond : Value,
  body : Value,
) -> Value raise {
  let cond = if cond.truthy() { list2(q_not, cond) } else { cond }
  let mut r = if equal(nextexp, list1(Nil)) {
    mkfcfor(var_, lo, cond, var_, Nil)
  } else if nextexp.truthy() {
    mkfcfor(var_, lo, cond, var_, nextexp)
  } else {
    mkfcfor(var_, lo, cond, Nil, Nil)
  }
  indentclevel(Fix(1L)) |> ignore
  r = append(r, cstmt(body))
  indentclevel(Fix(-1L)) |> ignore
  r
}

///|
fn cgoto(stmt : Value) -> Value raise {
  mkfcgo(cadr(stmt))
}

///|
fn cif(stmt : Value) -> Value raise {
  let mut r = mkfcif(caadr(stmt))
  indentclevel(Fix(1L)) |> ignore
  r = append(r, cstmt(allgentran__clause_stmt(cdadr(stmt))))
  indentclevel(Fix(-1L)) |> ignore
  let mut stmt = cdr(stmt)
  while true {
    stmt = cdr(stmt)
    if !(stmt.truthy() && !eq(caar(stmt), t)) {
      break
    }
    r = append(r, mkfcelseif(caar(stmt)))
    indentclevel(Fix(1L)) |> ignore
    r = append(r, cstmt(allgentran__clause_stmt(cdar(stmt))))
    indentclevel(Fix(-1L)) |> ignore
  }
  if stmt.truthy() {
    r = append(r, mkfcelse())
    indentclevel(Fix(1L)) |> ignore
    r = append(r, cstmt(allgentran__clause_stmt(cdar(stmt))))
    indentclevel(Fix(-1L)) |> ignore
  }
  r
}

///|
fn clabel(label : Value) -> Value raise {
  mkfclabel(label)
}

///|
fn cliteral(stmt : Value) -> Value raise {
  mkfcliteral(cdr(stmt))
}

///|
fn cloop(stmt : Value) -> Value raise {
  if complexdop(stmt).truthy() {
    return cstmt(seqtogp(simplifydo(stmt)))
  }
  let (var_, lo, nextexp, exitcond) = allgentran__loop_parts(stmt)
  let body = seqtogp(cdddr(stmt))
  if exitcond.truthy() && !var_.truthy() {
    cwhile(exitcond, body)
  } else if allgentran__repeat_loop_p(var_, lo, nextexp, exitcond) {
    crepeat(body, nextexp)
  } else {
    cfor(var_, lo, nextexp, exitcond, body)
  }
}

///|
fn crepeat(body : Value, logexp : Value) -> Value raise {
  let mut r = mkfcdo()
  indentclevel(Fix(1L)) |> ignore
  r = append(r, cstmt(body))
  indentclevel(Fix(-1L)) |> ignore
  append(r, mkfcdowhile(list2(q_not, logexp)))
}

///|
fn creturn(stmt : Value) -> Value raise {
  mkfcreturn(cadr(stmt))
}

///|
fn cstmtgp(stmtgp : Value) -> Value raise {
  let stmts = if equal(car(stmtgp), q_progn) {
    cdr(stmtgp)
  } else {
    cddr(stmtgp)
  }
  let mut r = mkfcbegingp()
  indentclevel(Fix(1L)) |> ignore
  r = append(r, mapcan(stmt => cstmt(stmt), stmts))
  indentclevel(Fix(-1L)) |> ignore
  append(r, mkfcendgp())
}

///|
fn cwhile(cond : Value, body : Value) -> Value raise {
  let cond = if cond.truthy() { list2(q_not, cond) } else { cond }
  let mut r = mkfcwhile(cond)
  indentclevel(Fix(1L)) |> ignore
  r = append(r, cstmt(body))
  indentclevel(Fix(-1L)) |> ignore
  r
}

///|
fn mkfcassign(lhs : Value, rhs : Value) -> Value raise {
  append(
    append(cons(mkctab(), cexp_(lhs)), cons(q_op_eq, cexp_(rhs))),
    list2(symval(q_semicolon), mkterpri()),
  )
}

///|
fn mkfcbegingp() -> Value raise {
  list3(mkctab(), q_op_lc, mkterpri())
}

///|
fn mkfcbreak() -> Value raise {
  list([mkctab(), q_break, symval(q_semicolon), mkterpri()])
}

///|
fn mkfcdec(type_ : Value, varlist : Value) -> Value raise {
  let varlist = mapcar(
    v => if atom(v) {
      v
    } else {
      cons(car(v), mapcar(dim => num_add(dim, Fix(1L)), cdr(v)))
    },
    varlist,
  )
  append(
    cons(mkctab(), cons(type_, cons(q_op_sp, allgentran__params(varlist, cexp_)))),
    list2(symval(q_semicolon), mkterpri()),
  )
}

///|
fn mkfcdo() -> Value raise {
  list3(mkctab(), q_do, mkterpri())
}

///|
fn mkfcdowhile(exp_ : Value) -> Value raise {
  append(
    append(list([mkctab(), q_while, q_op_sp, q_op_u0028]), cexp_(exp_)),
    list3(q_op_u0029, symval(q_semicolon), mkterpri()),
  )
}

///|
fn mkfcelse() -> Value raise {
  list3(mkctab(), q_else, mkterpri())
}

///|
fn mkfcelseif(exp_ : Value) -> Value raise {
  append(
    append(
      list([mkctab(), q_else, q_op_sp, q_if, q_op_sp, q_op_u0028]),
      cexp_(exp_),
    ),
    list2(q_op_u0029, mkterpri()),
  )
}

///|
fn mkfcendgp() -> Value raise {
  list3(mkctab(), q_op_rc, mkterpri())
}

///|
fn mkfcexit() -> Value raise {
  list([
    mkctab(),
    q_exit,
    q_op_u0028,
    Fix(0L),
    q_op_u0029,
    symval(q_semicolon),
    mkterpri(),
  ])
}

///|
fn mkfcfor(
  var1 : Value,
  lo : Value,
  cond : Value,
  var2 : Value,
  nextexp : Value,
) -> Value raise {
  allgentran__for_header(mkctab(), var1, lo, cond, var2, nextexp, cexp_)
}

///|
fn mkfcgo(label : Value) -> Value raise {
  list([mkctab(), q_goto, q_op_sp, label, symval(q_semicolon), mkterpri()])
}

///|
fn mkfcif(exp_ : Value) -> Value raise {
  append(
    append(list([mkctab(), q_if, q_op_sp, q_op_u0028]), cexp_(exp_)),
    list2(q_op_u0029, mkterpri()),
  )
}

///|
fn mkfclabel(label : Value) -> Value raise {
  list3(label, q_kw_, mkterpri())
}

///|
fn mkfcliteral(args : Value) -> Value raise {
  mapcan(
    a => if equal(a, q_d_tab) {
      list1(mkctab())
    } else if equal(a, q_d_cr) {
      list1(mkterpri())
    } else if listp(a) {
      cexp_(a)
    } else {
      list1(a)
    },
    args,
  )
}

///|
fn mkfcprocdec(type_ : Value, name : Value, params : Value) -> Value raise {
  let params = aconc(
    cons(q_op_u0028, allgentran__params(params, cexp_)),
    q_op_u0029,
  )
  if type_.truthy() {
    append(
      cons(mkctab(), cons(type_, cons(q_op_sp, cexp_(name)))),
      aconc(params, mkterpri()),
    )
  } else {
    append(cons(mkctab(), cexp_(name)), aconc(params, mkterpri()))
  }
}

///|
fn mkfcreturn(exp_ : Value) -> Value raise {
  if exp_.truthy() {
    append(
      append(list3(mkctab(), q_return, q_op_u0028), cexp_(exp_)),
      list3(q_op_u0029, symval(q_semicolon), mkterpri()),
    )
  } else {
    list([mkctab(), q_return, symval(q_semicolon), mkterpri()])
  }
}

///|
fn mkfcwhile(exp_ : Value) -> Value raise {
  append(
    append(list([mkctab(), q_while, q_op_sp, q_op_u0028]), cexp_(exp_)),
    list2(q_op_u0029, mkterpri()),
  )
}

///|
fn mkctab() -> Value raise {
  list2(q_ctab, symval(q_d_ccurrind))
}

///|
fn indentclevel(n : Value) -> Value raise {
  set(
    q_d_ccurrind,
    num_add(symval(q_d_ccurrind), num_mul(n, symval(q_d_tablen))),
  )
}

// ---------------------------------------------------------------------------
// intrfc.l: command parsing routines & control functions
//
// The functions callable from Maxima prepend genoutpath to output file
// names.

///|
/// gentran(stmt1, stmt2, ..., stmtn {, [f1, f2, ..., fm]})
///   -->  (gentran (stmt1 ... stmtn) (f1 ... fm))
fn d_gentran(forms : Value) -> Value raise {
  let mut forms = reverse(forms)
  let mut flist : Value = Nil
  if listp(car(forms)) && listp(caar(forms)) && equal(car(caar(forms)), q_mlist) {
    flist = cdar(forms)
    forms = cdr(forms)
  }
  forms = cdr(reverse(forms))
  gentran(forms, mapcar(f => outpath(f), flist))
}

///|
/// gentranout(f1, ..., fn)  -->  (gentranoutpush (f1 ... fn) t)
fn d_gentranout(flist : Value) -> Value raise {
  gentranoutpush(mapcar(f => outpath(f), flist), t)
}

///|
fn gentranout(flist : Value) -> Value raise {
  gentranoutpush(flist, t)
}

///|
fn d_gentranshut(flist : Value) -> Value raise {
  gentranshut(mapcar(f => outpath(f), flist))
}

///|
/// gentranpush(f1, ..., fn)  -->  (gentranoutpush (f1 ... fn) nil)
fn d_gentranpush(flist : Value) -> Value raise {
  gentranoutpush(mapcar(f => outpath(f), flist), Nil)
}

///|
fn gentranpush(flist : Value) -> Value raise {
  gentranoutpush(flist, Nil)
}

///|
fn d_gentranpop(flist : Value) -> Value raise {
  gentranpop(mapcar(f => outpath(f), flist))
}

///|
/// gentranin(f1, ..., fn {, [f1, ..., fm]})
///   -->  (gentranin (f1 ... fn) (f1 ... fm))
fn d_gentranin(forms : Value) -> Value raise {
  let mut forms = reverse(forms)
  let mut outflist : Value = Nil
  if listp(car(forms)) && listp(caar(forms)) && equal(car(caar(forms)), q_mlist) {
    outflist = cdar(forms)
    forms = cdr(forms)
  }
  forms = reverse(forms)
  gentranin(forms, mapcar(f => outpath(f), outflist))
}

///|
/// Cleanup for when gentranin hangs.
fn d_gentraninshut() -> Value raise {
  popinstk() |> ignore
  q_d_done
}

///|
fn d_gentran_on(flaglist : Value) -> Value raise {
  onoff(flaglist, t)
}

///|
fn on(flaglist : Value) -> Value raise {
  onoff(flaglist, t)
}

///|
fn d_gentran_off(flaglist : Value) -> Value raise {
  onoff(flaglist, Nil)
}

///|
fn gentran_off(flaglist : Value) -> Value raise {
  onoff(flaglist, Nil)
}

///|
fn gentran(forms : Value, flist : Value) -> Value raise {
  let flist = preproc(flist)
  if flist.truthy() {
    gentranoutpush(flist, Nil) |> ignore
  }
  let mut forms = preproc(forms)
  if symval(q_d_gentranparser).truthy() {
    gentranparse(forms) |> ignore
  }
  forms = franz(forms)
  if symval(q_d_gentranseg).truthy() {
    forms = seg(forms)
  }
  let lang = allgentran__lang()
  if eq(lang, q_ratfor) {
    formatrat(ratcode(forms)) |> ignore
  } else if eq(lang, q_c) {
    formatc(ccode(forms)) |> ignore
  } else {
    formatfort(fortcode(forms)) |> ignore
  }
  if flist.truthy() {
    let r = allgentran__currout_value()
    gentranpop(list1(Nil)) |> ignore
    r
  } else {
    allgentran__currout_value()
  }
}

///|
/// Open, [delete,] push.
fn gentranoutpush(flist : Value, outp : Value) -> Value raise {
  let flist = fargstonames(preproc(flist), t)
  if onep(int(length(flist))).truthy() {
    let mut fp = filpr(car(flist), symval(q_ear_outstk))
    if !fp.truthy() {
      fp = mkfilpr(car(flist))
    }
    if outp.truthy() {
      delstk(fp) |> ignore
    }
    pushstk(fp) |> ignore
  } else {
    let fp = mapcar(
      f => {
        let p = filpr(f, symval(q_ear_outstk))
        if p.truthy() {
          p
        } else {
          mkfilpr(f)
        }
      },
      flist,
    )
    if outp.truthy() {
      for p in fp.iter() {
        delstk(p) |> ignore
      }
      delstk(pfilpr(flist, symval(q_ear_outstk))) |> ignore
    }
    pushstk(allgentran__nil_pair()) |> ignore
    if outp.truthy() {
      for p in fp.iter() {
        pushstk(p) |> ignore
      }
    } else {
      for p in fp.iter() {
        if !member(p, symval(q_ear_outstk)).truthy() {
          pushstk(p) |> ignore
        }
      }
    }
    pushstk(cons(Nil, flist)) |> ignore
  }
  resetstk(symval(q_ear_outstk)) |> ignore
  allgentran__currout_value()
}

///|
/// Close, delete, [output to t].
fn gentranshut(flist : Value) -> Value raise {
  let flist = fargstonames(preproc(flist), Nil)
  if onep(int(length(flist))).truthy() {
    let trm = equal(car(symval(q_ear_currout)), car(flist))
    let fp = filpr(car(flist), symval(q_ear_outstk))
    allgentran__close(cdr(fp))
    delstk(fp) |> ignore
    if trm {
      pushstk(symval(q_ear_stdout)) |> ignore
    }
  } else {
    let currout = symval(q_ear_currout)
    let trm = if car(currout).truthy() {
      member(car(currout), flist).truthy()
    } else {
      cdr(currout).iter().all(f => member(f, flist).truthy())
    }
    let fp = mapcar(f => filpr(f, symval(q_ear_outstk)), flist)
    for p in fp.iter() {
      allgentran__close(cdr(p))
    }
    for p in fp.iter() {
      delstk(p) |> ignore
    }
    delstk(pfilpr(flist, symval(q_ear_outstk))) |> ignore
    if trm {
      pushstk(symval(q_ear_stdout)) |> ignore
    }
  }
  resetstk(symval(q_ear_outstk)) |> ignore
  allgentran__currout_value()
}

///|
/// [Close,] delete.
fn gentranpop(flist : Value) -> Value raise {
  let flist = preproc(flist)
  if member(q_d_all, flist).truthy() {
    while length(symval(q_ear_outstk)) > 1 {
      gentranpop(list1(Nil)) |> ignore
    }
    return car(symval(q_ear_currout))
  }
  let flist = fargstonames(flist, Nil)
  if onep(int(length(flist))).truthy() {
    let fp = filpr(car(flist), symval(q_ear_outstk))
    popstk(fp) |> ignore
    if !member(fp, symval(q_ear_outstk)).truthy() {
      allgentran__close(cdr(fp))
    }
  } else {
    let fp = mapcar(f => filpr(f, symval(q_ear_outstk)), flist)
    popstk(pfilpr(flist, symval(q_ear_outstk))) |> ignore
    for p in fp.iter() {
      if !member(p, symval(q_ear_outstk)).truthy() {
        allgentran__close(cdr(p))
      }
    }
  }
  allgentran__currout_value()
}

///|
fn gentranin(inlist : Value, outlist : Value) -> Value raise {
  // no declarations of the temporary variables of a template
  let ogendecs = symval(q_n_stargendecs)
  set(q_n_stargendecs, Nil) |> ignore
  // input files are found with file_search
  let mut inlist = mapcar(f => fsearch(f), inlist)
  inlist = preproc(inlist)
  for inf in inlist.iter() {
    if listp(inf) {
      if !inf.truthy() {
        gentranerr(q_e, inf, Str("file not found in searchpath")) |> ignore
      } else {
        gentranerr(q_e, inf, Str("wrong type of arg")) |> ignore
      }
    } else if !streamp(inf) && !probe_file(lstring(stripdollar(inf))) {
      gentranerr(q_e, inf, Str("nonexistent input file")) |> ignore
    }
  }
  if outlist.truthy() {
    gentranoutpush(outlist, Nil) |> ignore
  }
  for inf in inlist.iter() {
    if equal(inf, car(symval(q_ear_stdin))) {
      pushinstk(symval(q_ear_stdin)) |> ignore
    } else if filpr(inf, symval(q_ear_instk)).truthy() {
      gentranerr(q_e, inf, Str("template file already open for input"))
      |> ignore
    } else {
      let stream = if streamp(inf) {
        inf
      } else {
        open_input_file(lstring(inf))
      }
      pushinstk(cons(inf, stream)) |> ignore
    }
    let lang = allgentran__lang()
    if eq(lang, q_ratfor) {
      procrattem() |> ignore
    } else if eq(lang, q_c) {
      procctem() |> ignore
    } else {
      procforttem() |> ignore
    }
    if cdr(symval(q_ear_currin)).truthy() {
      allgentran__close(cdr(symval(q_ear_currin)))
    }
    popinstk() |> ignore
  }
  set(q_n_stargendecs, ogendecs) |> ignore
  if outlist.truthy() {
    let r = allgentran__currout_value()
    gentranpop(list1(Nil)) |> ignore
    r
  } else {
    allgentran__currout_value()
  }
}

///|
/// Set the switches *flag of flags to onp and run their SIMPFG forms.
fn onoff(flags : Value, onp : Value) -> Value raise {
  for f0 in flags.iter() {
    let flag = stripdollar1(f0)
    let f = implode(cons(Char('*'), exploden(flag)))
    set(f, onp) |> ignore
    let funlist = assoc(onp, get(flag, q_simpfg))
    if funlist.truthy() {
      for form in cdr(funlist).iter() {
        allgentran__eval(form) |> ignore
      }
    }
  }
  q_d_done
}

///|
fn d_tempvar(type_ : Value) -> Value raise {
  tempvar(stripdollar1(type_))
}

///|
fn d_markvar(var_ : Value) -> Value raise {
  markvar(stripdollar1(var_)) |> ignore
  var_
}

///|
fn d_markedvarp(var_ : Value) -> Value raise {
  markedvarp(stripdollar1(var_))
}

///|
fn d_unmarkvar(var_ : Value) -> Value raise {
  unmarkvar(stripdollar1(var_)) |> ignore
  q_d_done
}

///|
fn d_recurunmark(exp_ : Value) -> Value raise {
  if atom(exp_) {
    unmarkvar(stripdollar1(exp_)) |> ignore
  } else {
    for elt in exp_.iter() {
      d_recurunmark(elt) |> ignore
    }
  }
  q_d_done
}

///|
fn d_gendecs(name : Value) -> Value raise {
  gendecs(name)
}

///|
/// File arguments to file names: nil or 0 is the current output, t the
/// terminal, $all every open file.
fn fargstonames(args : Value, openp : Value) -> Value raise {
  let args = mapcan(
    a => if member(a, list2(Nil, Fix(0L))).truthy() {
      let co = symval(q_ear_currout)
      if car(co).truthy() {
        list1(car(co))
      } else {
        copy_list(cdr(co))
      }
    } else if eq(a, t) {
      list1(car(symval(q_ear_stdout)))
    } else if eq(a, q_d_all) {
      mapcan(
        fp => if car(fp).truthy() && !equal(fp, symval(q_ear_stdout)) {
          list1(car(fp))
        } else {
          Nil
        },
        symval(q_ear_outstk),
      )
    } else if atom(a) {
      if openp.truthy() {
        list1(a)
      } else if filpr(a, symval(q_ear_outstk)).truthy() {
        list1(a)
      } else {
        gentranerr(q_w, a, Str("file not open for output"))
      }
    } else {
      gentranerr(q_e, a, Str("wrong type of arg"))
    },
    if listp(args) {
      args
    } else {
      list1(args)
    },
  )
  let mut names : Value = Nil
  for z in args.iter() {
    if !member(z, names).truthy() {
      names = cons(z, names)
    }
  }
  nreverse(names)
}

///|
/// on/off fortran, ratfor, c: translate the statements read from the
/// current input until the switch is turned off.
fn gentranswitch(lang : Value) -> Value raise {
  let hlang = symval(q_d_gentranlang)
  set(q_d_gentranlang, lang) |> ignore
  let flag = implode(cons(Char('*'), exploden(lang)))
  while symval(flag).truthy() {
    let exp_ = gentranswitch1(
      list1(caddr(mread(list2(cdr(symval(q_ear_currin)), Nil)))),
    )
    gentran(exp_, Nil) |> ignore
  }
  set(q_d_gentranlang, hlang)
}

///|
fn gentranswitch1(exp_ : Value) -> Value raise {
  let r = gentranswitch2(exp_)
  if r.truthy() {
    car(r)
  } else {
    r
  }
}

///|
fn gentranswitch2(exp_ : Value) -> Value raise {
  if atom(exp_) {
    list1(exp_)
  } else if listp(car(exp_)) &&
    member(caar(exp_), list2(q_gentran_off, q_d_gentran_off)).truthy() {
    for f in cdr(exp_).iter() {
      onoff(list1(f), Nil) |> ignore
    }
    Nil
  } else {
    list1(mapcan(e => gentranswitch2(e), exp_))
  }
}

///|
/// on/off gendecs; gendecs(subprogname): print the declarations of a
/// subprogram (or of the current one).
fn gendecs(name : Value) -> Value raise {
  let name : Value = if equal(name, Fix(0L)) { Nil } else { name }
  let lang = allgentran__lang()
  if eq(lang, q_ratfor) {
    formatrat(ratdecs(symtabget(name, q_ear_decs))) |> ignore
  } else if eq(lang, q_c) {
    formatc(cdecs(symtabget(name, q_ear_decs))) |> ignore
  } else {
    formatfort(fortdecs(symtabget(name, q_ear_decs))) |> ignore
  }
  symtabrem(name, Nil) |> ignore
  symtabrem(name, q_ear_decs) |> ignore
  q_d_done
}

///|
/// Print assignments for a list of dotted pairs (var . exp).
fn gentranpairs(prs : Value) -> Value raise {
  let lang = allgentran__lang()
  for pr in prs.iter() {
    if eq(lang, q_ratfor) {
      formatrat(mkfratassign(car(pr), cdr(pr))) |> ignore
    } else if eq(lang, q_c) {
      formatc(mkfcassign(car(pr), cdr(pr))) |> ignore
    } else {
      formatfort(mkffortassign(car(pr), cdr(pr))) |> ignore
    }
  }
  Nil
}

// ---------------------------------------------------------------------------
// pre.l: preprocessing

///|
fn preproc(exp_ : Value) -> Value raise {
  let r = preproc1(exp_)
  if r.truthy() {
    car(r)
  } else {
    r
  }
}

///|
fn allgentran__preproc_all(exp_ : Value) -> Value raise {
  mapcan(e => preproc1(e), exp_)
}

///|
fn preproc1(exp_ : Value) -> Value raise {
  if atom(exp_) {
    return list1(exp_)
  }
  if atom(car(exp_)) || listp(caar(exp_)) {
    return list1(allgentran__preproc_all(exp_))
  }
  if symval(q_d_gentranopt).truthy() &&
    macassignp(exp_).truthy() &&
    !macdefp(exp_).truthy() &&
    !macnestassignp(exp_).truthy() &&
    !macmatassignp(exp_).truthy() {
    let exp_ = allgentran__preproc_all(exp_)
    let lhs = cadr(exp_)
    let mut rhs = d_optimize(caddr(exp_))
    if macexpp(rhs).truthy() {
      return list1(list3(list1(q_msetq), lhs, rhs))
    }
    rhs = cdr(rhs)
    let mut tassigns : Value = Nil
    if listp(car(rhs)) && listp(caar(rhs)) && equal(car(caar(rhs)), q_mlist) {
      // the temporary variables of optimize are named by optimvarname
      let tvarname = symval(q_d_tempvarname)
      set(q_d_tempvarname, symval(q_d_optimvarname)) |> ignore
      let tvarlist = cdar(rhs)
      rhs = cdr(rhs)
      let tvartype = getvartype(if atom(lhs) { lhs } else { car(lhs) })
      for tv in tvarlist.iter() {
        let v = tempvar(tvartype)
        markvar(v) |> ignore
        putprop(tv, v, q_ear_varname) |> ignore
        rhs = subst(v, tv, rhs)
      }
      for tv in tvarlist.iter() {
        unmarkvar(get(tv, q_ear_varname)) |> ignore
        putprop(tv, Nil, q_ear_varname) |> ignore
      }
      rhs = reverse(rhs)
      tassigns = reverse(cdr(rhs))
      rhs = car(rhs)
      set(q_d_tempvarname, tvarname) |> ignore
    }
    if tassigns.truthy() {
      return list1(
        append1(cons(list1(q_mprogn), tassigns), list3(list1(q_msetq), lhs, rhs)),
      )
    } else {
      return list1(list3(list1(q_msetq), lhs, rhs))
    }
  }
  let op = stripdollar1(caar(exp_))
  if member(op, list([q_lsetq, q_rsetq, q_lrsetq])).truthy() {
    // (($lsetq  ~) (name d1 d2 ... dn) exp)
    //   -->  ((msetq) ((name) (($eval) d1) ... (($eval) dn)) exp)
    // (($rsetq  ~) var exp)
    //   -->  ((msetq) var (($eval) exp))
    // (($lrsetq ~) ((name) d1 d2 ... dn) exp)
    //   -->  ((msetq) (name (($eval) d1) ... (($eval) dn)) (($eval) exp))
    let mut lhs = cadr(exp_)
    let mut rhs = caddr(exp_)
    if member(op, list2(q_lsetq, q_lrsetq)).truthy() && listp(lhs) {
      lhs = cons(
        list1(caar(lhs)),
        mapcar(s => list2(list1(q_d_eval), s), cdr(lhs)),
      )
    }
    if member(op, list2(q_rsetq, q_lrsetq)).truthy() {
      rhs = list2(list1(q_d_eval), rhs)
    }
    return preproc1(list3(list1(q_msetq), lhs, rhs))
  }
  if equal(op, q_eval) {
    return preproc1(meval(cadr(exp_)))
  }
  if equal(caar(exp_), q_msetq) &&
    listp(caddr(exp_)) &&
    listp(car(caddr(exp_))) &&
    equal(caaaddr(exp_), q_lambda) {
    // store subprogram name & parameters in the symbol table
    symtabput(
      stripdollar1(cadr(exp_)),
      q_ear_params,
      mapcar(p => stripdollar1(p), cdadaddr(exp_)),
    )
    |> ignore
    return list1(allgentran__preproc_all(exp_))
  }
  if equal(caar(exp_), q_mdefine) {
    symtabput(
      stripdollar1(caaadr(exp_)),
      q_ear_params,
      mapcar(p => stripdollar1(p), cdadr(exp_)),
    )
    |> ignore
    return list1(allgentran__preproc_all(exp_))
  }
  if equal(op, q_type) {
    // store type declarations in the symbol table
    let mut exp_ = car(preproc1(cdr(exp_)))
    exp_ = preprocdec(exp_)
    for var_ in cdr(exp_).iter() {
      if member(car(exp_), list2(q_subroutine, q_function)).truthy() {
        symtabput(var_, q_ear_type, car(exp_)) |> ignore
      } else {
        symtabput(
          Nil,
          if atom(var_) {
            var_
          } else {
            caar(var_)
          },
          if atom(var_) {
            list1(car(exp_))
          } else {
            cons(car(exp_), cdr(var_))
          },
        )
        |> ignore
      }
    }
    return Nil
  }
  if equal(op, q_body) {
    // (($body) stmt1 stmt2 ... stmtn)
    // -->
    // if a main (fortran or ratfor) program is being generated then
    //    ((mprogn) stmt1 stmt2 ... stmtn (($stop)) (($end)))
    // else if fortran or ratfor then
    //    ((mprogn) stmt1 stmt2 ... stmtn ((mreturn)) (($end)))
    // else c
    //    ((mprog) stmt1 stmt2 ... stmtn)
    if eq(allgentran__lang(), q_c) {
      return preproc1(cons(list1(q_mprog), cdr(exp_)))
    }
    let mut e = reverse(cons(list1(q_mprogn), cdr(exp_)))
    if equal(car(symval(q_ear_symboltable)), q_ear_main) {
      e = cons(list1(list1(q_d_end)), cons(list1(list1(q_d_stop)), e))
    } else {
      e = cons(list1(list1(q_d_end)), cons(list1(list1(q_mreturn)), e))
    }
    return preproc1(reverse(e))
  }
  if member(op, list([q_subroutine, q_function, q_cprocedure])).truthy() {
    // store subprogram name, (subprogram type), (return value type),
    // parameter list in the symbol table:
    // (($subroutine/$function/$cprocedure) {&type} (($name) $p1..$pn))
    //  --> ((mdefine) (($name) $p1..$pn))
    let mut decs : Value = Nil
    if memq(allgentran__lang(), list2(q_fortran, q_ratfor)).truthy() {
      decs = list1(list3(list1(q_d_type), caar(exp_), caaar(last(exp_))))
    }
    if length(exp_) == 3 {
      decs = aconc(decs, list3(list1(q_d_type), cadr(exp_), caaar(last(exp_))))
    }
    decs = cons(list1(q_mdefine), cons(car(last(exp_)), decs))
    return preproc1(decs)
  }
  list1(allgentran__preproc_all(exp_))
}

///|
/// Parse type declarations that look like expressions (strings are better
/// for types):
/// $var  -->  var
/// ((mtimes) $type int)  -->  type*int
/// ((mplus) $v1 ((mminus) $v2))  -->  v1-v2
fn preprocdec(arg : Value) -> Value raise {
  if atom(arg) {
    stripdollar1(arg)
  } else if atom(car(arg)) {
    mapcar(a => preprocdec(a), arg)
  } else if equal(caar(arg), q_mtimes) {
    // INTERN of the printed (case-inverted) names, which inverts the case
    // of the declaration
    let s = compress(
      append(
        append(exploden(stripdollar1(cadr(arg))), exploden(Char('*'))),
        exploden(caddr(arg)),
      ),
    )
    sym(invert_case(lstring(s)))
  } else if equal(caar(arg), q_mplus) {
    let s = compress(
      append(
        append(exploden(stripdollar1(cadr(arg))), exploden(Char('-'))),
        exploden(stripdollar1(cadaddr(arg))),
      ),
    )
    sym(invert_case(lstring(s)))
  } else {
    mapcar(a => preprocdec(a), arg)
  }
}

// ---------------------------------------------------------------------------
// Top-level forms

///|
fn init_share_allgentran() -> Unit raise {
  // mode switches
  set(q_n_starfortran, Nil) |> ignore
  set(q_n_starratfor, Nil) |> ignore
  set(q_n_starc, Nil) |> ignore
  set(q_n_stargendecs, t) |> ignore
  let switch_forms = (form : Value) => list2(list1(Nil), list2(t, form))
  put(q_fortran, q_simpfg, switch_forms(list2(q_gentranswitch, list2(q_quote, q_fortran))))
  |> ignore
  put(q_ratfor, q_simpfg, switch_forms(list2(q_gentranswitch, list2(q_quote, q_ratfor))))
  |> ignore
  put(q_c, q_simpfg, switch_forms(list2(q_gentranswitch, list2(q_quote, q_c))))
  |> ignore
  put(q_gendecs, q_simpfg, switch_forms(list2(q_gendecs, Nil))) |> ignore
  // user-accessible global variables
  set(q_d_genfloat, Nil) |> ignore
  set(q_d_dblfloat, Nil) |> ignore
  set(q_d_usefortcomplex, Nil) |> ignore
  set(q_d_gentranopt, Nil) |> ignore
  set(q_d_gentranseg, t) |> ignore
  set(q_d_gentranparser, Nil) |> ignore
  set(q_d_gentranlang, q_fortran) |> ignore
  set(q_d_maxexpprintlen, Fix(800L)) |> ignore
  set(q_d_tempvarname, q_d_t) |> ignore
  set(q_d_optimvarname, q_d_u) |> ignore
  set(q_d_tempvarnum, Fix(0L)) |> ignore
  set(q_d_tempvartype, Nil) |> ignore
  set(q_d_implicit, Nil) |> ignore
  set(q_d_genstmtno, Fix(25000L)) |> ignore
  set(q_d_genstmtincr, Fix(1L)) |> ignore
  set(q_d_fortcurrind, Fix(6L)) |> ignore
  set(q_d_ratcurrind, Fix(0L)) |> ignore
  set(q_d_ccurrind, Fix(0L)) |> ignore
  set(q_d_tablen, Fix(4L)) |> ignore
  set(q_d_fortlinelen, Fix(72L)) |> ignore
  set(q_d_ratlinelen, Fix(80L)) |> ignore
  set(q_d_clinelen, Fix(80L)) |> ignore
  set(q_d_geninpath, Nil) |> ignore
  set(q_d_genoutpath, Nil) |> ignore
  // system variables
  set(q_ear_stdin, cons(t, symval(standard_input))) |> ignore
  set(q_ear_instk, list1(symval(q_ear_stdin))) |> ignore
  set(q_ear_currin, car(symval(q_ear_instk))) |> ignore
  set(q_ear_stdout, cons(t, symval(standard_output))) |> ignore
  set(q_ear_outstk, list1(symval(q_ear_stdout))) |> ignore
  set(q_ear_currout, car(symval(q_ear_outstk))) |> ignore
  set(q_ear_outchanl, list1(cdr(symval(q_ear_currout)))) |> ignore
  set(q_ear_symboltable, list1(q_ear_main)) |> ignore
  set(q_ear_endofloopstack, Nil) |> ignore
  set(
    q_ear_lisparithexpops,
    list([q_expt, q_minus, q_plus, q_quotient, q_times]),
  )
  |> ignore
  set(
    q_ear_lisplogexpops,
    list([
      q_and, q_equal, q_geqp, q_greaterp, q_leqp, q_lessp, q_not, q_notequal, q_or,
    ]),
  )
  |> ignore
  set(
    q_ear_lispstmtops,
    list([
      q_break, q_cond, q_do, q_end, q_go, q_princ, q_return, q_setq, q_stop,
    ]),
  )
  |> ignore
  set(q_ear_lispstmtgpops, list2(q_prog, q_progn)) |> ignore
  set(q_ear_lispdefops, list1(q_defun)) |> ignore
  set(q_ear_slash, Char('/')) |> ignore
  set(q_ear_cr, Char('\n')) |> ignore
  set(q_ear_eof, Char('\u{0}')) |> ignore
  set(
    q_ear_reswds,
    list([
      q_lambda, q_mand, q_mcond, q_mdefine, q_mdo, q_mdoin, q_mequal, q_mexpt, q_mgeqp,
      q_mgo, q_mgreaterp, q_mleqp, q_mlessp, q_mlist, q_mminus, q_mnot, q_mnotequal,
      q_mor, q_mplus, q_mprog, q_mprogn, q_mquotient, q_mreturn, q_msetq, q_mtimes,
      q_rat, q_d_end, q_d_ev, q_d_false, q_d_matrix, q_d_print, q_d_readonly, q_d_stop,
    ]),
  )
  |> ignore
  // Lisp names of Maxima operators
  for p in [
    (q_mor, q_or),
    (q_mand, q_and),
    (q_mnot, q_not),
    (q_mgreaterp, q_greaterp),
    (q_mequal, q_equal),
    (q_mnotequal, q_notequal),
    (q_mlessp, q_lessp),
    (q_mgeqp, q_geqp),
    (q_mleqp, q_leqp),
    (q_mplus, q_plus),
    (q_mtimes, q_times),
    (q_mquotient, q_quotient),
    (q_rat, q_quotient),
    (q_mexpt, q_expt),
    (q_mminus, q_minus),
    (q_mabs, q_abs),
  ] {
    putprop(p.0, p.1, q_franznotn) |> ignore
  }
  // Fortran
  for p in [
    (q_or, 1L),
    (q_and, 2L),
    (q_not, 3L),
    (q_equal, 4L),
    (q_notequal, 4L),
    (q_op_gt, 4L),
    (q_greaterp, 4L),
    (q_geqp, 4L),
    (q_op_lt, 4L),
    (q_lessp, 4L),
    (q_leqp, 4L),
    (q_op_plus, 5L),
    (q_plus, 5L),
    (q_op_star, 6L),
    (q_times, 6L),
    (q_quotient, 6L),
    (q_op_h_, 7L),
    (q_minus, 7L),
    (q_expt, 8L),
  ] {
    put(p.0, q_ear_fortranprecedence, Fix(p.1)) |> ignore
  }
  for p in [
    (q_or, q_n_sp_dot_co__cr__dot_sp),
    (q_and, q_n_sp_dot_ca__cn__cd__dot_sp),
    (q_not, q_n_sp_dot_cn__co__ct__dot_sp),
    (q_equal, q_n_sp_dot_ce__cq__dot_sp),
    (q_notequal, q_n_sp_dot_cn__ce__dot_sp),
    (q_op_gt, q_n_sp_dot_cg__ct__dot_sp),
    (q_greaterp, q_n_sp_dot_cg__ct__dot_sp),
    (q_geqp, q_n_sp_dot_cg__ce__dot_sp),
    (q_op_lt, q_n_sp_dot_cl__ct__dot_sp),
    (q_lessp, q_n_sp_dot_cl__ct__dot_sp),
    (q_leqp, q_n_sp_dot_cl__ce__dot_sp),
    (q_op_plus, q_op_plus),
    (q_plus, q_op_plus),
    (q_op_star, q_op_star),
    (q_times, q_op_star),
    (q_quotient, q_op_sl),
    (q_expt, q_op_star_star),
    (q_op_h_, q_op_h_),
    (q_minus, q_op_h_),
  ] {
    put(p.0, q_ear_fortranop, p.1) |> ignore
  }
  put(Nil, q_ear_fortranname, Str(".false.")) |> ignore
  set(q_comma_star, Str(",")) |> ignore
  // Ratfor
  put(Nil, q_ear_ratforname, Str(".false.")) |> ignore
  for p in [
    (q_or, 1L),
    (q_and, 2L),
    (q_not, 3L),
    (q_equal, 4L),
    (q_notequal, 4L),
    (q_greaterp, 4L),
    (q_geqp, 4L),
    (q_lessp, 4L),
    (q_leqp, 4L),
    (q_plus, 5L),
    (q_times, 6L),
    (q_quotient, 6L),
    (q_minus, 7L),
    (q_expt, 8L),
  ] {
    put(p.0, q_ear_ratforprecedence, Fix(p.1)) |> ignore
  }
  for p in [
    (q_or, Value::Str("||")),
    (q_and, q_op_amp),
    (q_not, q_op_bang),
    (q_equal, q_op_eq_eq),
    (q_notequal, q_op_bang_eq),
    (q_greaterp, q_op_gt),
    (q_geqp, q_op_gt_eq),
    (q_lessp, q_op_lt),
    (q_leqp, q_op_lt_eq),
    (q_plus, q_op_plus),
    (q_times, q_op_star),
    (q_quotient, q_op_sl),
    (q_expt, q_op_star_star),
    (q_minus, q_op_h_),
  ] {
    put(p.0, q_ear_ratforop, p.1) |> ignore
  }
  // C
  put(Nil, q_ear_cname, Fix(0L)) |> ignore
  for p in [
    (q_or, 1L),
    (q_and, 2L),
    (q_equal, 3L),
    (q_notequal, 3L),
    (q_greaterp, 4L),
    (q_geqp, 4L),
    (q_lessp, 4L),
    (q_leqp, 4L),
    (q_plus, 5L),
    (q_times, 6L),
    (q_quotient, 6L),
    (q_not, 7L),
    (q_minus, 7L),
  ] {
    put(p.0, q_ear_cprecedence, Fix(p.1)) |> ignore
  }
  for p in [
    (q_and, q_op_amp_amp),
    (q_not, q_op_bang),
    (q_equal, q_op_eq_eq),
    (q_notequal, q_op_bang_eq),
    (q_greaterp, q_op_gt),
    (q_geqp, q_op_gt_eq),
    (q_lessp, q_op_lt),
    (q_leqp, q_op_lt_eq),
    (q_plus, q_op_plus),
    (q_times, q_op_star),
    (q_quotient, q_op_sl),
    (q_minus, q_op_h_),
    (q_or, Value::Str("||")),
  ] {
    put(p.0, q_ear_cop, p.1) |> ignore
  }
}
