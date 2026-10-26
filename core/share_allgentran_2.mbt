// Port of share/contrib/gentran/allgentran.lisp (part 2): the parser of
// Maxima's internal representation (parser.l), the segmentation of long
// expressions (segmnt.l) and the Lisp -> Fortran translation (lspfor.l).

// ---------------------------------------------------------------------------
// parser.l

///|
fn gentranparse(forms : Value) -> Value raise {
  for f in forms.iter() {
    if !(pmstmt(f).truthy() || pmexp(f).truthy() || pmlogexp(f).truthy()) {
      gentranerr(q_e, f, Str("cannot be translated")) |> ignore
    }
  }
  Nil
}

///|
/// exp  ::=  const | var | funcall | ((mminus ~) exp) |
///           ((mquotient ~) exp exp) | ((rat ~) exp exp) |
///           ((mexpt ~) exp exp) | ((mplus ~) exp exp exp') |
///           ((mtimes ~) exp exp exp')
/// funcall  ::=  ((id ~) exp')
fn pmexp(s : Value) -> Value raise {
  if atom(s) {
    let c = pmconst(s)
    if c.truthy() {
      c
    } else {
      pmid(s)
    }
  } else if listp(s) && listp(car(s)) {
    if pmidop(car(s)).truthy() {
      pmexp1(cdr(s))
    } else if pmmminusop(car(s)).truthy() {
      lbool(length(s) == 2 && pmexp(cadr(s)).truthy())
    } else if pmmquotientop(car(s)).truthy() ||
      pmratop(car(s)).truthy() ||
      pmmexptop(car(s)).truthy() {
      lbool(
        length(s) == 3 && pmexp(cadr(s)).truthy() && pmexp(caddr(s)).truthy(),
      )
    } else if pmmplusop(car(s)).truthy() || pmmtimesop(car(s)).truthy() {
      lbool(
        length(s) > 2 &&
        pmexp(cadr(s)).truthy() &&
        pmexp(caddr(s)).truthy() &&
        pmexp1(cdddr(s)).truthy(),
      )
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// exp'  ::=  exp exp' | epsilon
fn pmexp1(s : Value) -> Value raise {
  lbool(null(s) || (pmexp(car(s)).truthy() && pmexp1(cdr(s)).truthy()))
}

///|
/// logexp  ::=  t | nil | var | funcall | relexp | ((mnot ~) logexp) |
///              ((mand ~) logexp logexp logexp') |
///              ((mor ~) logexp logexp logexp')
/// relexp  ::=  ((mgreaterp ~) exp exp) | ((mequal ~) exp exp) |
///              ((mnotequal ~) exp exp) | ((mlessp ~) exp exp) |
///              ((mgeqp ~) exp exp) | ((mleqp ~) exp exp)
fn pmlogexp(s : Value) -> Value raise {
  if atom(s) {
    lbool(pmid(s).truthy() || null(s) || equal(s, t))
  } else if listp(s) && listp(car(s)) {
    if pmidop(car(s)).truthy() {
      pmexp1(cdr(s))
    } else if pmmgreaterpop(car(s)).truthy() ||
      pmmequalop(car(s)).truthy() ||
      pmmnotequalop(car(s)).truthy() ||
      pmmlesspop(car(s)).truthy() ||
      pmmgeqpop(car(s)).truthy() ||
      pmmleqpop(car(s)).truthy() {
      lbool(
        length(s) == 3 && pmexp(cadr(s)).truthy() && pmexp(caddr(s)).truthy(),
      )
    } else if pmmnotop(car(s)).truthy() {
      lbool(length(s) == 2 && pmlogexp(cadr(s)).truthy())
    } else if pmmandop(car(s)).truthy() || pmmorop(car(s)).truthy() {
      lbool(
        length(s) > 2 &&
        pmlogexp(cadr(s)).truthy() &&
        pmlogexp(caddr(s)).truthy() &&
        pmlogexp1(cdddr(s)).truthy(),
      )
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn pmlogexp1(s : Value) -> Value raise {
  lbool(null(s) || (pmlogexp(car(s)).truthy() && pmlogexp1(cdr(s)).truthy()))
}

///|
/// stmt  ::=  assign | nestassign | matassign | cond | for | forin | go |
///            label | call | return | stop | end | read | print | stmtgp |
///            defn
fn pmstmt(s : Value) -> Value raise {
  if atom(s) {
    pmid(s)
  } else if listp(s) && listp(car(s)) {
    let op = car(s)
    if pmmsetqop(op).truthy() {
      pmmsetq1(cdr(s))
    } else if pmmcondop(op).truthy() {
      lbool(
        length(s) > 4 &&
        pmlogexp(cadr(s)).truthy() &&
        pmstmt(caddr(s)).truthy() &&
        equal(cadddr(s), t) &&
        pmmcond1(cddddr(s)).truthy(),
      )
    } else if pmmdoop(op).truthy() {
      lbool(
        length(s) == 8 &&
        pmvarnil(cadr(s)).truthy() &&
        pmexp(caddr(s)).truthy() &&
        pmexp(cadddr(s)).truthy() &&
        pmexp(caddddr(s)).truthy() &&
        pmexp(cadddddr(s)).truthy() &&
        pmlogexp(caddddddr(s)).truthy() &&
        pmstmt(cadddddddr(s)).truthy(),
      )
    } else if pmmdoinop(op).truthy() {
      lbool(
        length(s) == 8 &&
        pmvar(cadr(s)).truthy() &&
        pmlist(caddr(s)).truthy() &&
        null(cadddr(s)) &&
        null(caddddr(s)) &&
        null(cadddddr(s)) &&
        pmlogexp(caddddddr(s)).truthy() &&
        pmstmt(cadddddddr(s)).truthy(),
      )
    } else if pmmgoop(op).truthy() {
      lbool(length(s) == 2 && pmid(cadr(s)).truthy())
    } else if pmmreturnop(op).truthy() {
      lbool(length(s) == 1 || (length(s) == 2 && pmretexp(cadr(s)).truthy()))
    } else if pm_dolstopop(op).truthy() {
      lbool(length(s) == 1)
    } else if pm_dolendop(op).truthy() {
      lbool(length(s) == 1)
    } else if pm_dolprintop(op).truthy() {
      pmparams1(cdr(s))
    } else if pm_doldeclare_typeop(op).truthy() {
      t
    } else if pmmprogop(op).truthy() ||
      pmmprognop(op).truthy() ||
      pm_dolevop(op).truthy() {
      lbool(length(s) > 1 && pmstmt(cadr(s)).truthy() && pmstmt1(cddr(s)).truthy())
    } else if pmmdefineop(op).truthy() {
      lbool(
        length(s) > 1 &&
        pmidparamop(cadr(s)).truthy() &&
        (null(cddr(s)) || pmmdefine1(cddr(s)).truthy()),
      )
    } else if pmidop(op).truthy() {
      pmparams1(cdr(s))
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn pmstmt1(s : Value) -> Value raise {
  lbool(null(s) || (pmstmt(car(s)).truthy() && pmstmt1(cdr(s)).truthy()))
}

///|
fn pmmsetq1(s : Value) -> Value raise {
  if listp(s) && atom(car(s)) {
    lbool(pmid(car(s)).truthy() && pmmsetq2(cdr(s)).truthy())
  } else if listp(s) && listp(car(s)) {
    lbool(
      length(car(s)) > 1 &&
      pmidop(caar(s)).truthy() &&
      pmexp(cadar(s)).truthy() &&
      pmexp1(cddar(s)).truthy() &&
      pmmsetq3(cdr(s)).truthy(),
    )
  } else {
    Nil
  }
}

///|
fn pmmsetq2(s : Value) -> Value raise {
  if listp(s) &&
    listp(car(s)) &&
    length(s) == 1 &&
    length(car(s)) == 3 &&
    pmlambdaop(caar(s)).truthy() {
    lbool(pmlist(cadar(s)).truthy() && pmretexp(caddar(s)).truthy())
  } else {
    pmmsetq3(s)
  }
}

///|
fn pmmsetq3(s : Value) -> Value raise {
  if listp(s) &&
    listp(car(s)) &&
    length(s) == 1 &&
    length(car(s)) > 1 &&
    pm_dolmatrixop(caar(s)).truthy() {
    lbool(pmlist(cadar(s)).truthy() && pmlist1(cddar(s)).truthy())
  } else {
    pmmsetq4(s)
  }
}

///|
fn pmmsetq4(s : Value) -> Value raise {
  if listp(s) {
    if pmexp(car(s)).truthy() {
      lbool(null(cdr(s)))
    } else if pmlogexp(car(s)).truthy() {
      lbool(null(cdr(s)))
    } else if listp(car(s)) && pmmsetqop(caar(s)).truthy() {
      lbool(
        length(s) == 1 &&
        length(car(s)) > 1 &&
        pmvar(cadar(s)).truthy() &&
        pmmsetq4(cddar(s)).truthy(),
      )
    } else if listp(car(s)) && pm_dolreadonlyop(caar(s)).truthy() {
      lbool(
        length(s) == 1 &&
        (length(car(s)) == 1 ||
        (length(car(s)) == 2 && pmvar(cadar(s)).truthy())),
      )
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn pmmcond1(s : Value) -> Value raise {
  if equal(s, list1(q_d_false)) {
    t
  } else if pmstmt(car(s)).truthy() {
    lbool(null(cdr(s)))
  } else {
    Nil
  }
}

///|
fn pmidop(s : Value) -> Value raise {
  lbool(listp(s) && !member(car(s), symval(q_ear_reswds)).truthy())
}

///|
fn allgentran__pmop(s : Value, op : Value) -> Value {
  lbool(listp(s) && equal(car(s), op))
}

///|
fn pmmminusop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mminus)
}

///|
fn pmmquotientop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mquotient)
}

///|
fn pmratop(s : Value) -> Value raise {
  allgentran__pmop(s, q_rat)
}

///|
fn pmmexptop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mexpt)
}

///|
fn pmmplusop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mplus)
}

///|
fn pmmtimesop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mtimes)
}

///|
fn pmmgreaterpop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mgreaterp)
}

///|
fn pmmequalop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mequal)
}

///|
fn pmmnotequalop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mnotequal)
}

///|
fn pmmlesspop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mlessp)
}

///|
fn pmmgeqpop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mgeqp)
}

///|
fn pmmleqpop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mleqp)
}

///|
fn pmmnotop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mnot)
}

///|
fn pmmandop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mand)
}

///|
fn pmmorop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mor)
}

///|
fn pmmsetqop(s : Value) -> Value raise {
  allgentran__pmop(s, q_msetq)
}

///|
fn pmmcondop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mcond)
}

///|
fn pmmdoop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mdo)
}

///|
fn pmmdoinop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mdoin)
}

///|
fn pmmgoop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mgo)
}

///|
fn pmmreturnop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mreturn)
}

///|
fn pm_dolstopop(s : Value) -> Value raise {
  allgentran__pmop(s, q_d_stop)
}

///|
fn pm_dolendop(s : Value) -> Value raise {
  allgentran__pmop(s, q_d_end)
}

///|
fn pm_dolprintop(s : Value) -> Value raise {
  allgentran__pmop(s, q_d_print)
}

///|
fn pm_doldeclare_typeop(s : Value) -> Value raise {
  allgentran__pmop(s, q_d_declare_type)
}

///|
fn pmmprogop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mprog)
}

///|
fn pmmprognop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mprogn)
}

///|
fn pm_dolevop(s : Value) -> Value raise {
  allgentran__pmop(s, q_d_ev)
}

///|
fn pmmdefineop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mdefine)
}

///|
fn pm_dolreadonlyop(s : Value) -> Value raise {
  allgentran__pmop(s, q_d_readonly)
}

///|
fn pmlambdaop(s : Value) -> Value raise {
  allgentran__pmop(s, q_lambda)
}

///|
fn pm_dolmatrixop(s : Value) -> Value raise {
  allgentran__pmop(s, q_d_matrix)
}

///|
fn pmmlistop(s : Value) -> Value raise {
  allgentran__pmop(s, q_mlist)
}

///|
fn pmidparamop(s : Value) -> Value raise {
  lbool(listp(s) && pmidop(car(s)).truthy() && pmid1(cdr(s)).truthy())
}

///|
fn pmmdefine1(s : Value) -> Value raise {
  lbool(
    listp(s) &&
    length(s) == 1 &&
    (pmretexp(car(s)).truthy() || pmstmt(car(s)).truthy()),
  )
}

///|
/// id'  ::=  id id' | epsilon
fn pmid1(s : Value) -> Value raise {
  lbool(null(s) || (pmid(car(s)).truthy() && pmid1(cdr(s)).truthy()))
}

///|
/// var  ::=  id | arrelt
/// arrelt  ::=  ((id ~) exp exp')
fn pmvar(s : Value) -> Value raise {
  if atom(s) {
    pmid(s)
  } else if listp(s) {
    lbool(
      length(s) > 1 &&
      pmidop(car(s)).truthy() &&
      pmexp(cadar(s)).truthy() &&
      pmexp1(cddar(s)).truthy(),
    )
  } else {
    Nil
  }
}

///|
/// varnil  ::=  var | nil
fn pmvarnil(s : Value) -> Value raise {
  if null(s) {
    t
  } else {
    pmvar(s)
  }
}

///|
/// retexp  ::=  exp | logexp | string | epsilon
fn pmretexp(s : Value) -> Value raise {
  lbool(
    null(s) ||
    pmexp(s).truthy() ||
    pmlogexp(s).truthy() ||
    pmstring(s).truthy(),
  )
}

///|
/// params  ::=  exp params | logexp params | string params | epsilon
fn pmparams1(s : Value) -> Value raise {
  lbool(
    null(s) ||
    (pmexp(car(s)).truthy() && pmparams1(cdr(s)).truthy()) ||
    (pmlogexp(car(s)).truthy() && pmparams1(cdr(s)).truthy()) ||
    (pmstring(car(s)).truthy() && pmparams1(cdr(s)).truthy()),
  )
}

///|
/// list  ::=  ((mlist ~) exp exp') | ((mlist ~) logexp logexp')
fn pmlist(s : Value) -> Value raise {
  lbool(listp(s) && pmmlistop(car(s)).truthy() && pmlist2(cdr(s)).truthy())
}

///|
fn pmlist2(s : Value) -> Value raise {
  lbool(
    (pmexp(car(s)).truthy() && pmexp1(cdr(s)).truthy()) ||
    (pmlogexp(car(s)).truthy() && pmlogexp1(cdr(s)).truthy()),
  )
}

///|
/// list'  ::=  list list' | epsilon
fn pmlist1(s : Value) -> Value raise {
  lbool(null(s) || (pmlist(car(s)).truthy() && pmlist1(cdr(s)).truthy()))
}

///|
fn pmconst(s : Value) -> Value raise {
  lbool(numberp(s) || null(s) || equal(s, t))
}

///|
fn pmstring(s : Value) -> Value raise {
  lbool(stringp(s))
}

///|
fn pmid(s : Value) -> Value raise {
  lbool(atom(s) && !member(s, list2(t, Nil)).truthy())
}

// ---------------------------------------------------------------------------
// segmnt.l: segmentation of long expressions and statements

///|
/// exp  --+-->  exp          stmt  --+-->  stmt
///        +-->  stmtgp               +-->  stmtgp
/// stmtgp  ----->  stmtgp    def  ----->  def
fn seg(forms : Value) -> Value raise {
  mapcar(
    f => if !atom(f) &&
      !equal(car(f), q_literal) &&
      lispexpp(f).truthy() {
      if toolongexpp(f).truthy() {
        segexp(f, q_unknown)
      } else {
        f
      }
    } else if lispstmtp(f).truthy() {
      segstmt(f)
    } else if lispstmtgpp(f).truthy() {
      if toolongstmtgpp(f).truthy() {
        seggroup(f)
      } else {
        f
      }
    } else if lispdefp(f).truthy() {
      if toolongdefp(f).truthy() {
        segdef(f)
      } else {
        f
      }
    } else {
      f
    },
    forms,
  )
}

///|
/// exp  -->  stmtgp comprising (assign(1) assign(2) ... assign(n-1) exp(n))
fn segexp(exp_ : Value, type_ : Value) -> Value raise {
  mkstmtgp(Fix(0L), reverse(segexp1(exp_, type_)))
}

///|
/// exp  -->  (exp(n) assign(n-1) assign(n-2) ... assign(1))
fn segexp1(exp_ : Value, type_ : Value) -> Value raise {
  let tempvarname = symval(q_d_tempvarname)
  let mut res = segexp2(exp_, type_)
  recurunmark(res) |> ignore
  set(q_d_tempvarname, tempvarname) |> ignore
  if equal(car(res), cadadr(res)) {
    res = cdr(res)
    rplaca(res, caddar(res)) |> ignore
  }
  res
}

///|
/// exp  -->  (exp(n) assign(n-1) assign(n-2) ... assign(1))
fn segexp2(exp_ : Value, type_ : Value) -> Value raise {
  let mut expn = exp_
  let mut assigns : Value = Nil
  let mut unops : Value = Nil
  let mut termlist : Value = Nil
  let mut var_ : Value = Nil
  while length(expn) == 2 {
    unops = cons(car(expn), unops)
    expn = cadr(expn)
  }
  let op = car(expn)
  for term0 in cdr(expn).iter() {
    let mut term = term0
    let mut newassigns : Value = Nil
    if toolongexpp(term).truthy() {
      let tmp = segexp2(term, type_)
      term = car(tmp)
      newassigns = cdr(tmp)
    }
    if toolongexpp(cons(op, cons(term, termlist))).truthy() &&
      termlist.truthy() &&
      (length(termlist) > 1 || listp(car(termlist))) {
      recurunmark(termlist) |> ignore
      if !var_.truthy() {
        var_ = tempvar(type_)
      }
      markvar(var_) |> ignore
      assigns = cons(
        mkassign(
          var_,
          if onep(int(length(termlist))).truthy() {
            car(termlist)
          } else {
            cons(op, termlist)
          },
        ),
        assigns,
      )
      termlist = list2(var_, term)
    } else {
      termlist = aconc(termlist, term)
    }
    assigns = append(newassigns, assigns)
  }
  expn = if onep(int(length(termlist))).truthy() {
    car(termlist)
  } else {
    cons(op, termlist)
  }
  while unops.truthy() {
    expn = list2(car(unops), expn)
    unops = cdr(unops)
  }
  if equal(expn, exp_) {
    recurunmark(expn) |> ignore
    if !var_.truthy() {
      var_ = tempvar(type_)
    }
    markvar(var_) |> ignore
    assigns = list1(mkassign(var_, expn))
    expn = var_
  }
  cons(expn, assigns)
}

///|
/// assign, cond, do, return  --+-->  same statement
///                             +-->  stmtgp
fn segstmt(stmt : Value) -> Value raise {
  if lispassignp(stmt).truthy() {
    if toolongassignp(stmt).truthy() {
      segassign(stmt)
    } else {
      stmt
    }
  } else if lispcondp(stmt).truthy() {
    if toolongcondp(stmt).truthy() {
      segcond(stmt)
    } else {
      stmt
    }
  } else if lispdop(stmt).truthy() {
    if toolongdop(stmt).truthy() {
      segdo(stmt)
    } else {
      stmt
    }
  } else if lispreturnp(stmt).truthy() {
    if toolongreturnp(stmt).truthy() {
      segreturn(stmt)
    } else {
      stmt
    }
  } else {
    stmt
  }
}

///|
/// assign  -->  stmtgp
fn segassign(stmt : Value) -> Value raise {
  let var_ = cadr(stmt)
  let type_ = getvartype(var_)
  let exp_ = caddr(stmt)
  let stmt = segexp1(exp_, type_)
  rplaca(stmt, mkassign(var_, car(stmt))) |> ignore
  mkstmtgp(Fix(0L), reverse(stmt))
}

///|
/// cond  --+-->  cond
///         +-->  stmtgp
fn segcond(cond : Value) -> Value raise {
  let mut tassigns : Value = Nil
  let mut res : Value = Nil
  let mut markedvars : Value = Nil
  let type_ = if eq(allgentran__lang(), q_c) { q_int } else { q_logical }
  let mut cond = cdr(cond)
  while cond.truthy() {
    let mut exp_ = caar(cond)
    if toolongexpp(exp_).truthy() {
      exp_ = segexp1(exp_, type_)
      tassigns = append(cdr(exp_), tassigns)
      exp_ = car(exp_)
      markvar(exp_) |> ignore
      markedvars = cons(exp_, markedvars)
    }
    let stmt = mapcar(st => segstmt(st), cdar(cond))
    res = cons(cons(exp_, stmt), res)
    cond = cdr(cond)
  }
  recurunmark(markedvars) |> ignore
  if tassigns.truthy() {
    mkstmtgp(Fix(0L), reverse(cons(mkcond(reverse(res)), tassigns)))
  } else {
    mkcond(reverse(res))
  }
}

///|
/// do  --+-->  do
///       +-->  stmtgp
fn segdo(stmt : Value) -> Value raise {
  let mut tassigns : Value = Nil
  let mut markedvars : Value = Nil
  let mut body = cdddr(stmt)
  let mut var_ = cadr(stmt)
  if var_.truthy() {
    let mut initexp = cadar(var_)
    if toolongexpp(initexp).truthy() {
      let type_ = getvartype(caar(var_))
      initexp = segexp1(initexp, type_)
      tassigns = cdr(initexp)
      initexp = car(initexp)
      markvar(initexp) |> ignore
      markedvars = cons(initexp, markedvars)
    }
    let mut nextexp = caddar(var_)
    if toolongexpp(nextexp).truthy() {
      let type_ = getvartype(caar(var_))
      nextexp = segexp1(nextexp, type_)
      body = append(body, reverse(cdr(nextexp)))
      nextexp = car(nextexp)
      markvar(nextexp) |> ignore
      markedvars = cons(nextexp, markedvars)
    }
    var_ = list1(list3(caar(var_), initexp, nextexp))
  }
  let exitcond = caddr(stmt)
  if toolongexpp(car(exitcond)).truthy() {
    let ltype = if eq(allgentran__lang(), q_c) { q_int } else { q_logical }
    let texps = segexp1(car(exitcond), ltype)
    markvar(car(texps)) |> ignore
    markedvars = cons(car(texps), markedvars)
    rplaca(exitcond, car(texps)) |> ignore
    for texp0 in reverse(cdr(texps)).iter() {
      // (setq v e)  -->  (v e e)
      let texp = reverse(texp0)
      var_ = cons(cdr(reverse(cons(car(texp), texp))), var_)
    }
    var_ = reverse(var_)
  }
  body = mapcar(st => segstmt(st), body)
  recurunmark(markedvars) |> ignore
  if tassigns.truthy() {
    mkstmtgp(Fix(0L), reverse(cons(mkdo(var_, exitcond, body), tassigns)))
  } else {
    mkdo(var_, exitcond, body)
  }
}

///|
/// return  -->  stmtgp
fn segreturn(ret : Value) -> Value raise {
  let ret = segexp1(cadr(ret), q_unknown)
  rplaca(ret, mkreturn(car(ret))) |> ignore
  mkstmtgp(Fix(0L), reverse(ret))
}

///|
/// stmtgp  -->  stmtgp
fn seggroup(stmtgp : Value) -> Value raise {
  let mut stmtgp = stmtgp
  let mut locvars : Value = Fix(0L)
  let mut res : Value = Nil
  if equal(car(stmtgp), q_prog) {
    locvars = cadr(stmtgp)
    stmtgp = cdr(stmtgp)
  }
  stmtgp = cdr(stmtgp)
  while stmtgp.truthy() {
    res = cons(segstmt(car(stmtgp)), res)
    stmtgp = cdr(stmtgp)
  }
  mkstmtgp(locvars, reverse(res))
}

///|
/// def  -->  def
fn segdef(def : Value) -> Value raise {
  mkdef(cadr(def), caddr(def), mapcar(stmt => segstmt(stmt), cdddr(def)))
}

///|
fn toolongexpp(exp_ : Value) -> Value raise {
  lbool(num_gt(numprintlen(exp_), symval(q_d_maxexpprintlen)))
}

///|
fn allgentran__some(l : Value) -> Value {
  for x in l.iter() {
    if x.truthy() {
      return x
    }
  }
  Nil
}

///|
fn toolongstmtp(stmt : Value) -> Value raise {
  if atom(stmt) {
    Nil
  } else if lispstmtp(stmt).truthy() {
    if lispcondp(stmt).truthy() {
      toolongcondp(stmt)
    } else if lispassignp(stmt).truthy() {
      toolongassignp(stmt)
    } else if lispreturnp(stmt).truthy() {
      toolongreturnp(stmt)
    } else if lispdop(stmt).truthy() {
      toolongdop(stmt)
    } else {
      allgentran__some(mapcar(exp_ => toolongexpp(exp_), stmt))
    }
  } else {
    toolongstmtgpp(stmt)
  }
}

///|
fn toolongassignp(assign : Value) -> Value raise {
  toolongexpp(caddr(assign))
}

///|
fn toolongcondp(cond : Value) -> Value raise {
  let mut toolong : Value = Nil
  let mut cond = cdr(cond)
  while cond.truthy() {
    if toolongexpp(caar(cond)).truthy() || toolongstmtp(cadar(cond)).truthy() {
      toolong = t
    }
    cond = cdr(cond)
  }
  toolong
}

///|
fn toolongdop(dostmt : Value) -> Value raise {
  let mut sum : Value = Fix(0L)
  for exp_ in caadr(dostmt).iter() {
    sum = num_add(sum, numprintlen(exp_))
  }
  if num_gt(sum, symval(q_d_maxexpprintlen)) {
    t
  } else if toolongexpp(caaddr(dostmt)).truthy() {
    t
  } else if lispstmtgpp(cadddr(dostmt)).truthy() {
    toolongstmtgpp(cadddr(dostmt))
  } else {
    allgentran__some(mapcar(stmt => toolongstmtp(stmt), cdddr(dostmt)))
  }
}

///|
fn toolongreturnp(ret : Value) -> Value raise {
  toolongexpp(cadr(ret))
}

///|
fn toolongstmtgpp(stmtgp : Value) -> Value raise {
  allgentran__some(mapcar(stmt => toolongstmtp(stmt), cdr(stmtgp)))
}

///|
fn toolongdefp(def : Value) -> Value raise {
  if lispstmtgpp(cadddr(def)).truthy() {
    toolongstmtgpp(cadddr(def))
  } else {
    allgentran__some(mapcar(stmt => toolongstmtp(stmt), cdddr(def)))
  }
}

///|
/// The print length of an expression.
fn numprintlen(exp_ : Value) -> Value raise {
  if atom(exp_) {
    int(length(explode(exp_)))
  } else if onep(int(length(exp_))).truthy() {
    numprintlen(car(exp_))
  } else {
    let mut sum : Value = Fix(0L)
    for elt in cdr(exp_).iter() {
      sum = num_add(sum, numprintlen(elt))
    }
    num_add(int(length(exp_)), sum)
  }
}

// ---------------------------------------------------------------------------
// lspfor.l: Lisp -> Fortran translation

///|
fn fortcode(forms : Value) -> Value raise {
  mapcan(
    f => if atom(f) {
      if member(f, list2(q_d_begin_group, q_d_end_group)).truthy() {
        Nil
      } else {
        fortexp(f)
      }
    } else if lispstmtp(f).truthy() || lispstmtgpp(f).truthy() {
      if symval(q_n_stargendecs).truthy() {
        let d = fortdecs(symtabget(q_ear_main, q_ear_decs))
        let r = append(d, fortstmt(f))
        symtabrem(q_ear_main, q_ear_decs) |> ignore
        r
      } else {
        fortstmt(f)
      }
    } else if lispdefp(f).truthy() {
      fortsubprog(f)
    } else {
      fortexp(f)
    },
    forms,
  )
}

///|
/// The parts of a subprogram definition: (type stype name params body),
/// shared by the Fortran and Ratfor translations.
fn allgentran__subprog_parts(
  def : Value,
) -> (Value, Value, Value, Value, Value) raise {
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
  if body.truthy() {
    let lastst = car(reverse(body))
    if lispreturnp(lastst).truthy() {
      body = aconc(body, list1(q_end))
    } else if !lispendp(lastst).truthy() {
      body = append(body, list2(list1(q_return), list1(q_end)))
    }
  }
  let mut type_ = symtabget(name, name)
  if type_.truthy() {
    type_ = cadr(type_)
    symtabrem(name, name) |> ignore
  }
  let mut stype = symtabget(name, q_ear_type)
  if !stype.truthy() {
    stype = if type_.truthy() || gfunctionp(body, name).truthy() {
      q_function
    } else {
      q_subroutine
    }
  }
  symtabrem(name, q_ear_type) |> ignore
  let mut params = symtabget(name, q_ear_params)
  if !params.truthy() {
    params = caddr(def)
  }
  symtabrem(name, q_ear_params) |> ignore
  (type_, stype, name, params, body)
}

///|
fn fortsubprog(def : Value) -> Value raise {
  let (type_, stype, name, params, body) = allgentran__subprog_parts(def)
  let mut r = mkffortsubprogdec(type_, stype, name, params)
  if symval(q_n_stargendecs).truthy() {
    r = append(r, fortdecs(symtabget(name, q_ear_decs)))
  }
  r = append(r, mapcan(s => fortstmt(s), body))
  if symval(q_n_stargendecs).truthy() {
    symtabrem(name, Nil) |> ignore
    symtabrem(name, q_ear_decs) |> ignore
  }
  r
}

///|
fn fortdecs(decs : Value) -> Value raise {
  mapcan(tl => mkffortdec(car(tl), cdr(tl)), formtypelists(decs))
}

///|
/// Print floats as "double" n.0d0.
fn dbl(n : Value) -> Value raise {
  // (= (float 1) 1.0d0) holds: FLOAT makes double floats in Maxima
  if floatp(n) {
    double(n)
  } else {
    n
  }
}

///|
fn fortexp(exp_ : Value) -> Value raise {
  if symval(q_d_dblfloat).truthy() {
    mapcar(n => dbl(n), fortexp1(exp_, Fix(0L)))
  } else {
    fortexp1(exp_, Fix(0L))
  }
}

///|
/// Token list of an infix operator expression, or of a function call
/// `name(arg, ...)`; shared by the Fortran, Ratfor and C translations.
/// sub: the translation of a subexpression at a precedence; op_of and
/// prec_of: the operator token and precedence of a Lisp operator.
fn allgentran__infix(
  exp_ : Value,
  wtin : Value,
  sub : (Value, Value) -> Value raise,
  op_of : (Value) -> Value raise,
  prec_of : (Value) -> Value raise,
) -> Value raise {
  let wt = prec_of(car(exp_))
  let op = op_of(car(exp_))
  let mut res = sub(cadr(exp_), wt)
  let mut exp_ = cdr(exp_)
  if eq(op, q_op_plus) {
    while true {
      exp_ = cdr(exp_)
      if !exp_.truthy() {
        break
      }
      let res1 = sub(car(exp_), wt)
      if eq(car(res1), q_op_h_) || (numberp(car(res1)) && minusp(car(res1))) {
        res = append(res, res1)
      } else {
        res = append(res, cons(op, res1))
      }
    }
  } else {
    while true {
      exp_ = cdr(exp_)
      if !exp_.truthy() {
        break
      }
      res = append(res, cons(op, sub(car(exp_), wt)))
    }
  }
  if num_lt(wt, wtin) {
    aconc(cons(q_op_u0028, res), q_op_u0029)
  } else {
    res
  }
}

///|
fn allgentran__unary(
  exp_ : Value,
  wtin : Value,
  sub : (Value, Value) -> Value raise,
  op_of : (Value) -> Value raise,
  prec_of : (Value) -> Value raise,
) -> Value raise {
  let wt = prec_of(car(exp_))
  let res = cons(op_of(car(exp_)), sub(cadr(exp_), wt))
  if num_lt(wt, wtin) {
    aconc(cons(q_op_u0028, res), q_op_u0029)
  } else {
    res
  }
}

///|
fn allgentran__call(
  exp_ : Value,
  sub : (Value, Value) -> Value raise,
) -> Value raise {
  let mut res = cons(car(exp_), cons(q_op_u0028, sub(cadr(exp_), Fix(0L))))
  let mut exp_ = cdr(exp_)
  while true {
    exp_ = cdr(exp_)
    if !exp_.truthy() {
      break
    }
    res = append(res, cons(q_op_cm, sub(car(exp_), Fix(0L))))
  }
  aconc(res, q_op_u0029)
}

///|
fn allgentran__arith_or_log_op_p(op : Value) -> Bool {
  memq(op, symval(q_ear_lisparithexpops)).truthy() ||
  memq(op, symval(q_ear_lisplogexpops)).truthy()
}

///|
fn fortexp1(exp_ : Value, wtin : Value) -> Value raise {
  if atom(exp_) {
    list1(fortranname(exp_))
  } else if eq(car(exp_), q_data) {
    fortdata(exp_)
  } else if eq(car(exp_), q_literal) {
    fortliteral(exp_)
  } else if null(cdr(exp_)) {
    exp_
  } else if memq(car(exp_), list2(q_minus, q_not)).truthy() {
    allgentran__unary(exp_, wtin, fortexp1, fortranop, fortranprecedence)
  } else if allgentran__arith_or_log_op_p(car(exp_)) {
    allgentran__infix(exp_, wtin, fortexp1, fortranop, fortranprecedence)
  } else {
    allgentran__call(exp_, fortexp1)
  }
}

///|
fn fortranname(name : Value) -> Value raise {
  if symbolp(name) {
    let n = get(name, q_ear_fortranname)
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
fn fortranop(op : Value) -> Value raise {
  let o = get(op, q_ear_fortranop)
  if o.truthy() {
    o
  } else {
    op
  }
}

///|
fn fortranprecedence(op : Value) -> Value raise {
  let p = get(op, q_ear_fortranprecedence)
  if p.truthy() {
    p
  } else {
    Fix(9L)
  }
}

///|
fn fortstmt(stmt : Value) -> Value raise {
  if null(stmt) {
    Nil
  } else if member(stmt, list2(q_d_begin_group, q_d_end_group)).truthy() {
    Nil
  } else if lisplabelp(stmt).truthy() {
    fortstmtno(stmt)
  } else if eq(car(stmt), q_data) {
    fortdata(stmt)
  } else if eq(car(stmt), q_literal) {
    fortliteral(stmt)
  } else if lispreadp(stmt).truthy() {
    fortread(stmt)
  } else if lispassignp(stmt).truthy() {
    fortassign(stmt)
  } else if lispprintp(stmt).truthy() {
    fortwrite(stmt)
  } else if lispcondp(stmt).truthy() {
    fortif(stmt)
  } else if lispbreakp(stmt).truthy() {
    fortbreak(stmt)
  } else if lispgop(stmt).truthy() {
    fortgoto(stmt)
  } else if lispreturnp(stmt).truthy() {
    fortreturn(stmt)
  } else if lispstopp(stmt).truthy() {
    fortstop(stmt)
  } else if lispendp(stmt).truthy() {
    fortend(stmt)
  } else if lispdop(stmt).truthy() {
    fortloop(stmt)
  } else if lispstmtgpp(stmt).truthy() {
    fortstmtgp(stmt)
  } else if lispdefp(stmt).truthy() {
    fortsubprog(stmt)
  } else if lispcallp(stmt).truthy() {
    fortcall(stmt)
  } else {
    Nil
  }
}

///|
fn fortassign(stmt : Value) -> Value raise {
  mkffortassign(cadr(stmt), caddr(stmt))
}

///|
fn fortbreak(stmt : Value) -> Value raise {
  ignore(stmt)
  let eols = symval(q_ear_endofloopstack)
  if null(eols) {
    gentranerr(q_e, Nil, Str("break not inside loop - cannot be translated"))
  } else if atom(car(eols)) {
    let n1 = genstmtno()
    rplaca(eols, list2(car(eols), n1)) |> ignore
    mkffortgo(n1)
  } else {
    mkffortgo(cadar(eols))
  }
}

///|
fn fortcall(stmt : Value) -> Value raise {
  mkffortcall(car(stmt), cdr(stmt))
}

///|
/// Close a loop: the continue of a break out of it, then pop the loop.
fn allgentran__end_loop(
  result : Value,
  cont : (Value) -> Value raise,
) -> Value raise {
  let mut result = result
  let eols = symval(q_ear_endofloopstack)
  if listp(car(eols)) {
    result = append(result, cont(cadar(eols)))
  }
  set(q_ear_endofloopstack, cdr(eols)) |> ignore
  result
}

///|
fn fortdo(
  var_ : Value,
  lo : Value,
  nextexp : Value,
  exitcond : Value,
  body : Value,
) -> Value raise {
  let n1 = genstmtno()
  set(q_ear_endofloopstack, cons(n1, symval(q_ear_endofloopstack))) |> ignore
  let hi = car(delete1(q_greaterp, delete1(q_lessp, delete1(var_, exitcond))))
  let incr = car(delete1(q_plus, delete1(var_, nextexp)))
  let mut result = mkffortdo(n1, var_, lo, hi, incr)
  indentfortlevel(Fix(1L)) |> ignore
  result = append(result, mapcan(st => fortstmt(st), body))
  indentfortlevel(Fix(-1L)) |> ignore
  result = append(result, mkffortcontinue(n1))
  allgentran__end_loop(result, mkffortcontinue)
}

///|
fn fortend(stmt : Value) -> Value raise {
  ignore(stmt)
  mkffortend()
}

///|
fn fortfor(
  var_ : Value,
  lo : Value,
  nextexp : Value,
  exitcond : Value,
  body : Value,
) -> Value raise {
  let mut nextexp = nextexp
  let n1 = genstmtno()
  let n2 = genstmtno()
  set(q_ear_endofloopstack, cons(n2, symval(q_ear_endofloopstack))) |> ignore
  let mut result : Value = Nil
  if var_.truthy() {
    result = mkffortassign(var_, lo)
  }
  if exitcond.truthy() {
    result = append(result, append(list2(n1, q_op_sp), mkffortifgo(exitcond, n2)))
  } else {
    result = append(result, mkffortcontinue(n1))
  }
  indentfortlevel(Fix(1L)) |> ignore
  result = append(result, mapcan(st => fortstmt(st), body))
  if nextexp.truthy() {
    if equal(nextexp, list1(Nil)) {
      nextexp = Nil
    }
    result = append(result, mkffortassign(var_, nextexp))
  }
  result = append(result, mkffortgo(n1))
  indentfortlevel(Fix(-1L)) |> ignore
  result = append(result, mkffortcontinue(n2))
  allgentran__end_loop(result, mkffortcontinue)
}

///|
/// The statement number of a label (assigned on first use).
fn allgentran__label_stmtno(label : Value) -> Value raise {
  let n = get(label, q_ear_stmtno)
  if n.truthy() {
    n
  } else {
    put(label, q_ear_stmtno, genstmtno())
  }
}

///|
fn fortgoto(stmt : Value) -> Value raise {
  mkffortgo(allgentran__label_stmtno(cadr(stmt)))
}

///|
fn fortif(stmt : Value) -> Value raise {
  let stmt = cdr(stmt)
  if onep(int(length(stmt))).truthy() {
    if equal(caar(stmt), t) {
      mapcan(st => fortstmt(st), cdar(stmt))
    } else {
      let n1 = genstmtno()
      let mut res = mkffortifgo(list2(q_not, caar(stmt)), n1)
      indentfortlevel(Fix(1L)) |> ignore
      res = append(res, mapcan(st => fortstmt(st), cdar(stmt)))
      indentfortlevel(Fix(-1L)) |> ignore
      append(res, mkffortcontinue(n1))
    }
  } else {
    let n1 = genstmtno()
    let n2 = genstmtno()
    let mut res = mkffortifgo(list2(q_not, caar(stmt)), n1)
    indentfortlevel(Fix(1L)) |> ignore
    res = append(res, mapcan(st => fortstmt(st), cdar(stmt)))
    res = append(res, mkffortgo(n2))
    indentfortlevel(Fix(-1L)) |> ignore
    res = append(res, mkffortcontinue(n1))
    indentfortlevel(Fix(1L)) |> ignore
    res = append(res, fortif(cons(q_cond, cdr(stmt))))
    indentfortlevel(Fix(-1L)) |> ignore
    append(res, mkffortcontinue(n2))
  }
}

///|
fn fortliteral(stmt : Value) -> Value raise {
  mapcan(
    a => if equal(a, q_d_tab) {
      list1(mkforttab())
    } else if equal(a, q_d_cr) {
      list1(mkterpri())
    } else if listp(a) {
      fortexp(a)
    } else {
      list1(a)
    },
    cdr(stmt),
  )
}

///|
fn fortdata(stmt : Value) -> Value raise {
  append(
    list([mkforttab(), Str("data "), cadr(stmt), q_op_sl]),
    append(addcom(cddr(stmt)), list1(q_op_sl)),
  )
}

///|
fn addcom(nl : Value) -> Value raise {
  if null(nl) {
    Nil
  } else if null(cdr(nl)) {
    nl
  } else {
    cons(car(nl), cons(symval(q_comma_star), addcom(cdr(nl))))
  }
}

///|
/// The parts (var lo nextexp exitcond) of a simple do loop.
fn allgentran__loop_parts(stmt : Value) -> (Value, Value, Value, Value) raise {
  let mut var_ = cadr(stmt)
  let mut lo : Value = Nil
  let mut nextexp : Value = Nil
  if var_.truthy() {
    lo = cadar(var_)
    if length(car(var_)) == 3 {
      let n = caddar(var_)
      nextexp = if n.truthy() { n } else { list1(Nil) }
    }
    var_ = caar(var_)
  }
  let mut exitcond = caddr(stmt)
  if exitcond.truthy() {
    exitcond = car(exitcond)
  }
  (var_, lo, nextexp, exitcond)
}

///|
fn allgentran__do_loop_p(
  var_ : Value,
  lo : Value,
  nextexp : Value,
  exitcond : Value,
) -> Bool raise {
  var_.truthy() &&
  lo.truthy() &&
  equal(car(nextexp), q_plus) &&
  member(var_, nextexp).truthy() &&
  member(car(exitcond), list2(q_greaterp, q_lessp)).truthy() &&
  member(var_, exitcond).truthy()
}

///|
fn allgentran__repeat_loop_p(
  var_ : Value,
  lo : Value,
  nextexp : Value,
  exitcond : Value,
) -> Bool raise {
  var_.truthy() &&
  !lo.truthy() &&
  lisplogexpp(nextexp).truthy() &&
  equal(exitcond, var_)
}

///|
fn fortloop(stmt : Value) -> Value raise {
  if complexdop(stmt).truthy() {
    return fortstmt(seqtogp(simplifydo(stmt)))
  }
  let (var_, lo, nextexp, exitcond) = allgentran__loop_parts(stmt)
  let body = cdddr(stmt)
  if allgentran__do_loop_p(var_, lo, nextexp, exitcond) {
    fortdo(var_, lo, nextexp, exitcond, body)
  } else if exitcond.truthy() && !var_.truthy() {
    fortwhile(exitcond, body)
  } else if allgentran__repeat_loop_p(var_, lo, nextexp, exitcond) {
    fortrepeat(body, nextexp)
  } else {
    fortfor(var_, lo, nextexp, exitcond, body)
  }
}

///|
fn fortread(stmt : Value) -> Value raise {
  mkffortread(cadr(stmt))
}

///|
fn fortrepeat(body : Value, exitcond : Value) -> Value raise {
  let n = genstmtno()
  set(q_ear_endofloopstack, cons(q_dummy, symval(q_ear_endofloopstack)))
  |> ignore
  let mut result = mkffortcontinue(n)
  indentfortlevel(Fix(1L)) |> ignore
  result = append(result, mapcan(st => fortstmt(st), body))
  indentfortlevel(Fix(-1L)) |> ignore
  result = append(result, mkffortifgo(list2(q_not, exitcond), n))
  allgentran__end_loop(result, mkffortcontinue)
}

///|
fn fortreturn(stmt : Value) -> Value raise {
  if onep(int(length(stmt))).truthy() {
    mkffortreturn()
  } else if !eq(car(symval(q_ear_symboltable)), q_ear_main) {
    append(
      mkffortassign(car(symval(q_ear_symboltable)), cadr(stmt)),
      mkffortreturn(),
    )
  } else {
    gentranerr(q_e, Nil, Str("return not inside function - cannot be translated"))
  }
}

///|
fn fortstmtgp(stmtgp : Value) -> Value raise {
  let stmts = if equal(car(stmtgp), q_progn) {
    cdr(stmtgp)
  } else {
    cddr(stmtgp)
  }
  mapcan(stmt => fortstmt(stmt), stmts)
}

///|
fn fortstmtno(label : Value) -> Value raise {
  mkffortcontinue(allgentran__label_stmtno(label))
}

///|
fn fortstop(stmt : Value) -> Value raise {
  ignore(stmt)
  mkffortstop()
}

///|
fn fortwhile(exitcond : Value, body : Value) -> Value raise {
  let n1 = genstmtno()
  let n2 = genstmtno()
  set(q_ear_endofloopstack, cons(n2, symval(q_ear_endofloopstack))) |> ignore
  let mut result = append(list2(n1, q_op_sp), mkffortifgo(exitcond, n2))
  indentfortlevel(Fix(1L)) |> ignore
  result = append(result, mapcan(st => fortstmt(st), body))
  result = append(result, mkffortgo(n1))
  indentfortlevel(Fix(-1L)) |> ignore
  result = append(result, mkffortcontinue(n2))
  allgentran__end_loop(result, mkffortcontinue)
}

///|
fn fortwrite(stmt : Value) -> Value raise {
  mkffortwrite(cdr(stmt))
}

///|
fn mkffortassign(lhs : Value, rhs : Value) -> Value raise {
  append(
    append(cons(mkforttab(), fortexp(lhs)), cons(q_op_eq, fortexp(rhs))),
    list1(mkterpri()),
  )
}

///|
/// `(f1 , f2 , ...)` tokens of a parameter list translated by tr.
fn allgentran__params(
  params : Value,
  tr : (Value) -> Value raise,
) -> Value raise {
  mapcan(p => tr(p), insertcommas(params))
}

///|
fn mkffortcall(fname : Value, params : Value) -> Value raise {
  let mut params = params
  if params.truthy() {
    params = append(
      append(list1(q_op_u0028), allgentran__params(params, fortexp)),
      list1(q_op_u0029),
    )
  }
  append(
    append(list3(mkforttab(), q_call, q_op_sp), fortexp(fname)),
    append(params, list1(mkterpri())),
  )
}

///|
fn mkffortcontinue(stmtno : Value) -> Value raise {
  list([stmtno, q_op_sp, mkforttab(), q_continue, mkterpri()])
}

///|
fn mkffortdec(type_ : Value, varlist : Value) -> Value raise {
  let type_ = if type_.truthy() { type_ } else { q_dimension }
  let varlist = allgentran__params(varlist, fortexp)
  if implicitp(type_).truthy() {
    append(
      list([mkforttab(), type_, q_op_sp, q_op_u0028]),
      append(varlist, list2(q_op_u0029, mkterpri())),
    )
  } else {
    append(list3(mkforttab(), type_, q_op_sp), aconc(varlist, mkterpri()))
  }
}

///|
fn mkffortdo(
  stmtno : Value,
  var_ : Value,
  lo : Value,
  hi : Value,
  incr : Value,
) -> Value raise {
  let mut incr = incr
  if onep(incr).truthy() {
    incr = Nil
  } else if incr.truthy() {
    incr = cons(q_op_cm, fortexp(incr))
  }
  append(
    append(
      append(list([mkforttab(), q_do, q_op_sp, stmtno, q_op_sp]), fortexp(var_)),
      append(cons(q_op_eq, fortexp(lo)), cons(q_op_cm, fortexp(hi))),
    ),
    append(incr, list1(mkterpri())),
  )
}

///|
fn mkffortend() -> Value raise {
  list3(mkforttab(), q_end, mkterpri())
}

///|
fn mkffortgo(stmtno : Value) -> Value raise {
  list([mkforttab(), q_goto, q_op_sp, stmtno, mkterpri()])
}

///|
fn mkffortifgo(exp_ : Value, stmtno : Value) -> Value raise {
  append(
    append(list([mkforttab(), q_if, q_op_sp, q_op_u0028]), fortexp(exp_)),
    list([q_op_u0029, q_op_sp, q_goto, q_op_sp, stmtno, mkterpri()]),
  )
}

///|
fn mkffortread(var_ : Value) -> Value raise {
  append(
    list([mkforttab(), q_read, q_op_u0028_star_cm_star_u0029, q_op_sp]),
    append(fortexp(var_), list1(mkterpri())),
  )
}

///|
fn mkffortreturn() -> Value raise {
  list3(mkforttab(), q_return, mkterpri())
}

///|
fn mkffortstop() -> Value raise {
  list3(mkforttab(), q_stop, mkterpri())
}

///|
fn mkffortsubprogdec(
  type_ : Value,
  stype : Value,
  name : Value,
  params : Value,
) -> Value raise {
  let mut params = params
  if params.truthy() {
    params = aconc(
      cons(q_op_u0028, allgentran__params(params, fortexp)),
      q_op_u0029,
    )
  }
  let head = if type_.truthy() {
    list([mkforttab(), type_, q_op_sp, stype, q_op_sp])
  } else {
    list3(mkforttab(), stype, q_op_sp)
  }
  append(append(head, fortexp(name)), aconc(params, mkterpri()))
}

///|
fn quotstring(arg : Value) -> Value raise {
  arg
}

///|
fn mkffortwrite(arglist : Value) -> Value raise {
  append(
    append(
      list([mkforttab(), q_write, q_op_u0028_star_cm_star_u0029, q_op_sp]),
      allgentran__params(mapcar(a => quotstring(a), arglist), fortexp),
    ),
    list1(mkterpri()),
  )
}

///|
fn mkforttab() -> Value raise {
  list2(q_forttab, num_sub(symval(q_d_fortcurrind), Fix(6L)))
}

///|
fn indentfortlevel(n : Value) -> Value raise {
  set(
    q_d_fortcurrind,
    num_add(symval(q_d_fortcurrind), num_mul(n, symval(q_d_tablen))),
  )
}
