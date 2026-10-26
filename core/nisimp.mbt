// Port of src/nisimp.lisp: programs for the LET, LETSIMP, LETRULES and
// REMLET commands.  These programs use the names LETSIMPTREE and LETRULES
// on the property list of atoms.  Except for the top level programs all
// program names have the prefix NIS.

///|
/// `'#.(intern (format nil " ~A " 'where))`
let nisimp__q_where : Value = sym(" where ")

///|
fn let_rule_setter(var_ : Value, val : Value) -> Value raise {
  if eq(var_, q_d_default_let_rule_package) {
    merr("assignment: cannot assign to default_let_rule_package.", [])
  } else if eq(var_, q_d_current_let_rule_package) &&
    memalike(val, cdr(symval(q_d_let_rule_packages))) is Nil {
    merr("assignment: ~M is not a rule package.", [val])
  } else if eq(var_, q_d_let_rule_packages) {
    merr(
      "assignment: cannot assign to let_rule_packages.~%assignment: call 'let' to create let rule packages.",
      [],
    )
  } else {
    Nil
  }
}

///|
fn d_let(l : Value) -> Value raise {
  let mut l = cdr(l)
  if cdr(l) is Nil {
    wna_err(q_d_let) |> ignore
  }
  // LET([PATTERN,REPL,PRED,ARG1,...,ARGN],NAME)
  let rb = bind(q_d_ratfac, Nil)
  defer unbind(rb)
  let mut treename : Value = Nil
  // LET(PATTERN,REPL,PRED,ARG1,...,ARGN)
  if atom(car(l)) {
    treename = symval(q_d_current_let_rule_package)
  } else if eq(q_mlist, caaar(l)) {
    treename = cadr(l)
    if !symbolp(treename) {
      improper_arg_err(treename, q_d_let) |> ignore
    }
    l = cdar(l)
  } else {
    treename = symval(q_d_current_let_rule_package)
  }
  let bs = bind_all([
    (q_nistree, mget(treename, q_letsimptree)),
    (q_nisrules, mget(treename, q_letrules)),
  ])
  defer unbind_all(bs)
  let pat = strip_lineinfo(meval(car(l)))
  let replacement = cdr(l)
  let pattern = if atom(pat) {
    list1(pat)
  } else if eq(caar(pat), q_mtimes) {
    cdr(pat)
  } else {
    list1(pat)
  }
  set(q_nistree, nislet(symval(q_nistree), pattern, replacement)) |> ignore
  if treename.truthy() {
    mputprop(treename, symval(q_nistree), q_letsimptree) |> ignore
    add2lnc(treename, symval(q_d_let_rule_packages)) |> ignore
  }
  nonsymchk(caddr(l), q_d_let) |> ignore
  let text = append(
    list3(list1(q_mtext), pat, q_op_sp___gt_sp),
    if cddr(l).truthy() {
      list3(cadr(l), nisimp__q_where, cons(list1(caddr(l)), cdddr(l)))
    } else {
      replacement
    },
  )
  set(q_nisrules, append(list1(text), symval(q_nisrules))) |> ignore
  if treename.truthy() {
    mputprop(treename, symval(q_nisrules), q_letrules) |> ignore
  }
  text
}

///|
fn nislet(tree : Value, list_ : Value, function : Value) -> Value raise {
  let mut tree = tree
  let mut permlist = nispermutations(list_)
  while permlist.truthy() {
    tree = nistreebuilder(tree, car(permlist), function)
    permlist = cdr(permlist)
  }
  tree
}

///|
fn nispermutations(llist : Value) -> Value raise {
  if cdr(llist) is Nil {
    return list1(llist)
  }
  let mut llist = llist
  let mut permlist : Value = Nil
  let mut a : Value = Nil
  while true {
    permlist = append(
      nisaddon(car(llist), nispermutations(append(a, cdr(llist)))),
      permlist,
    )
    if cdr(llist) is Nil {
      return permlist
    }
    a = cons(car(llist), a)
    llist = cdr(llist)
  }
  permlist
}

///|
fn nisaddon(x : Value, llist : Value) -> Value raise {
  if llist.truthy() {
    cons(cons(x, car(llist)), nisaddon(x, cdr(llist)))
  } else {
    Nil
  }
}

///|
fn nistreebuilder(tree : Value, perm : Value, function : Value) -> Value raise {
  if perm is Nil {
    cons(list1(function), tree)
  } else if tree is Nil {
    list1(cons(car(perm), nistreebuilder(Nil, cdr(perm), function)))
  } else if equal(car(perm), caar(tree)) {
    nisswcar(
      tree,
      nisswcdr(car(tree), nistreebuilder(cdar(tree), cdr(perm), function)),
    )
  } else {
    nisswcdr(tree, nistreebuilder(cdr(tree), perm, function))
  }
}

///|
fn nisswcar(x : Value, y : Value) -> Value raise {
  cons(y, cdr(x))
}

///|
fn nisswcdr(x : Value, y : Value) -> Value raise {
  cons(car(x), y)
}

///|
fn d_remlet(x : Value) -> Value raise {
  let x = cdr(x)
  // REMLET(PROD,NAME) REMLET(PROD) REMLET() REMLET(FALSE,NAME)
  let mut treename : Value = Nil
  if cddr(x).truthy() {
    wna_err(q_d_remlet) |> ignore
  } else if cdr(x) is Nil {
    treename = symval(q_d_current_let_rule_package)
  } else {
    treename = cadr(x)
    if !symbolp(treename) {
      improper_arg_err(treename, q_d_remlet) |> ignore
    }
  }
  let pattern = strip_lineinfo(meval(car(x)))
  if pattern is Nil || eq(q_d_all, pattern) {
    set(q_nisrules, Nil) |> ignore
    set(q_nistree, Nil) |> ignore
    if !eq(treename, q_d_default_let_rule_package) {
      set(
        q_d_let_rule_packages,
        matrun__delete1(treename, symval(q_d_let_rule_packages)),
      )
      |> ignore
    }
  } else {
    set(q_nistree, mget(treename, q_letsimptree)) |> ignore
    let text = nisremlet(pattern)
    if text.truthy() {
      return text
    }
    if symval(q_nistree).truthy() {
      set(q_nisrules, nistreelister(mget(treename, q_letrules), pattern))
      |> ignore
    } else {
      set(q_nisrules, Nil) |> ignore
    }
  }
  // a
  mputprop(treename, symval(q_nistree), q_letsimptree) |> ignore
  mputprop(treename, symval(q_nisrules), q_letrules) |> ignore
  q_d_done
}

///|
fn nistreelister(llist : Value, pattern : Value) -> Value raise {
  let mut llist = llist
  let mut x : Value = Nil
  while true {
    if alike1(pattern, cadar(llist)).truthy() {
      return append(x, cdr(llist))
    }
    x = append(x, list1(car(llist)))
    llist = cdr(llist)
  }
  x
}

///|
fn nisremlet(pat : Value) -> Value raise {
  let llist = if mtimesp(pat).truthy() { cdr(pat) } else { ncons(pat) }
  set(q_nisflag, t) |> ignore
  let mut x = symval(q_nistree)
  let mut permlist = nispermutations(llist)
  while true {
    if permlist is Nil {
      set(q_nistree, x) |> ignore
      return Nil
    }
    x = nistreetrimmer(car(permlist), x)
    if symval(q_nisflag) is Nil {
      merr("remlet: no rule found: ~M", [pat]) |> ignore
    }
    permlist = cdr(permlist)
  }
  Nil
}

///|
fn nistreetrimmer(perm : Value, tree : Value) -> Value raise {
  if perm is Nil {
    if tree is Nil {
      set(q_nisflag, Nil)
    } else if cdar(tree) is Nil {
      set(q_nisflag, caar(tree)) |> ignore
      cdr(tree)
    } else {
      nisswcdr(tree, nistreetrimmer(Nil, cdr(tree)))
    }
  } else if tree is Nil {
    set(q_nisflag, Nil)
  } else if equal(car(perm), caar(tree)) {
    let x = nistreetrimmer(cdr(perm), cdar(tree))
    if x is Nil {
      cdr(tree)
    } else {
      nisswcar(tree, nisswcdr(car(tree), x))
    }
  } else {
    nisswcdr(tree, nistreetrimmer(perm, cdr(tree)))
  }
}

///|
fn d_letrules(name : Value) -> Value raise {
  let name = cdr(name) // LETRULES(NAME)
  let treename = if name.truthy() {
    car(name)
  } else {
    symval(q_d_current_let_rule_package)
  }
  if !symbolp(treename) {
    improper_arg_err(treename, q_d_letrules) |> ignore
  }
  set(q_nistree, mget(treename, q_letsimptree)) |> ignore
  set(q_nisrules, mget(treename, q_letrules)) |> ignore
  d_disp(symval(q_nisrules))
}

///|
/// letsimp(expr,tree1,...,treen)
fn d_letsimp(form : Value) -> Value raise {
  let mut form = cdr(form)
  let first = car(form)
  form = cdr(form)
  let mut expr = strip_lineinfo(meval(first))
  let sw = d_ratp(expr).truthy()
  let rb = bind(q_d_ratfac, Nil)
  defer unbind(rb)
  let pv = if sw {
    []
  } else {
    bind_all([(q_varlist, symval(q_varlist)), (q_genvar, symval(q_genvar))])
  }
  defer unbind_all(pv)
  if sw && memq(q_trunc, cdar(expr)).truthy() {
    expr = d_taytorat(expr)
  }
  let packages = if form.truthy() {
    form
  } else {
    list1(symval(q_d_current_let_rule_package))
  }
  for rulepackage in packages.iter() {
    if !symbolp(rulepackage) {
      improper_arg_err(rulepackage, q_d_letsimp) |> ignore
    }
    set(q_nistree, mget(rulepackage, q_letsimptree)) |> ignore
    if symval(q_nistree).truthy() {
      // Whereas nisletsimp returns an expression in general
      // representation, the original expr might be in CRE form.
      // Regardless, we use ratf to make sure varlist and genvar
      // know of expr's kernels.
      expr = nisletsimp(nformat(if atom(expr) { expr } else { ratf(expr) }))
    }
  }
  if sw {
    ratf(expr)
  } else {
    expr
  }
}

///|
fn nisletsimp(e : Value) -> Value raise {
  let mut e = e
  let mut x : Value = Nil
  if mnump(e).truthy() {
    e
  } else if (
      atom(e) &&
      ({
        x = ncons(e)
        x.truthy()
      })
    ) ||
    (
      eq(caar(e), q_mtimes) &&
      ({
        x = cdr(e)
        x.truthy()
      })
    ) {
    x = nisnewlist(x)
    if x.truthy() {
      nisletsimp(d_ratexpand(cons(list1(q_mtimes), x)))
    } else {
      e
    }
  } else if ({
      let o = caar(e)
      eq(o, q_mplus) ||
      eq(o, q_mequal) ||
      eq(o, q_mlist) ||
      eq(o, q_d_matrix) ||
      eq(o, q_mminus)
    }) {
    cons(remove(q_simp, car(e)), mapcar(y => nisletsimp(y), cdr(e)))
  } else if eq(caar(e), q_mrat) ||
    (
      eq(caar(e), q_mquotient) &&
      ({
        e = ratf(e)
        e.truthy()
      })
    ) {
    nisletsimprat(e)
  } else {
    // A kernel (= product of 1 element)
    x = nisnewlist(ncons(e))
    if x.truthy() {
      nisletsimp(d_ratexpand(cons(list1(q_mtimes), x)))
    } else {
      e
    }
  }
}

///|
fn nisletsimprat(e : Value) -> Value raise {
  let mut num = cadr(e)
  let mut denom = cddr(e)
  let rb = bind(q_d_ratexpand, Nil)
  defer unbind(rb)
  if symval(q_d_letvarsimp).truthy() {
    set(q_varlist, mapcar(v => nisletsimp(v), symval(q_varlist))) |> ignore
  }
  with_special(q_d_ratexpand, t, fn() raise {
    // Construct new CREs based on the numerator and denominator of E and
    // disrep them in the VARLIST and GENVAR context from E.
    //
    // NISLETSIMP can change VARLIST and GENVAR, so the order of the PDIS
    // and NISLETSIMP forms matter here.  PDISing and NISLETSIMPing the
    // numerator before moving on to the denominator is not correct.
    with_specials([(q_varlist, mrat_varlist(e)), (q_genvar, mrat_genvar(e))], fn() raise {
      num = pdis(num)
      denom = pdis(denom)
    })
    num = nisletsimp(num)
    denom = nisletsimp(denom)
  })
  let e = list3(list1(q_mquotient), num, denom)
  if symval(q_d_letrat).truthy() {
    nisletsimp(d_ratexpand(e))
  } else {
    e
  }
}

///|
fn nisnewlist(llist : Value) -> Value raise {
  let x = nissearch(llist, symval(q_nistree), Nil)
  if x.truthy() {
    nisreplace(llist, x)
  } else {
    Nil
  }
}

///|
fn nissearch(x : Value, y : Value, z : Value) -> Value raise {
  if y is Nil {
    return Nil
  }
  let inner = nisinnernull(y)
  if inner.truthy() {
    return nisfix(inner, z)
  }
  if x is Nil {
    return Nil
  }
  let mut yy = y
  while true {
    // a
    let mut xx = x
    while true {
      // b
      let bind_ = nismatch(car(xx), caar(yy), z)
      if bind_.truthy() {
        let path = nissearch(cdr(xx), cdar(yy), cdr(bind_))
        if path.truthy() {
          return cons(car(bind_), path)
        }
      }
      xx = cdr(xx)
      if xx is Nil {
        break
      }
    }
    yy = cdr(yy)
    if yy is Nil {
      return Nil
    }
  }
  Nil
}

///|
fn nisinnernull(x : Value) -> Value raise {
  if x is Nil {
    Nil
  } else if cdar(x) is Nil {
    caar(x)
  } else {
    nisinnernull(cdr(x))
  }
}

///|
fn nisfix(funperd : Value, argasslist : Value) -> Value raise {
  if argasslist is Nil {
    return car(funperd)
  }
  let argasslist = nisnumberpicker(argasslist)
  let args = maplist(l => caar(l), argasslist)
  let bindings = maplist(l => cdar(l), argasslist)
  let mut function : Value = Nil
  let mut flag = false
  // (mbinding (args bindings) ...)
  let mut win = false
  defer (if win { munbind(args) |> ignore })
  mbind(args, bindings, Nil) |> ignore
  win = true
  function = car(funperd)
  let perd = cdr(funperd)
  if perd.truthy() {
    if meval(perd) is Nil {
      flag = true
    }
  }
  if !flag {
    function = meval(function)
  }
  if flag {
    Nil
  } else {
    list1(function)
  }
}

///|
fn nisnumberpicker(x : Value) -> Value raise {
  if x is Nil {
    Nil
  } else if !symbolp(caar(x)) || kindp(caar(x), q_d_constant).truthy() {
    // Skip over numbers and constants
    nisnumberpicker(cdr(x))
  } else {
    nisswcdr(x, nisnumberpicker(cdr(x)))
  }
}

///|
fn nismatch(a : Value, b : Value, c : Value) -> Value raise {
  let mut c = c
  let x = nisextract(a)
  let y = nisextract(b)
  if listp(cadr(y)) {
    if listp(cadr(x)) &&
      equal(car(x), car(y)) &&
      ({
        c = cons(cons(car(x), car(y)), c)
        c.truthy()
      }) &&
      ({
        c = nisargschecker(cadr(x), cadr(y), c)
        c.truthy()
      }) {
      let newexpt = nisexpocheck(cddr(x), cddr(y), c)
      if newexpt.truthy() {
        if equal(list1(q_rat), car(newexpt)) {
          return cons(cons(a, nisbuild(x, newexpt)), c)
        } else {
          return cons(nisimp__dummy(a), newexpt)
        }
      }
    }
    return Nil
  }
  c = nisargmatch(niskernel(a), car(y), c)
  if c.truthy() {
    let newexpt = nisexpocheck(cddr(x), cddr(y), c)
    if newexpt.truthy() {
      if equal(list1(q_rat), car(newexpt)) {
        return cons(cons(a, nisbuild(x, newexpt)), c)
      } else {
        return cons(nisimp__dummy(a), newexpt)
      }
    }
  }
  Nil
}

///|
/// `(cons a '(dummy 0 (0 0)))`
fn nisimp__dummy(a : Value) -> Value {
  cons(a, list3(q_dummy, Fix(0L), list2(Fix(0L), Fix(0L))))
}

///|
fn niskernel(a : Value) -> Value raise {
  if mexptp(a).truthy() {
    cadr(a)
  } else {
    a
  }
}

///|
fn nisextract(x : Value) -> Value raise {
  if atom(x) || eq(caar(x), q_rat) {
    cons(x, cons(t, Fix(1L)))
  } else if eq(q_mexpt, caar(x)) {
    if atom(cadr(x)) {
      cons(cadr(x), cons(t, caddr(x)))
    } else {
      cons(
        if memq(q_array, cdr(caadr(x))).truthy() {
          list2(caaadr(x), q_array)
        } else {
          caaadr(x)
        },
        cons(cdadr(x), caddr(x)),
      )
    }
  } else {
    cons(
      if memq(q_array, cdar(x)).truthy() {
        list2(caar(x), q_array)
      } else {
        caar(x)
      },
      cons(cdr(x), Fix(1L)),
    )
  }
}

///|
fn nisargschecker(
  listargs : Value,
  treeargs : Value,
  argasslist : Value,
) -> Value raise {
  if listargs.truthy() && treeargs.truthy() {
    let c = nisargmatch(car(listargs), car(treeargs), argasslist)
    if c.truthy() {
      nisargschecker(cdr(listargs), cdr(treeargs), c)
    } else {
      Nil
    }
  } else if listargs.truthy() || treeargs.truthy() {
    Nil
  } else {
    argasslist
  }
}

///|
fn nisexpocheck(
  listpower : Value,
  treepower : Value,
  argasslist : Value,
) -> Value raise {
  let mut r : Value = Nil
  let mut s : Value = Nil
  if atom(treepower) {
    if numberp(treepower) {
      r = treepower
      s = Fix(1L)
    } else {
      return nisargmatch(listpower, treepower, argasslist)
    }
  } else {
    r = cadr(treepower)
    s = caddr(treepower)
    if !numberp(s) {
      return Nil
    }
  }
  // math
  let mut p : Value = Nil
  let mut q : Value = Nil
  if numberp(listpower) {
    p = listpower
    q = Fix(1L)
  } else if atom(listpower) {
    return Nil
  } else if eq(q_rat, caar(listpower)) {
    p = cadr(listpower)
    q = caddr(listpower)
  } else {
    return Nil
  }
  let xx = num_mul(num_mul(q, s), num_sub(num_mul(p, s), num_mul(q, r)))
  let a = num_lt(num_mul(r, s), Fix(0L))
  let b = num_lt(xx, Fix(0L))
  if !(a || b) || (a && (b || equal(Fix(0L), xx))) {
    return list3(list1(q_rat), xx, num_mul(q, s))
  }
  Nil
}

///|
fn nisargmatch(x : Value, y : Value, c : Value) -> Value raise {
  let mut w = c
  // up
  while w.truthy() {
    if eq(caar(w), y) {
      if alike1(cdar(w), x).truthy() {
        return c
      } else {
        return Nil
      }
    }
    w = cdr(w)
  }
  // down
  w = mget(y, q_matchdeclare)
  let out = if w is Nil {
    equal(x, y)
  } else if eq(car(w), q_d_true) || eq(car(w), t) {
    true
  } else if atom(car(w)) &&
    meval(cons(ncons(car(w)), append(cdr(w), list1(x)))).truthy() {
    true
  } else if !atom(car(w)) &&
    !atom(caar(w)) &&
    atom(caaar(w)) &&
    // If we arrive here, (CAR W) is a Maxima expression like ((FOO) ...)
    // If (CAR W) is a Maxima lambda expression, evaluate it via MFUNCALL.
    // Otherwise, append X and call MEVAL.
    // Note that "otherwise" includes Maxima lambda expressions with missing
    // arguments; in that case the expression is ((MQAPPLY) ((LAMBDA) ...))
    // and MEVAL is the way to go.
    (if eq(caaar(w), q_lambda) {
      mfuncall(car(w), list1(x))
    } else {
      meval(append(car(w), list1(x)))
    }).truthy() {
    true
  } else {
    false
  }
  if out {
    cons(cons(y, x), c)
  } else {
    Nil
  }
}

///|
fn nisbuild(x : Value, newexpt : Value) -> Value raise {
  list3(
    list1(q_mexpt),
    if listp(cadr(x)) {
      cons(if symbolp(car(x)) { ncons(car(x)) } else { car(x) }, cadr(x))
    } else {
      car(x)
    },
    newexpt,
  )
}

///|
fn nisreplace(llist : Value, asslist : Value) -> Value raise {
  if cdr(asslist) is Nil {
    cons(car(asslist), llist)
  } else if equal(car(llist), caar(asslist)) {
    if equal(Fix(0L), cadar(cdr(cddar(asslist)))) {
      nisreplace(cdr(llist), cdr(asslist))
    } else {
      cons(cdar(asslist), nisreplace(cdr(llist), cdr(asslist)))
    }
  } else {
    cons(car(llist), nisreplace(cdr(llist), asslist))
  }
}

///|
fn init_nisimp() -> Unit raise {
  putprop(q_d_letrat, t, q_evflag) |> ignore
  set(q_nisrules, Nil) |> ignore
  set(q_nistree, Nil) |> ignore
}
