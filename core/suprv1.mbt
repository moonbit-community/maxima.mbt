// Port of src/suprv1.lisp: top-level evaluation (meval*), input/output
// labels, kill, remvalue, alias, nounify/verbify, string, stringout,
// playback, errcatch/catch/throw, time, quit, status/sstatus.
//
// This file also holds a few helpers shared by the other top-level files
// (macsys, mload, dskfn): CL FORMAT with a leading ~& honoured against the
// destination stream, DELETE :COUNT 1, the RAT-ERROR-TO-MERROR and ERRCATCH
// macros, and a small evaluator for the restricted Lisp files written by
// save() (the port cannot load arbitrary Lisp code).

///|
/// `(format dest ctl args...)` where DEST follows CL conventions (NIL: return
/// a string, T: *standard-output*).  A leading "~&" is honoured against the
/// destination stream's column.
fn suprv1__fmt(dest : Value, ctl : String, args : Array[Value]) -> Value raise {
  let mut ctl = ctl
  if dest.truthy() && ctl.has_prefix("~&") {
    let st = if eq(dest, t) { symval(standard_output) } else { dest }
    fresh_line(stream=st) |> ignore
    ctl = ctl.substring(start=2)
  }
  if eq(dest, t) {
    format(symval(standard_output), ctl, args)
  } else {
    format(dest, ctl, args)
  }
}

///|
/// `(delete x l :count 1 :test #'eq)`
fn suprv1__delete1(x : Value, l : Value) -> Value {
  suprv1__delete1_if(e => eq(e, x), l)
}

///|
/// `(delete x l :count 1 :test #'equal)`
fn suprv1__delete1_equal(x : Value, l : Value) -> Value {
  suprv1__delete1_if(e => equal(e, x), l)
}

///|
fn suprv1__delete1_if(p : (Value) -> Bool, l : Value) -> Value {
  match l {
    Cons({ car, cdr }) =>
      if p(car) {
        cdr
      } else {
        let mut prev = l
        let mut cur = cdr
        while cur is Cons({ car: c, cdr: rest }) {
          if p(c) {
            rplacd(prev, rest) |> ignore
            return l
          }
          prev = cur
          cur = rest
        }
        l
      }
    _ => l
  }
}

///|
/// The RAT-ERROR-TO-MERROR macro: a throw to RAT-ERR becomes an merror.
fn suprv1__rat_error_to_merror(f : () -> Value raise) -> Value raise {
  f() catch {
    LispError::Throw(tag, args) if eq(tag, q_rat_err) =>
      merror(car(args), cdr(args))
    e => raise e
  }
}

///|
/// Is this error a non-local control transfer rather than an error?
fn suprv1__control_transfer(e : Error) -> Bool {
  match e {
    LispError::Throw(_, _) => true
    LispError::ReturnFrom(_, _) => true
    LispError::Go(_) => true
    _ => false
  }
}

///|
/// Message text of a Lisp error, as (PRINC condition) shows it.
fn suprv1__error_text(e : Error) -> String {
  prompt_util__error_message(e)
}

///|
/// The ERRCATCH macro (errset.lisp): evaluate F while catching Maxima and
/// Lisp errors; returns (value) on success and NIL on error.
fn suprv1__errcatch(f : () -> Value raise) -> Value raise {
  let ec = cons(symval(q_bindlist), symval(q_loclist))
  let block = gensym(prefix="errcatch")
  with_specials([(q_errcatch, ec), (q_ear_mdebug, Nil)], () => {
    let body = () => {
      // WITH-ERRCATCH-TAG-$ERRORS
      let caught = catch_tag(q_macsyma_quit, () => catch_tag(q_errorsw, () => {
        let v = suprv1__rat_error_to_merror(f)
        raise LispError::ReturnFrom(block, v)
      }))
      ignore(caught)
      with_special(q_ear_merror_signals__dolerror_p, t, () => merr(
        "An error was caught by errcatch.",
        [],
      ))
    }
    let r = body() catch {
      LispError::ReturnFrom(tag, v) if physical_equal_value(tag, block) =>
        v
      e if is_maxima_error(e) => {
        errlfun1(ec) |> ignore
        return Nil
      }
      e if suprv1__control_transfer(e) => raise e
      e => {
        set(
          q_d_error,
          list([list2(q_mlist, q_simp), Str(suprv1__error_text(e))]),
        )
        |> ignore
        if symval(q_d_errormsg).truthy() {
          d_errormsg() |> ignore
        }
        errlfun1(ec) |> ignore
        return Nil
      }
    }
    list1(r)
  })
}

///|
/// Absolute name of a file (CL TRUENAME of a file we just wrote or read).
fn suprv1__truename(path : String) -> String {
  if path.has_prefix("/") {
    path
  } else {
    match getenv("PWD") {
      Some(d) => if d.has_suffix("/") { d + path } else { d + "/" + path }
      None => path
    }
  }
}

///|
/// LOAD of a Lisp source file: a ported share file runs its MoonBit port,
/// anything else is read and evaluated by the Lisp evaluator.
fn suprv1__load_lisp_file(path : String) -> Value raise {
  if share_try_load(path) {
    return t
  }
  lisp_load_file(path)
  t
}

///|
/// WITH-TOP-LEVEL-ENVIRONMENT: make sure that clearsign is called after the
/// evaluation.
fn suprv1__with_top_level_environment(f : () -> Value raise) -> Value raise {
  let r = with_specials([(q_ear_refchkl, Nil), (q_ear_checkfactors, Nil)], () => {
    if symval(q_d_ratvarswitch).truthy() {
      set(q_varlist, cdr(symval(q_d_ratvars))) |> ignore
    }
    f()
  }) catch {
    e => {
      // Clear the facts from asksign and friends.
      clearsign() |> ignore
      raise e
    }
  }
  clearsign() |> ignore
  r
}

///|
/// The macro WITH-TOP-LEVEL-ENVIRONMENT called as a function: BODY is a list
/// of Maxima forms (or a function value) evaluated in that environment.
fn with_top_level_environment(body : Value) -> Value raise {
  suprv1__with_top_level_environment(() => match body {
    Func(_) => funcall(body, [])
    _ => {
      let mut v : Value = Nil
      for f in body.iter() {
        v = meval(f)
      }
      v
    }
  })
}

///|
/// The MCATCH macro called as a function: FORM is a Maxima form (or a
/// function value).
fn mcatch(form : Value) -> Value raise {
  suprv1__mcatch(() => match form {
    Func(_) => funcall(form, [])
    _ => meval(form)
  })
}

///|
fn suprv1__mcatch(f : () -> Value raise) -> Value raise {
  let mc = cons(symval(q_bindlist), symval(q_loclist))
  with_special(q_mcatch, mc, () => {
    let r = catch_tag(q_mcatch, () => suprv1__rat_error_to_merror(f)) catch {
      e => {
        errlfun1(mc) |> ignore
        raise e
      }
    }
    errlfun1(mc) |> ignore
    r
  })
}

///|
fn meval_star(expr : Value) -> Value raise {
  suprv1__with_top_level_environment(() => meval(expr))
}

///|
fn makelabel10(x : Value) -> Value raise {
  // x should be a symbol (one of $inchar, $outchar, $linechar)
  with_specials([(q_ear_print_radix, Nil), (q_ear_print_base, Fix(10L))], () => d_concat(
    list([x, symval(q_d_linenum)]),
  ))
}

///|
fn makelabel(x : Value) -> Value raise {
  let label = makelabel10(x)
  set(q_ear_linelabel, label) |> ignore
  if !symval(q_d_nolabels).truthy() {
    let labels = symval(q_d_labels)
    let cond = if cdr(labels) is Nil {
      true
    } else if member_equal(label, cddr(labels)).truthy() {
      set(q_d_labels, suprv1__delete1(label, labels)) |> ignore
      true
    } else {
      !eq(label, cadr(symval(q_d_labels)))
    }
    if cond {
      let labels = symval(q_d_labels)
      set(q_d_labels, cons(car(labels), cons(label, cdr(labels)))) |> ignore
    }
  }
  label
}

///|
fn printlabel() -> Value raise {
  let s = princ_to_string(symval(q_ear_linelabel))
  mtell_open(Str("(~A) "), list1(Str(s.substring(start=1))))
}

///|
fn mexploden(x : Value) -> Value raise {
  with_specials([(q_ear_print_radix, Nil), (q_ear_print_base, Fix(10L))], () => exploden(
    x,
  ))
}

///|
fn addlabel(label : Value) -> Value raise {
  let labels = symval(q_d_labels)
  set(
    q_d_labels,
    cons(car(labels), cons(label, suprv1__delete1(label, cdr(labels)))),
  )
}

///|
fn tyi_star() -> Value raise {
  while true {
    let n = read_char(stream=symval(standard_input), eof_value=Nil)
    match n {
      Char(c) =>
        if c == '\n' || (c.to_int() > 31 && c.to_int() != 127) {
          return n
        } else if c.to_int() == 12 {
          suprv1__fmt(t, "~|", []) |> ignore
          throw_tag(q_retry, Nil) |> ignore
        }
      _ => return Char('\n')
    }
  }
  Nil
}

///|
fn continuep() -> Value raise {
  while true {
    let r = catch_tag(q_retry, () => {
      fresh_line() |> ignore
      princ(break_prompt()) |> ignore
      finish_output()
      raise LispError::ReturnFrom(q_continuep, lbool(tyi_star() is Char('\n')))
    }) catch {
      LispError::ReturnFrom(tag, v) if eq(tag, q_continuep) => return v
      e => raise e
    }
    ignore(r)
  }
  Nil
}

///|
/// CHECKLABEL returns T iff label is not in use
fn checklabel(x : Value) -> Value raise {
  lbool(
    !(
      symval(q_d_nolabels).truthy() ||
      num_eq(symval(q_d_linenum), Fix(0L)) ||
      boundp(makelabel10(x))
    ),
  )
}

///|
fn gctimep(timep : Value, tim : Value) -> Value raise {
  if eq(timep, q_d_all) && !zerop(tim) {
    princ(Str("Total time = ")) |> ignore
    t
  } else {
    princ(Str("Time = ")) |> ignore
    Nil
  }
}

///|
/// The dynamic loader.
fn load_function(func : Value, mexprp : Value) -> Value raise {
  ignore(mexprp)
  let file = get(func, q_autoload)
  if file.truthy() {
    funcall(symval(q_autoload), [cons(func, file)])
  } else {
    Nil
  }
}

///|
fn d_loadfile(form : Value) -> Value raise {
  loadfile(
    Str(princ_to_string(meval(cadr(form)))),
    Nil,
    lbool(!memq(symval(q_d_loadprint), list([Nil, q_d_autoload])).truthy()),
  )
}

///|
fn dollarify(l : Value) -> Value raise {
  with_special(q_errset, t, () => cons(
    list2(q_mlist, q_simp),
    mapcar(
      x => {
        if numberp(x) {
          return x
        }
        let y = match errset(() => readlist(mexploden(x))) {
          Some(v) => v
          None => Nil
        }
        if numberp(y) {
          y
        } else {
          makealias(x)
        }
      },
      l,
    ),
  ))
}

///|
fn mfboundp(func : Value) -> Value raise {
  let v = mgetl(func, list([q_mexpr, q_mmacro]))
  if v.truthy() {
    v
  } else {
    getl(func, list([q_translated_mmacro, q_mfexpr_star, q_mfexpr_stars]))
  }
}

///|
fn loadfile(file : Value, findp : Value, printp : Value) -> Value raise {
  let mut printp = printp
  if findp.truthy() &&
    memq(symval(q_d_loadprint), list([Nil, q_d_loadfile])).truthy() {
    printp = Nil
  }
  // Should really get the truename of FILE.
  if printp.truthy() {
    suprv1__fmt(t, "loadfile: loading ~A.~%", [file]) |> ignore
  }
  let path = lstring(file)
  let tem = with_specials(
    [(q_d_load_pathname, Str(path)), (q_ear_read_base, Fix(10L)), (q_ear_print_base, Fix(10L))],
    () => errset(() => suprv1__load_lisp_file(path)),
  )
  if tem is None {
    merr("loadfile: failed to load ~A", [Str(path)]) |> ignore
  }
  Str(path)
}

///|
fn d_kill(form : Value) -> Value raise {
  // get assume db into consistent state
  clear() |> ignore
  for x in cdr(form).iter() {
    kill1(x) |> ignore
  }
  db_gc() |> ignore
  q_d_done
}

///|
fn kill1_atom(x : Value) -> Value raise {
  let z = {
    let a = if member_equal(x, cdr(symval(q_d_aliases))).truthy() {
      get(x, q_noun)
    } else {
      Nil
    }
    if a.truthy() {
      a
    } else {
      get(x, q_verb)
    }
  }
  let allbutl = symval(q_allbutl)
  if !(allbutl is Nil || !member_equal(z, allbutl).truthy()) {
    return Nil
  }
  remvalue(x, q_d_kill) |> ignore
  mget(x, q_array) |> ignore
  remcompary(x) |> ignore
  if member_equal(x, cdr(symval(q_d_contexts))).truthy() {
    d_killcontext(list1(x)) |> ignore
  }
  if mget(x, q_d_rule).truthy() {
    free_rule_symbols(get(x, q_rule_symbols)) |> ignore
    remprop(x, q_rule_symbols) |> ignore
    let y = ruleof(x)
    if y.truthy() {
      d_remrule(y, x) |> ignore
    } else if !member_equal(x, symval(q_ear_builtin__dolrules)).truthy() {
      fmakunbound(x) |> ignore
      set(q_d_rules, suprv1__delete1(x, symval(q_d_rules))) |> ignore
    }
  }
  if get(x, q_operators).truthy() && rulechk(x).truthy() {
    d_remrule(x, q_d_all) |> ignore
  }
  if mget(x, q_trace).truthy() {
    macsyma_untrace(x) |> ignore
  }
  if get(x, q_translated).truthy() {
    if !member_equal(x, symval(q_ear_builtin_symbols)).truthy() {
      remove_transl_fun_props(x) |> ignore
      remove_transl_array_fun_props(x) |> ignore
    }
  }
  if !get(x, q_sysconst).truthy() {
    remprop(x, q_lineinfo) |> ignore
    remprop(x, q_mprops) |> ignore
  }
  for u in [q_bindtest, q_nonarray, q_evfun, q_evflag, q_opers, q_mode] {
    remprop(x, u) |> ignore
  }
  for u in symval(q_opers).iter() {
    if remprop(x, u).truthy() {
      let xopval = get(x, q_operators)
      if eq(xopval, q_simpargs1) || xopval is Nil {
        remprop(x, q_operators) |> ignore
      }
    }
  }
  let opx = {
    let o = get(x, q_op)
    if o.truthy() {
      o
    } else {
      x
    }
  }
  if member_equal(opx, cdr(symval(q_d_props))).truthy() {
    remprop(x, q_sp2) |> ignore
    killframe(x) |> ignore
    i__dolremove(list([x, symval(q_d_features)])) |> ignore
  }
  let y = get(x, q_op)
  if y.truthy() &&
    !member_equal(y, symval(q_ear_mopl)).truthy() &&
    member_equal(y, cdr(symval(q_d_props))).truthy() {
    kill_operator(x) |> ignore
  }
  remalias(x, remp=Nil) |> ignore
  set(q_d_arrays, suprv1__delete1(x, symval(q_d_arrays))) |> ignore
  rempropchk(x) |> ignore
  set(
    q_ear_autoloaded_files,
    suprv1__delete1_equal(
      assq(x, symval(q_ear_autoloaded_files)),
      symval(q_ear_autoloaded_files),
    ),
  )
  |> ignore
  set(
    q_d_functions,
    suprv1__delete1_equal(
      assoc_equal(list1(x), symval(q_d_functions)),
      symval(q_d_functions),
    ),
  )
  |> ignore
  set(
    q_d_macros,
    suprv1__delete1_equal(
      assoc_equal(list1(x), symval(q_d_macros)),
      symval(q_d_macros),
    ),
  )
  |> ignore
  let y = assoc_equal(list1(x), symval(q_d_gradefs))
  if y.truthy() {
    remprop(x, q_grad) |> ignore
    set(q_d_gradefs, suprv1__delete1_equal(y, symval(q_d_gradefs))) |> ignore
  }
  set(
    q_d_dependencies,
    suprv1__delete1_equal(
      assoc_equal(list1(x), symval(q_d_dependencies)),
      symval(q_d_dependencies),
    ),
  )
  |> ignore
  // ASSOC-IF applies its predicate to the CAR of each element.
  let y = find_if(e => equal(x, caar(e)), cdr(symval(q_d_structures)))
  if y.truthy() {
    remprop(x, q_dimension) |> ignore
    remprop(x, q_defstruct_template) |> ignore
    remprop(x, q_defstruct_default) |> ignore
    remprop(x, q_translate) |> ignore
    remprop(x, q_operators) |> ignore
    set(q_d_structures, suprv1__delete1_equal(y, symval(q_d_structures)))
    |> ignore
  }
  remprop(x, q_noun) |> ignore
  remprop(x, q_verb) |> ignore
  if member_equal(x, symval(q_ear_builtin_symbols)).truthy() {
    let props = gethash(x, symval(q_ear_builtin_symbol_props))
    if props.truthy() {
      set_symbol_plist(x, copy_tree(props)) |> ignore
    }
  }
  if memq(x, symval(q_ear_builtin_numeric_constants)).truthy() {
    // reset db value for $%pi, $%e, etc
    initialize_numeric_constant(x) |> ignore
  }
  if memq(x, list([q_d_zeroa, q_d_zerob])).truthy() {
    // restore db assumptions for $zeroa and $zerob
    initialize_zeroab(x) |> ignore
  }
  if z.truthy() {
    kill1(z)
  } else {
    Nil
  }
}

///|
fn kill1(x : Value) -> Value raise {
  if stringp(x) && !getopr0(x).truthy() {
    return Nil
  }
  let mut x = x
  let mut z : Value = Nil
  let allbutl = symval(q_allbutl)
  if allbutl.truthy() && member_equal(x, allbutl).truthy() {
    return Nil
  }
  x = getopr(x)
  if eq(x, q_d_labels) {
    for u in cdr(symval(q_d_labels)).iter() {
      let allbutl = symval(q_allbutl)
      if allbutl.truthy() && member_equal(u, allbutl).truthy() {
        z = nconc(z, list1(u))
      } else {
        makunbound(u) |> ignore
        remprop(u, q_time) |> ignore
        remprop(u, q_nodisp) |> ignore
      }
    }
    set(q_d_labels, cons(list2(q_mlist, q_simp), z)) |> ignore
    set(q_d_linenum, Fix(0L)) |> ignore
  } else if memq(
      x,
      list([
        q_d_values, q_d_arrays, q_d_aliases, q_d_rules, q_d_props, q_d_let_rule_packages,
      ]),
    ).truthy() {
    for y in cdr(symval(x)).iter() {
      kill1(y) |> ignore
    }
  } else if memq(
      x,
      list([q_d_functions, q_d_macros, q_d_gradefs, q_d_dependencies, q_d_structures]),
    ).truthy() {
    for y in cdr(symval(x)).iter() {
      kill1(caar(y)) |> ignore
    }
  } else if eq(x, q_d_myoptions) {
    ()
  } else if eq(x, q_d_tellrats) {
    set(q_tellratlist, Nil) |> ignore
  } else if eq(x, q_d_ratvars) {
    set(q_d_ratvars, list1(list2(q_mlist, q_simp))) |> ignore
    set(q_varlist, Nil) |> ignore
  } else if eq(x, q_d_ratweights) {
    set(q_n_starratweights, Nil) |> ignore
    set(q_d_ratweights, list1(list2(q_mlist, q_simp))) |> ignore
  } else if eq(x, q_d_features) {
    if !equal(cdr(symval(q_d_features)), symval(q_featurel)) {
      set(
        q_d_features,
        cons(list2(q_mlist, q_simp), copy_list(symval(q_featurel))),
      )
      |> ignore
    }
  } else if eq(x, t) || eq(x, q_d_all) {
    for y in cdr(symval(q_d_infolists)).iter() {
      kill1(y) |> ignore
    }
    set(q_d_ratvars, list1(list2(q_mlist, q_simp))) |> ignore
    set(q_varlist, Nil) |> ignore
    set(q_genvar, Nil) |> ignore
    set(q_ear_checkfactors, Nil) |> ignore
    set(q_greatorder, Nil) |> ignore
    set(q_lessorder, Nil) |> ignore
    set(q_d_gensumnum, Fix(0L)) |> ignore
    set(q_n_starratweights, Nil) |> ignore
    set(q_d_ratweights, list1(list2(q_mlist, q_simp))) |> ignore
    set(q_tellratlist, Nil) |> ignore
    set(q_d_dontfactor, list1(list1(q_mlist))) |> ignore
    set(q_d_setcheck, Nil) |> ignore
    killallcontexts() |> ignore
  } else {
    return suprv1__kill1_rest(x)
  }
  Nil
}

///|
/// The remaining clauses of KILL1 (labels lists, label numbers, atoms,
/// [m, n] label ranges, array elements, @-records and allbut).
fn suprv1__kill1_rest(x : Value) -> Value raise {
  let mut x = x
  let z = assq(
    x,
    list([
      cons(q_d_inlabels, q_d_inchar),
      cons(q_d_outlabels, q_d_outchar),
      cons(q_d_linelabels, q_d_linechar),
    ]),
  )
  if z.truthy() {
    for y in getlabels_star(symval(cdr(z)), Nil).iter() {
      remvalue(y, q_d_kill) |> ignore
    }
    return Nil
  }
  if fixnump(x) && num_ge(x, Fix(0L)) {
    remlabels(x) |> ignore
    return Nil
  }
  if atom(x) {
    kill1_atom(x) |> ignore
    return Nil
  }
  if eq(caar(x), q_mlist) && fixnump(cadr(x)) {
    let ok = if cddr(x) is Nil {
      x = append(x, list1(cadr(x)))
      true
    } else {
      fixnump(caddr(x)) && !num_gt(cadr(x), caddr(x))
    }
    if ok {
      let x1 = x
      with_special(q_d_linenum, caddr(x1), () => remlabels(
        num_sub(caddr(x1), cadr(x1)),
      ))
      |> ignore
      return Nil
    }
  }
  let z = mgetl(caar(x), list([q_hashar, q_array]))
  if z.truthy() {
    remarrelem(z, x) |> ignore
    return Nil
  }
  if d_subvarp(x).truthy() &&
    boundp(caar(x)) &&
    hash_table_p(symval(caar(x))) {
    let z = symval(caar(x))
    // Evaluate the subscripts (as is done in ARRSTORE)
    let indices = mevalargs(cdr(x))
    if gethash(q_dim1, z).truthy() {
      remhash(car(indices), z) |> ignore
    } else {
      remhash(indices, z) |> ignore
    }
  } else if eq(caar(x), q_d_op_at) {
    mrecord_kill(x) |> ignore
  } else if eq(caar(x), q_d_allbut) && every(u => symbolp(u), cdr(x)) {
    with_special(q_allbutl, cdr(x), () => kill1(t)) |> ignore
  } else {
    improper_arg_err(x, q_d_kill) |> ignore
  }
  Nil
}

///|
fn remlabels(n : Value) -> Value raise {
  let mut n = to_int(n)
  let l = [
    exploden(symval(q_d_inchar)),
    exploden(symval(q_d_outchar)),
    exploden(symval(q_d_linechar)),
  ]
  while true {
    let x = mexploden(symval(q_d_linenum))
    for p in l {
      remvalue(implode(append(p, x)), q_d_kill) |> ignore
    }
    n = n - 1
    if n < 0 || num_eq(symval(q_d_linenum), Fix(0L)) {
      return Nil
    }
    set(q_d_linenum, num_sub(symval(q_d_linenum), Fix(1L))) |> ignore
  }
  Nil
}

///|
fn remvalue(x : Value, fn_ : Value) -> Value raise {
  if !symbolp(x) {
    return improper_arg_err(x, fn_)
  }
  if !boundp(x) {
    return Nil
  }
  let restore = () => if member_equal(x, symval(q_ear_builtin_symbols_with_values)).truthy() {
    set(x, gethash(x, symval(q_ear_builtin_symbol_values))) |> ignore
  }
  let y = member_equal(x, cdr(symval(q_d_values)))
  if y.truthy() || member_equal(x, cdr(symval(q_d_labels))).truthy() {
    if y.truthy() {
      set(q_d_values, suprv1__delete1(x, symval(q_d_values))) |> ignore
    } else {
      set(q_d_labels, suprv1__delete1(x, symval(q_d_labels))) |> ignore
      remprop(x, q_time) |> ignore
      remprop(x, q_nodisp) |> ignore
    }
    makunbound(x) |> ignore
    restore()
    t
  } else if get(x, q_reset_on_kill).truthy() {
    makunbound(x) |> ignore
    restore()
    t
  } else if symval(q_transp).truthy() {
    set(x, x) |> ignore
    t
  } else if eq(x, q_d_default_let_rule_package) {
    t
  } else if eq(symval(x), x) {
    // X is bound to itself but X is not on values list.  Translation code
    // does that; silently let it stand.
    t
  } else {
    mtell(
      list([
        Str(
          "remvalue: ~M doesn't appear to be a known variable; just unbind it anyway.~%",
        ),
        x,
      ]),
    )
    |> ignore
    makunbound(x) |> ignore
    t
  }
}

///|
fn ruleof(rule : Value) -> Value raise {
  let r = mget(rule, q_ruleof)
  if r.truthy() {
    return r
  }
  let pattern = cadr(mget(rule, q_d_rule))
  let op : Value = if atom(pattern) { Nil } else { caar(pattern) }
  let l = get(op, q_rules)
  if l.truthy() && member_equal(rule, l).truthy() {
    op
  } else {
    Nil
  }
}

///|
fn d_debugmode(x : Value) -> Value raise {
  debugmode1(Nil, x) |> ignore
  set(q_d_debugmode, x)
}

///|
fn debugmode1(assign_var : Value, y : Value) -> Value raise {
  // The user manual says $debugmode has one of three values: false (NIL),
  // true (T), or lisp ($lisp).  Enforce that.
  if !(y is Nil || eq(y, t) || eq(y, q_d_lisp)) {
    mseterr(assign_var, y, reason=Str("Must be one of false, true, or lisp"))
    |> ignore
  }
  set(q_ear_mdebug, y)
}

///|
fn errlfun1(mpdls : Value) -> Value raise {
  let mut l = symval(q_bindlist)
  let mut l1 : Value = Nil
  while !physical_equal_value(l, car(mpdls)) && l is Cons(_) {
    l1 = cons(car(l), l1)
    l = cdr(l)
  }
  munbind(l1) |> ignore
  while !physical_equal_value(symval(q_loclist), cdr(mpdls)) &&
    symval(q_loclist) is Cons(_) {
    munlocal() |> ignore
  }
  Nil
}

///|
fn makealias(x : Value) -> Value raise {
  implode(cons(Char('$'), exploden(x)))
}

///|
/// Makes sure that F was called with exactly one argument and returns that
/// argument.
fn fexprcheck(form : Value) -> Value raise {
  if cdr(form) is Nil || cddr(form).truthy() {
    merr("~:M: expected just one argument; found: ~M", [caar(form), form])
  } else {
    cadr(form)
  }
}

///|
fn nonsymchk(x : Value, fn_ : Value) -> Value raise {
  if !symbolp(x) {
    merr("~:M: argument must be a symbol; found: ~M", [fn_, x]) |> ignore
  }
  Nil
}

///|
fn d_print(args : Value) -> Value raise {
  if args is Nil {
    return list1(list2(q_mlist, q_simp))
  }
  // Don't print out strings with quotation marks!
  with_special(q_d_stringdisp, Nil, () => {
    let mut l = args
    while l is Cons(_) {
      rplacd(l, cons(Str(" "), cdr(l))) |> ignore
      l = cddr(l)
    }
    displa(cons(list1(q_mtext), args)) |> ignore
    cadr(reverse(args))
  })
}

///|
fn d_playback(x : Value) -> Value raise {
  let mut x = cdr(x)
  let mut l : Value = Nil
  let mut l1 : Value = Nil
  let mut numbp : Value = Nil
  let mut slowp = false
  let mut nostringp = false
  let mut inputp = false
  let mut largp = false
  // Only the 1st alphabetic char. of $INCHAR is tested
  let inchar = getlabcharn(symval(q_d_inchar))
  let mut timep = symval(q_d_showtime)
  let mut grindp = symval(q_d_grind)
  while x is Cons(_) {
    let a = car(x)
    if fixnump(a) {
      numbp = a
    } else if eq(a, q_d_all) {
      ()
    } else if eq(a, q_d_slow) {
      slowp = true
    } else if eq(a, q_d_nostring) {
      nostringp = true
    } else if eq(a, q_d_grind) {
      grindp = t
    } else if eq(a, q_d_input) {
      inputp = true
    } else if eq(a, q_d_showtime) || eq(a, q_d_time) {
      timep = if timep.truthy() { timep } else { t }
    } else if eq(a, q_d_gctime) || eq(a, q_d_totaltime) {
      timep = q_d_all
    } else {
      let l2 = listargp(a)
      if l2.truthy() {
        l1 = nconc(l1, getlabels(car(l2), cdr(l2), Nil))
        largp = true
      } else {
        improper_arg_err(a, q_d_playback) |> ignore
      }
    }
    x = cdr(x)
  }
  let mut skip_to_loop = false
  if largp && numbp is Nil {
    skip_to_loop = true
  } else {
    l = cdr(symval(q_d_labels))
    if l.truthy() && !symval(q_d_nolabels).truthy() {
      l = cdr(l)
    }
  }
  if !skip_to_loop {
    if numbp is Nil || length(l) < to_int(numbp) {
      l1 = reverse(l)
    } else {
      let mut i = to_int(numbp)
      let mut l2 : Value = Nil
      while i != 0 {
        l2 = cons(car(l), l2)
        l = cdr(l)
        i -= 1
      }
      l1 = nconc(l1, l2)
    }
  }
  // loop
  while l1 is Cons(_) {
    let lab = car(l1)
    let incharp = getlabcharn(lab) is Char(c) && inchar is Char(ic) && c == ic
    let mut go_a = false
    with_special(q_errset, t, () => errset(() => {
      if !nostringp && incharp {
        with_special(q_ear_linelabel, lab, () => {
          mterpri() |> ignore
          printlabel()
        })
        |> ignore
        if grindp.truthy() {
          mgrind(meval1(lab).0, Nil) |> ignore
        } else {
          for c in mstring(meval1(lab).0).iter() {
            match c {
              Char(ch) => write_char(ch)
              _ => princ(c) |> ignore
            }
          }
        }
        if get(lab, q_nodisp).truthy() {
          princ(Str("$")) |> ignore
        } else {
          princ(Str(";")) |> ignore
        }
        mterpri() |> ignore
      } else if incharp ||
        {
          if timep.truthy() {
            let tm = get(lab, q_time)
            if tm.truthy() {
              let xx = gctimep(timep, cdr(tm))
              mtell(list([Str("~A seconds"), car(tm)])) |> ignore
              if xx.truthy() {
                mtell(list([Str("  GC time = ~A seconds"), cdr(tm)])) |> ignore
              }
              mterpri() |> ignore
            }
          }
          !(inputp || get(lab, q_nodisp).truthy())
        } {
        mterpri() |> ignore
        displa(list([list1(q_mlabel), lab, meval1(lab).0])) |> ignore
      } else {
        go_a = true
      }
      Nil
    }))
    |> ignore
    if !go_a && slowp && cdr(l1).truthy() && !continuep().truthy() {
      return q_d_terminated
    }
    l1 = cdr(l1)
  }
  q_d_done
}

///|
fn listargp(x : Value) -> Value raise {
  if d_listp(x).truthy() && fixnump(cadr(x)) {
    let high = if cddr(x) is Nil {
      cadr(x)
    } else if fixnump(caddr(x)) && !num_gt(cadr(x), caddr(x)) {
      caddr(x)
    } else {
      return Nil
    }
    cons(cadr(x), high)
  } else {
    Nil
  }
}

///|
fn d_alias(form : Value) -> Value raise {
  let mut form = cdr(form)
  if length(form) % 2 == 1 {
    merr("alias: expected an even number of arguments.", []) |> ignore
  }
  let mut l : Value = Nil
  while form is Cons(_) {
    let a = car(form)
    let b = cadr(form)
    form = cddr(form)
    l = cons(alias(a, b), l)
  }
  cons(list2(q_mlist, q_simp), nreverse(l))
}

///|
fn alias(x : Value, y : Value) -> Value raise {
  nonsymchk(x, q_d_alias) |> ignore
  nonsymchk(y, q_d_alias) |> ignore
  if eq(x, y) {
    // x is already the alias of y
    y
  } else if get(x, q_reversealias).truthy() {
    merr("alias: ~M already has an alias.", [x])
  } else {
    putprop(x, y, q_alias) |> ignore
    putprop(y, x, q_reversealias) |> ignore
    add2lnc(y, symval(q_d_aliases)) |> ignore
    y
  }
}

///|
fn remalias(x : Value, remp? : Value = Nil) -> Value raise {
  let y = if remp.truthy() || member_equal(x, cdr(symval(q_d_aliases))).truthy() {
    get(x, q_reversealias)
  } else {
    Nil
  }
  if y.truthy() && eq(x, q_p_derivative) {
    remprop(x, q_reversealias) |> ignore
    set(q_d_aliases, suprv1__delete1(x, symval(q_d_aliases))) |> ignore
    remprop(q_d_diff, q_alias) |> ignore
    q_d_diff
  } else if y.truthy() {
    remprop(x, q_reversealias) |> ignore
    remprop(x, q_noun) |> ignore
    set(q_d_aliases, suprv1__delete1(x, symval(q_d_aliases))) |> ignore
    remprop(y, q_alias) |> ignore
    remprop(y, q_verb) |> ignore
    y
  } else {
    Nil
  }
}

///|
fn fullstrip(x : Value) -> Value raise {
  mapcar(e => fullstrip1(e), x)
}

///|
fn fullstrip1(x : Value) -> Value raise {
  if numberp(x) {
    return x
  }
  let y = get(x, q_reversealias)
  if y.truthy() {
    let s = stripdollar(y)
    if s.truthy() {
      return s
    }
  }
  stripdollar(x)
}

///|
fn string_star(x : Value) -> Value raise {
  if numberp(x) {
    let e = exploden(x)
    if e.truthy() {
      return e
    }
  }
  string_star1(x)
}

///|
fn string_star1(x : Value) -> Value raise {
  with_specials([(q_d_stringdisp, Nil), (q_d_lispdisp, Nil)], () => makestring(
    x,
  ))
}

///|
fn d_nounify(x : Value) -> Value raise {
  if !(symbolp(x) || stringp(x)) {
    merr("nounify: argument must be a symbol or a string; found: ~M", [x])
    |> ignore
  }
  let x = amperchk(x)
  let v = get(x, q_verb)
  if v.truthy() {
    return v
  }
  if get(x, q_noun).truthy() {
    return x
  }
  let y = explodec(x)
  let u = eq(car(y), q_d_)
  if u || !eq(car(y), q_p_) {
    let y = implode(cons(q_p_, if u { cdr(y) } else { y }))
    putprop(y, x, q_noun) |> ignore
    putprop(x, y, q_verb) |> ignore
    y
  } else {
    x
  }
}

///|
fn d_verbify(x : Value) -> Value raise {
  if !(symbolp(x) || stringp(x)) {
    merr("verbify: argument must be a symbol or a string; found: ~M", [x])
    |> ignore
  }
  let x = amperchk(x)
  let n = get(x, q_noun)
  if n.truthy() {
    return n
  }
  if eq(x, q_empty) {
    return x
  }
  if symbol_name(x).has_prefix("%") {
    d_nounify(implode(cons(Char('$'), cdr(exploden(x))))) |> ignore
    let n = get(x, q_noun)
    if n.truthy() {
      return n
    }
  }
  x
}

///|
fn d_string(form : Value) -> Value raise {
  with_special(q_d_lispdisp, t, () => {
    let form = strmeval(fexprcheck(form))
    let form = if symval(q_d_grind).truthy() {
      strgrind(form)
    } else {
      mstring(form)
    }
    Str(char_list_to_string(form))
  })
}

///|
fn makstring(x : Value) -> Value raise {
  let x = mstring(x)
  let mut l = x
  while l is Cons(_) {
    rplaca(l, ascii(car(l))) |> ignore
    l = cdr(l)
  }
  x
}

///|
fn strmeval(x : Value) -> Value raise {
  if atom(x) {
    meval1(x).0
  } else if memq(caar(x), list([q_msetq, q_mdefine, q_mdefmacro])).truthy() {
    x
  } else {
    meval(x)
  }
}

///|
fn d_stringout(x : Value) -> Value raise {
  let x = cdr(x)
  let file = princ_to_string(meval(car(x)))
  let append_ = eq(symval(q_d_file_output_append), q_d_true) ||
    eq(symval(q_d_file_output_append), t)
  let x = cdr(x)
  let savefile = make_string_output_stream()
  let r = with_special(q_savefile, savefile, () => errset(() => {
    let mut l = x
    while true {
      if l is Nil {
        break
      }
      let a = car(l)
      if eq(a, q_d_all) || eq(a, q_d_input) {
        l = nconc(getlabels_star(symval(q_d_inchar), t), cdr(l))
      } else if eq(a, q_d_values) {
        l = nconc(
          mapcan(
            v => if boundp(v) {
              list1(list([list1(q_msetq), v, symval(v)]))
            } else {
              Nil
            },
            cdr(symval(q_d_values)),
          ),
          cdr(l),
        )
      } else if eq(a, q_d_functions) {
        l = nconc_n([
          mapcar(f => consfundef(caar(f), Nil, Nil), cdr(symval(q_d_functions))),
          mapcan(
            f => if mget(f, q_aexpr).truthy() {
              list1(consfundef(f, t, Nil))
            } else {
              Nil
            },
            cdr(symval(q_d_arrays)),
          ),
          mapcar(f => consfundef(caar(f), Nil, Nil), cdr(symval(q_d_macros))),
          cdr(l),
        ])
      } else {
        let l1 = listargp(a)
        if l1.truthy() {
          l = nconc(getlabels(car(l1), cdr(l1), t), cdr(l))
        }
      }
      if l is Nil {
        break
      }
      terpri(stream=savefile)
      if symval(q_d_grind).truthy() {
        mgrind(strmeval(car(l)), savefile) |> ignore
      } else {
        write_string(char_list_to_string(mstring(strmeval(car(l)))), stream=savefile)
      }
      if (symbolp(car(l)) && get(car(l), q_nodisp).truthy()) ||
        !symval(q_d_strdisp).truthy() {
        write_char('$', stream=savefile)
      } else {
        write_char(';', stream=savefile)
      }
      l = cdr(l)
    }
    Nil
  }))
  let maxima_error = r is None
  terpri(stream=savefile)
  let text = get_output_stream_string(savefile)
  let old = if append_ && probe_file(file) { read_file(file) } else { "" }
  write_file(file, old + text)
  if maxima_error {
    merr("stringout: unspecified error.", []) |> ignore
  }
  Str(suprv1__truename(file))
}

///|
fn d_labels(label_prefix : Value) -> Value raise {
  nonsymchk(label_prefix, q_d_labels) |> ignore
  cons(list2(q_mlist, q_simp), nreverse(getlabels_star(label_prefix, Nil)))
}

///|
fn d__pctth(x : Value) -> Value raise {
  let mut x = x
  if !fixnump(x) || zerop(x) {
    improper_arg_err(x, q_d__pctth) |> ignore
  }
  if num_gt(x, Fix(0L)) {
    x = num_neg(x)
  }
  let mut l : Value = Nil
  let mut outchar : Value = Nil
  if cdr(symval(q_d_labels)).truthy() {
    l = cddr(symval(q_d_labels))
    // Only the 1st alphabetic character of $OUTCHAR is tested.
    outchar = getlabcharn(symval(q_d_outchar))
  }
  while true {
    if l is Nil {
      merr("%th: no such previous output: ~M", [x]) |> ignore
    }
    if equal(getlabcharn(car(l)), outchar) {
      x = num_add(x, Fix(1L))
      if zerop(x) {
        return meval(car(l))
      }
    }
    l = cdr(l)
  }
  Nil
}

///|
/// FLAG = T for STRINGOUT, = NIL for PLAYBACK and SAVE.
fn getlabels(n1 : Value, n2 : Value, flag : Value) -> Value raise {
  let prefixes = if flag.truthy() {
    [exploden(symval(q_d_inchar))]
  } else {
    [
      exploden(symval(q_d_inchar)),
      exploden(symval(q_d_linechar)),
      exploden(symval(q_d_outchar)),
    ]
  }
  let mut l1 : Value = Nil
  let mut i = n1
  while !num_gt(i, n2) {
    let x = mexploden(i)
    for p in prefixes {
      let z = implode(append(p, x))
      if boundp(z) {
        l1 = cons(z, l1)
      }
    }
    i = num_add(i, Fix(1L))
  }
  nreverse(l1)
}

///|
/// FLAG = T only for STRINGOUT
fn getlabels_star(label_prefix : Value, flag : Value) -> Value raise {
  let prefix = symbol_name(label_prefix)
  let mut l = if flag.truthy() {
    cddr(symval(q_d_labels))
  } else {
    cdr(symval(q_d_labels))
  }
  let mut l1 : Value = Nil
  while l is Cons(_) {
    let name = symbol_name(car(l))
    if name.has_prefix(prefix) {
      l1 = cons(car(l), l1)
    }
    l = cdr(l)
  }
  l1
}

///|
fn getlabcharn(label : Value) -> Value raise {
  let name = symbol_name(label)
  let c = name[1].to_int().unsafe_to_char()
  if c == '%' {
    Char(name[2].to_int().unsafe_to_char())
  } else {
    Char(c)
  }
}

///|
fn d_errcatch(form : Value) -> Value raise {
  cons(list1(q_mlist), suprv1__errcatch(() => mevaln(cdr(form))))
}

///|
fn d_catch(form : Value) -> Value raise {
  suprv1__mcatch(() => mevaln(cdr(form)))
}

///|
fn d_throw(exp_ : Value) -> Value raise {
  if symval(q_mcatch) is Nil {
    merr("throw: not within 'catch'; expression: ~M", [exp_]) |> ignore
  }
  throw_tag(q_mcatch, exp_)
}

///|
fn d_time(l : Value) -> Value raise {
  let l = cdr(l)
  cons(
    list2(q_mlist, q_simp),
    mapcar(
      x => {
        if symbolp(x) {
          let tm = get(x, q_time)
          if tm.truthy() {
            return if num_eq(cdr(tm), Fix(0L)) {
              car(tm)
            } else {
              list([list2(q_mlist, q_simp), car(tm), cdr(tm)])
            }
          }
        }
        q_d_unknown
      },
      l,
    ),
  )
}

///|
fn timeorg(tim : Value) -> Value raise {
  if num_gt(symval(q_thistime), Fix(0L)) {
    set(
      q_thistime,
      num_add(symval(q_thistime), num_sub(macsys__run_time(), tim)),
    )
  } else {
    Nil
  }
}

///|
/// Quit Maxima with an optional exit code.
fn d_quit(exit_code? : Value = Fix(0L)) -> Value raise {
  princ(symval(q_ear_maxima_epilog)) |> ignore
  bye(exit_code~) |> ignore
  mtell(list([Str("quit: No known quit function for this Lisp.~%")]))
}

///|
fn mterpri(ostream? : Value) -> Value raise {
  let ostream = match ostream {
    Some(s) => s
    None => symval(standard_output)
  }
  terpri(stream=ostream)
  finish_output(stream=ostream)
  Nil
}

///|
fn d_status(form : Value) -> Value raise {
  let form = cdr(form)
  let keyword = car(form)
  let feature = cadr(form)
  if !symbolp(keyword) {
    merr("status: first argument must be a symbol; found: ~M", [keyword])
    |> ignore
  }
  if !(stringp(feature) || symbolp(feature)) {
    merr("status: second argument must be symbol or a string; found: ~M", [
      feature,
    ])
    |> ignore
  }
  if eq(keyword, q_d_feature) {
    if feature is Nil {
      dollarify(symval(q_ear_features))
    } else {
      let name = match feature {
        Str(s) => lstring(maybe_invert_string_case(Str(s)))
        _ => symbol_name(fullstrip1(feature))
      }
      if member_equal(kw(name), symval(q_ear_features)).truthy() {
        t
      } else {
        Nil
      }
    }
  } else {
    merr("status: unknown argument: ~M", [keyword])
  }
}

///|
/// `(defquote $sstatus (keyword item) ...)`: arguments are not evaluated.
fn suprv1__sstatus(keyword : Value, item : Value) -> Value raise {
  if equal(keyword, q_d_feature) {
    let k = d_mkey(item)
    if !member(k, symval(q_ear_features)).truthy() {
      set(q_ear_features, cons(k, symval(q_ear_features))) |> ignore
    }
    t
  } else if equal(keyword, q_d_nofeature) {
    set(q_ear_features, delete(d_mkey(item), symval(q_ear_features))) |> ignore
    t
  } else {
    merr("sstatus: unknown argument: ~M", [keyword])
  }
}

///|
fn d_at_difference(e : Value, x : Value, a : Value, b : Value) -> Value raise {
  m_(
    d_at(e, list([list1(q_mequal), x, b])),
    a2=d_at(e, list([list1(q_mequal), x, a])),
  )
}

///|
/// 2-d pretty printer display for antiderivative-like expressions
fn dimension__pctat_difference(form : Value, result : Value) -> Value raise {
  if length(cdr(form)) != 4 {
    return dimension_function(form, result)
  }
  let args = rest(form)
  let expr = first(args)
  let my_var = second(args)
  let lower_val = third(args)
  let upper_val = fourth(args)
  let lower_eqn = list([list1(q_mequal), my_var, lower_val])
  let upper_eqn = list([list1(q_mequal), my_var, upper_val])
  let vertical_bar_char = if display2d_unicode_enabled().truthy() {
    symval(q_at_char_unicode)
  } else {
    displa__first_char(symval(q_d_absboxchar))
  }
  let expr_result = dimension(expr, Nil, q_mparen, q_mparen, Nil, Fix(0L))
  let expr_w = displa__i(q_width)
  let expr_h = displa__i(q_height)
  let expr_d = displa__i(q_depth)
  let lower_result = dimension_infix(lower_eqn, Nil)
  let lower_w = displa__i(q_width)
  let lower_h = displa__i(q_height)
  let lower_d = displa__i(q_depth)
  let upper_result = dimension_infix(upper_eqn, Nil)
  let upper_w = displa__i(q_width)
  let upper_h = displa__i(q_height)
  let upper_d = displa__i(q_depth)
  let mx = displa__max
  let vertical_bar = list([
    q_d__vbar,
    int(1 + mx(expr_h, upper_d)),
    int(mx(1 + expr_d, lower_h)),
    vertical_bar_char,
  ])
  let result = append_n([
    list1(list([int(mx(lower_w, upper_w) - upper_w), Fix(0L)])),
    list([
      append(list([int(-lower_w), int(mx(expr_h, upper_d))]), upper_result),
      append_n([
        list([Fix(0L), int(-mx(1 + expr_d, lower_h))]),
        lower_result,
        list1(
          list([
            Fix(0L),
            int(if lower_w > upper_w { lower_w - upper_w } else { 0 }),
          ]),
        ),
      ]),
      vertical_bar,
      append(list([Fix(0L), Fix(0L)]), expr_result),
    ]),
    result,
  ])
  displa__set(q_height, mx(expr_h, upper_d) + upper_h)
  displa__set(q_width, 1 + expr_w + mx(lower_w, upper_w))
  displa__set(q_depth, mx(1 + expr_d, lower_h) + lower_d)
  // Edrx:
  displa__set(q_width, expr_w + 1 + mx(upper_w, lower_w))
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  result
}

///|
fn init_suprv1() -> Unit raise {
  defvar_init(q_ear_autoloaded_files, Nil)
  defvar_init(q_ear_builtin_symbol_props, make_hash_table())
  defvar_init(q_ear_builtin_symbol_values, make_hash_table())
  putprop(q_d_debugmode, q_debugmode1, q_assign) |> ignore
  putprop(q_d_poislim, q_poislim1, q_assign) |> ignore
  for x in [
    (q_d_block, q_mprog),
    (q_d_lambda, q_lambda),
    (q_d_subst, q_d_substitute),
    (q_d_go, q_mgo),
    (q_d_signum, q_p_signum),
    (q_d_return, q_mreturn),
    (q_d_factorial, q_mfactorial),
    (q_d_ibase, q_ear_read_base),
    (q_d_obase, q_ear_print_base),
    (q_d_mode_declare, q_d_modedeclare),
  ] {
    putprop(x.0, x.1, q_alias) |> ignore
    putprop(x.1, x.0, q_reversealias) |> ignore
  }
  // Validate values assigned to $ibase and $obase, which are aliased to
  // *read-base* and *print-base*, respectively, above.
  let base_check = lfunc("base-assign", args => {
    let val = arg(args, 1)
    if !(fixnump(val) && num_ge(val, Fix(2L)) && num_le(val, Fix(36L))) {
      mseterr(
        arg(args, 0),
        val,
        reason=Str("must be an integer between 2 and 36, inclusive"),
      )
      |> ignore
    }
    Nil
  })
  putprop(q_ear_read_base, base_check, q_assign) |> ignore
  putprop(q_ear_print_base, base_check, q_assign) |> ignore
  for x in [
    (q_d_ratcoeff, q_d_ratcoef),
    (q_d_ratnum, q_d_ratnumer),
    (q_d_true, t),
    (q_d_derivative, q_d_diff),
    (q_d_prod, q_d_product),
    (q_d_bothcoeff, q_d_bothcoef),
  ] {
    putprop(x.0, x.1, q_alias) |> ignore
  }
  register_mspec(q_d_sstatus, form => suprv1__sstatus(cadr(form), caddr(form)))
  for l in [
    q_d_sin, q_d_cos, q_d_tan, q_d_sec, q_d_csc, q_d_cot, q_d_sinh, q_d_cosh, q_d_tanh,
    q_d_sech, q_d_csch, q_d_coth, q_d_asin, q_d_acos, q_d_atan, q_d_acot, q_d_acsc,
    q_d_asec, q_d_asinh, q_d_acosh, q_d_atanh, q_d_acsch, q_d_asech, q_d_acoth,
    q_d_del,
  ] {
    let x = d_nounify(l)
    putprop(l, x, q_alias) |> ignore
    putprop(x, l, q_reversealias) |> ignore
  }
  d_nounify(q_d_sum) |> ignore
  d_nounify(q_d_lsum) |> ignore
  d_nounify(q_d_product) |> ignore
  d_nounify(q_d_integrate) |> ignore
  d_nounify(q_d_limit) |> ignore
  putprop(q_d_diff, q_p_derivative, q_verb) |> ignore
  putprop(q_p_derivative, q_d_diff, q_noun) |> ignore
  setf_get(q_p_at_difference, q_dimension, q_dimension__pctat_difference)
  |> ignore
}
