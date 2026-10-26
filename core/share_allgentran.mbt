// Port of share/contrib/gentran/allgentran.lisp (part 1): the CONVMAC
// compatibility layer, template processing (templt.l), declarations &
// initializations (init.l), general functions (global.l), code printing
// and the error handler (output.l), and the Maxima -> Lisp translation
// (vaxlsp.l).
//
// GENTRAN translates Maxima statements into an intermediate Lisp form
// ("franz" Lisp: (setq x (plus a b)), (cond ...), (do ...), ...), optionally
// segments long expressions, and then into token lists for Fortran, Ratfor
// or C. A token is printed with PRINC, except a list token, which is a form
// to evaluate: (forttab n), (rattab n), (ctab n) or (terpri).

// ---------------------------------------------------------------------------
// convmac: helpers and the function-like macros

///|
let allgentran__q_eof : Value = q_d_eof_dol

///|
/// The fresh list (nil), the marker of a "parallel" output file group.
fn allgentran__nil_pair() -> Value {
  list1(Nil)
}

///|
/// A minimal evaluator for the Lisp forms GENTRAN builds and EVALs: the
/// printing tokens (forttab n), (rattab n), (ctab n), (terpri), the forms
/// stored on the SIMPFG property, and (or ...), (and ...), (+ ...) over
/// already computed values.
fn allgentran__eval(form : Value) -> Value raise {
  match form {
    Nil => Nil
    Sym(_) => symval(form)
    Cons({ car: op, cdr: args }) =>
      if eq(op, q_quote) {
        car(args)
      } else if eq(op, q_terpri) {
        terpri()
        Nil
      } else if eq(op, q_or) {
        for a in args.iter() {
          let v = allgentran__eval(a)
          if v.truthy() {
            return v
          }
        }
        Nil
      } else if eq(op, q_and) {
        let mut v = t
        for a in args.iter() {
          v = allgentran__eval(a)
          if !v.truthy() {
            return Nil
          }
        }
        v
      } else if eq(op, q_op_plus) {
        let mut s : Value = Fix(0L)
        for a in args.iter() {
          s = num_add(s, allgentran__eval(a))
        }
        s
      } else if eq(op, q_forttab) {
        forttab(allgentran__eval(car(args)))
      } else if eq(op, q_rattab) {
        rattab(allgentran__eval(car(args)))
      } else if eq(op, q_ctab) {
        ctab(allgentran__eval(car(args)))
      } else {
        funcall(op, list_to_array(mapcar(a => allgentran__eval(a), args)))
      }
    _ => form
  }
}

///|
/// `(close stream)`: the port's file output streams write through to the
/// file, so there is nothing to flush.
fn allgentran__close(stream : Value) -> Unit {
  ignore(stream)
}

///|
/// `(read-char (cdr *currin*) nil '$eof$)`
fn allgentran__rc() -> Value raise {
  read_char(stream=cdr(symval(q_ear_currin)), eof_value=allgentran__q_eof)
}

///|
fn allgentran__lang() -> Value raise {
  stripdollar1(symval(q_d_gentranlang))
}

///|
/// `(or (car *currout*) (cons '(mlist) (cdr *currout*)))`
fn allgentran__currout_value() -> Value {
  let co = symval(q_ear_currout)
  let a = car(co)
  if a.truthy() {
    a
  } else {
    cons(list1(q_mlist), cdr(co))
  }
}

///|
/// `(foreach elt in/on lst do/collect/conc stmt)` expands into a mapping
/// function call; this returns the expansion.
fn foreach(
  elt_ : Value,
  kw1 : Value,
  lst : Value,
  kw2 : Value,
  stmt : Value,
) -> Value raise {
  let table = list([
    list([
      q_in,
      cons(q_do, q_mapc),
      cons(q_collect, q_mapcar),
      cons(q_conc, q_mapcan),
    ]),
    list([
      q_on,
      cons(q_do, q_map),
      cons(q_collect, q_maplist),
      cons(q_conc, q_mapcon),
    ]),
  ])
  let fcn = cdr(assoc(kw2, cdr(assoc(kw1, table))))
  let fn_form = list2(q_function, list3(q_lambda, list1(elt_), stmt))
  if member(fcn, list2(q_mapc, q_map)).truthy() {
    list3(q_progn, list3(fcn, fn_form, lst), Nil)
  } else {
    list3(fcn, fn_form, lst)
  }
}

///|
/// `(aconc lst elt)`  -->  `(nconc lst (list elt))`
fn aconc(m1 : Value, m2 : Value) -> Value raise {
  nconc(m1, list1(m2))
}

///|
fn caaaddr(p : Value) -> Value raise {
  caaar(cddr(p))
}

///|
fn cadaddr(x : Value) -> Value raise {
  car(cdr(car(cdr(cdr(x)))))
}

///|
fn caddaddr(x : Value) -> Value raise {
  car(cdr(cdr(car(cdr(cdr(x))))))
}

///|
/// The 8th element (nth 7).
fn cadddddddr(x : Value) -> Value raise {
  car(cdr(cdr(cdr(cdr(cdr(cdr(cdr(x))))))))
}

///|
fn caddddddr(x : Value) -> Value raise {
  car(cdr(cdr(cdr(cdr(cdr(cdr(x)))))))
}

///|
fn cadddddr(x : Value) -> Value raise {
  car(cdr(cdr(cdr(cdr(cdr(x))))))
}

///|
fn cdadaddr(x : Value) -> Value raise {
  cdr(car(cdr(car(cdr(cdr(x))))))
}

///|
fn caddddr(x : Value) -> Value raise {
  car(cdr(cdr(cdr(cdr(x)))))
}

///|
/// `(compress lst)  -->  (implode lst)`: the string of a list of characters.
fn compress(m : Value) -> Value raise {
  let sb = StringBuilder::new()
  for c in m.iter() {
    match c {
      Char(ch) => sb.write_char(ch)
      _ => raise type_error(c, "character")
    }
  }
  Str(sb.to_string())
}

///|
fn append1(x : Value, y : Value) -> Value raise {
  append(x, cons(y, Nil))
}

///|
/// `(delete1 elt lst)  -->  (delete elt lst :count 1)`: without the first
/// element EQL to elt.
fn delete1(e : Value, lst : Value) -> Value raise {
  let r = []
  let mut p = lst
  let mut found = false
  while p is Cons(c) {
    if !found && eql(e, c.car) {
      found = true
      p = c.cdr
      if p is Nil && r.is_empty() {
        return Nil
      }
      // share the rest of the list, as CL DELETE does
      let mut res = p
      for i = r.length() - 1; i >= 0; i = i - 1 {
        res = cons(r[i], res)
      }
      return res
    }
    r.push(c.car)
    p = c.cdr
  }
  lst
}

///|
/// `(explode2 arg)  -->  (explodec arg)`
fn explode2(m : Value) -> Value raise {
  string_to_char_list(princ_to_string(m))
}

///|
/// `(flag varlst fname)`; the macro uses the second and third of its
/// arguments.
fn flag(m : Value) -> Value raise {
  for v in cadr(m).iter() {
    putprop(v, t, caddr(m)) |> ignore
  }
  Nil
}

///|
fn flagp(var_ : Value, fname : Value) -> Value raise {
  get(var_, fname)
}

///|
fn geq(n1 : Value, n2 : Value) -> Value raise {
  lbool(num_ge(n1, n2))
}

///|
fn idp(m : Value) -> Value raise {
  lbool(symbolp(m))
}

///|
fn mkfil(m : Value) -> Value raise {
  if streamp(m) {
    m
  } else {
    stripdollar(m)
  }
}

///|
/// The output column of *standard-output*.
fn posn() -> Value raise {
  int(stream_column())
}

///|
/// `(prettyprint exp)  -->  (prog1 (linear-displa exp) (terpri))`
fn prettyprint(m : Value) -> Value raise {
  let r = linear_displa(m)
  terpri()
  r
}

///|
fn put(id : Value, proptype : Value, propval : Value) -> Value raise {
  putprop(id, propval, proptype)
}

///|
fn rederr(m : Value) -> Value raise {
  cons(q_error, m)
}

///|
fn remflag(varlst : Value, fname : Value) -> Value raise {
  for v in varlst.iter() {
    remprop(v, fname) |> ignore
  }
  Nil
}

///|
/// `(repeat stmt exp)` expands into a PROG loop running stmt until exp is
/// true; this returns the expansion.
fn repeat(stmt : Value, exp_ : Value) -> Value raise {
  list([
    q_prog,
    Nil,
    q_loop,
    stmt,
    list2(q_cond, list2(list2(q_not, exp_), list2(q_go, q_loop))),
  ])
}

///|
fn spaces(m : Value) -> Value raise {
  let n = to_int(m)
  for i = 0; i < n; i = i + 1 {
    princ(Str(" ")) |> ignore
  }
  Nil
}

// ---------------------------------------------------------------------------
// templt.l: template processing

///|
fn procforttem() -> Value raise {
  let mut c = procfortcomm()
  while !eq(c, allgentran__q_eof) {
    if eql(c, symval(q_ear_cr)) {
      pprin2(symval(q_ear_cr)) |> ignore
      c = procfortcomm()
    } else if eql(c, Char('<')) {
      c = allgentran__rc()
      if eql(c, Char('<')) {
        c = procactive()
      } else {
        pprin2(Char('<')) |> ignore
        pprin2(c) |> ignore
        c = allgentran__rc()
      }
    } else if eq(c, Char('>')) {
      c = allgentran__rc()
      if eql(c, Char('>')) {
        // ">>" in a passive section terminates file processing
        c = allgentran__q_eof
      } else {
        pprin2(Char('>')) |> ignore
        pprin2(c) |> ignore
        c = allgentran__rc()
      }
    } else {
      pprin2(c) |> ignore
      c = allgentran__rc()
    }
  }
  Nil
}

///|
/// Copy Fortran comment lines (c, C or * in column 1); returns the first
/// character after them.
fn procfortcomm() -> Value raise {
  while true {
    let c0 = allgentran__rc()
    if !member(c0, list([Char('c'), Char('C'), Char('*')])).truthy() {
      return c0
    }
    pprin2(c0) |> ignore
    while true {
      let c = allgentran__rc()
      if eql(c, Char('\n')) {
        pprin2(c) |> ignore
        break
      } else if eq(c, allgentran__q_eof) {
        pprin2(Char('\n')) |> ignore
        break
      } else {
        pprin2(c) |> ignore
      }
    }
  }
  Nil
}

///|
fn procrattem() -> Value raise {
  let mut c = allgentran__rc()
  while !eq(c, allgentran__q_eof) {
    if eq(c, symval(q_sharpsign)) {
      c = procratcomm()
    } else if eql(c, Char('<')) {
      c = allgentran__rc()
      if eql(c, Char('<')) {
        c = procactive()
      } else {
        pprin2(q_op_lt) |> ignore
        pprin2(c) |> ignore
        c = allgentran__rc()
      }
    } else if eq(c, Char('>')) {
      c = allgentran__rc()
      if eq(c, Char('>')) {
        c = allgentran__q_eof
      } else {
        pprin2(Char('>')) |> ignore
        pprin2(c) |> ignore
        c = allgentran__rc()
      }
    } else {
      pprin2(c) |> ignore
      c = allgentran__rc()
    }
  }
  Nil
}

///|
/// `# ... <cr>`
fn procratcomm() -> Value raise {
  pprin2(symval(q_sharpsign)) |> ignore
  while true {
    let c = allgentran__rc()
    if eql(c, symval(q_ear_cr)) {
      break
    }
    pprin2(c) |> ignore
  }
  pprin2(symval(q_ear_cr)) |> ignore
  allgentran__rc()
}

///|
fn procctem() -> Value raise {
  let mut c = allgentran__rc()
  while !eq(c, allgentran__q_eof) {
    if eql(c, symval(q_ear_slash)) {
      c = procccomm()
    } else if eql(c, Char('<')) {
      c = allgentran__rc()
      if eql(c, Char('<')) {
        c = procactive()
      } else {
        pprin2(Char('<')) |> ignore
        pprin2(c) |> ignore
        c = allgentran__rc()
      }
    } else if eql(c, Char('>')) {
      c = allgentran__rc()
      if eql(c, Char('>')) {
        c = allgentran__q_eof
      } else {
        pprin2(Char('>')) |> ignore
        pprin2(c) |> ignore
        c = allgentran__rc()
      }
    } else {
      pprin2(c) |> ignore
      c = allgentran__rc()
    }
  }
  Nil
}

///|
/// `/* ... */`
fn procccomm() -> Value raise {
  pprin2(symval(q_ear_slash)) |> ignore
  let mut c = allgentran__rc()
  if eql(c, Char('*')) {
    pprin2(c) |> ignore
    c = allgentran__rc()
    while true {
      while !eql(c, Char('*')) {
        pprin2(c) |> ignore
        c = allgentran__rc()
      }
      pprin2(c) |> ignore
      c = allgentran__rc()
      if eql(c, symval(q_ear_slash)) {
        break
      }
    }
    pprin2(c) |> ignore
    c = allgentran__rc()
  }
  c
}

///|
/// Read the Maxima statements of an active part ("<<" ... ">>") and MEVAL
/// each.
fn procactive() -> Value raise {
  while true {
    let vexp = d_readvexp(symval(q_ear_currin))
    let vexptrm = symval(q_n_starvexptrm)
    meval(vexp) |> ignore
    if member(vexptrm, list2(Char('\u{0}'), Char('>'))).truthy() {
      let c = allgentran__rc()
      if equal(c, symval(q_ear_cr)) {
        return allgentran__rc()
      }
      return c
    }
  }
  Nil
}

///|
/// `(peek-char t stream)`: skip whitespace, then peek.
fn allgentran__peek_skip_ws(stream : Value) -> Value raise {
  while true {
    let c = peek_char(stream~, eof_value=allgentran__q_eof)
    match c {
      Char(' ' | '\t' | '\n' | '\r' | '\u{0c}') => read_char(stream~) |> ignore
      Char(_) => return c
      _ => raise LispError::SimpleError("end of file on \{princ_to_string(stream)}")
    }
  }
  Nil
}

///|
fn d_readvexp(in_ : Value) -> Value raise {
  let iport = cdr(in_)
  let test_ = allgentran__peek_skip_ws(iport)
  if equal(test_, Char('>')) {
    if equal(read_char(stream=iport), Char('>')) &&
      equal(read_char(stream=iport), Char('>')) {
      set(q_n_starvexptrm, test_) |> ignore
      return Nil
    } else {
      gentranerr(q_e, Nil, Str("single > after active statement")) |> ignore
    }
  } else if member(test_, list([Char(';'), Char('$'), Char('\u{0}')])).truthy() {
    set(q_n_starvexptrm, test_) |> ignore
  }
  set(q_n_starvexptrm, Char('$')) |> ignore
  let r = with_special(q_ear_prompt_on_read_hang, Nil, () => mread(
    list2(iport, Nil),
  ))
  caddr(r)
}

// ---------------------------------------------------------------------------
// init.l: user-accessible variables, file paths, system variables

///|
fn concat2(str1 : Value, str2 : Value) -> Value raise {
  compress(append(exploden(str1), exploden(str2)))
}

///|
fn outpath(fname : Value) -> Value raise {
  if symval(q_d_genoutpath).truthy() &&
    !member(fname, list([q_d_all, t, Nil])).truthy() {
    concat2(symval(q_d_genoutpath), fname)
  } else {
    fname
  }
}

///|
fn fsearch(inf : Value) -> Value raise {
  let p = symval(q_d_geninpath)
  if p.truthy() {
    d_file_search(inf, paths=p)
  } else {
    d_file_search(inf)
  }
}

// ---------------------------------------------------------------------------
// global.l: temporary variables, statement numbers, symbol table, file
// stacks, Lisp form construction and predicates

///|
/// A temporary variable of type TYPE (default $tempvartype): the first
/// unmarked $tempvarname<n> whose type is TYPE or undeclared.
fn tempvar(type_ : Value) -> Value raise {
  let mut type_ = type_
  if symval(q_d_tempvartype).truthy() {
    set(q_d_tempvartype, stripdollar1(symval(q_d_tempvartype))) |> ignore
  }
  if member(type_, list2(Nil, Fix(0L))).truthy() {
    type_ = symval(q_d_tempvartype)
  }
  if type_.truthy() {
    type_ = stripdollar1(type_)
  }
  set(q_d_tempvarname, stripdollar1(symval(q_d_tempvarname))) |> ignore
  let mut num = symval(q_d_tempvarnum)
  let mut tvar : Value = Nil
  while true {
    tvar = implode(append(exploden(symval(q_d_tempvarname)), explode(num)))
    if markedvarp(tvar).truthy() ||
      !member(getvartype(tvar), list2(type_, Nil)).truthy() {
      num = num_add(Fix(1L), num)
      continue
    }
    break
  }
  put(tvar, q_ear_vtype, type_) |> ignore
  if equal(type_, q_unknown) {
    gentranerr(q_w, tvar, Str("undeclared variable")) |> ignore
  } else if type_.truthy() {
    symtabput(Nil, tvar, list1(type_)) |> ignore
  }
  tvar
}

///|
fn markvar(var_ : Value) -> Value raise {
  if numberp(var_) {
    var_
  } else if atom(var_) {
    putprop(var_, t, q_ear_marked) |> ignore
    var_
  } else {
    for v in var_.iter() {
      markvar(v) |> ignore
    }
    var_
  }
}

///|
fn markedvarp(var_ : Value) -> Value raise {
  flagp(var_, q_ear_marked)
}

///|
fn unmarkvar(var_ : Value) -> Value raise {
  if numberp(var_) {
    var_
  } else {
    remflag(list1(var_), q_ear_marked)
  }
}

///|
fn recurunmark(exp_ : Value) -> Value raise {
  if atom(exp_) {
    unmarkvar(exp_)
  } else {
    for elt in exp_.iter() {
      recurunmark(elt) |> ignore
    }
    Nil
  }
}

///|
fn genstmtno() -> Value raise {
  set(q_d_genstmtno, num_add(symval(q_d_genstmtno), symval(q_d_genstmtincr)))
}

///|
/// call                                                inserts
/// (symtabput subprogname nil       nil              ) subprog name
/// (symtabput subprogname '*type*   subprogtype      ) subprogram type
/// (symtabput subprogname '*params* paramlist        ) parameter list
/// (symtabput subprogname vname     '(type d1 d2 ...)) type & dimensions
/// (subprogname nil means the current one, car of *symboltable*)
fn symtabput(name : Value, type_ : Value, value : Value) -> Value raise {
  let st = symval(q_ear_symboltable)
  let name = if name.truthy() { name } else { car(st) }
  set(q_ear_symboltable, cons(name, delete1(name, st))) |> ignore
  if member(type_, list2(q_ear_type, q_ear_params)).truthy() {
    put(name, type_, value)
  } else if type_.truthy() {
    let v = type_
    let mut vtype = car(value)
    let mut vdims = cdr(value)
    let mut decs = get(name, q_ear_decs)
    let mut dec = assoc(v, decs)
    decs = delete1(dec, decs)
    if !vtype.truthy() {
      vtype = if length(dec) > 1 { cadr(dec) } else { Nil }
    }
    if !vdims.truthy() {
      vdims = if length(dec) > 2 { cddr(dec) } else { Nil }
    }
    dec = cons(v, cons(vtype, vdims))
    put(name, q_ear_decs, aconc(decs, dec))
  } else {
    Nil
  }
}

///|
/// call                              retrieves
/// (symtabget nil         nil      ) all subprogram names
/// (symtabget subprogname '*type*  ) subprogram type
/// (symtabget subprogname '*params*) parameter list
/// (symtabget subprogname vname    ) type & dimensions for variable
/// (symtabget subprogname '*decs*  ) all types & dimensions
fn symtabget(name : Value, type_ : Value) -> Value raise {
  let mut name = name
  if type_.truthy() && !name.truthy() {
    name = car(symval(q_ear_symboltable))
  }
  if !name.truthy() {
    symval(q_ear_symboltable)
  } else if member(type_, list([q_ear_type, q_ear_params, q_ear_decs])).truthy() {
    get(name, type_)
  } else {
    assoc(type_, get(name, q_ear_decs))
  }
}

///|
fn symtabrem(name : Value, type_ : Value) -> Value raise {
  let st = symval(q_ear_symboltable)
  let name = if name.truthy() { name } else { car(st) }
  if !type_.truthy() {
    let r = delete1(name, st)
    set(q_ear_symboltable, if r.truthy() { r } else { list1(q_ear_main) })
  } else if member(type_, list([q_ear_type, q_ear_params, q_ear_decs])).truthy() {
    remprop(name, type_)
  } else {
    let v = type_
    let mut decs = get(name, q_ear_decs)
    let dec = assoc(v, decs)
    decs = delete1(dec, decs)
    put(name, q_ear_decs, decs)
  }
}

///|
fn getvartype(var_ : Value) -> Value raise {
  let var_ = if listp(var_) { car(var_) } else { var_ }
  let mut type_ = symtabget(Nil, var_)
  if type_.truthy() && length(type_) > 1 {
    type_ = cadr(type_)
  } else {
    type_ = Nil
  }
  // no implicit typing in C
  if symval(q_d_implicit).truthy() &&
    !eq(allgentran__lang(), q_c) &&
    atom(var_) &&
    !type_.truthy() {
    type_ = imptype(var_)
  }
  type_
}

///|
/// Set gentranlang with checking (it can also be set directly).
fn d_setgentranlang(a : Value) -> Value raise {
  let a = stripdollar1(a)
  if !memq(a, list([q_fortran, q_ratfor, q_c])).truthy() {
    merr("arg must be one of fortran c or ratfor", []) |> ignore
  }
  set(q_d_gentranlang, a)
}

///|
fn imptype(var_ : Value) -> Value raise {
  if member(
      car(exploden(var_)),
      list([
        Char('i'),
        Char('j'),
        Char('k'),
        Char('l'),
        Char('m'),
        Char('n'),
        Char('I'),
        Char('J'),
        Char('K'),
        Char('L'),
        Char('M'),
        Char('N'),
      ]),
    ).truthy() {
    q_integer
  } else {
    q_real
  }
}

///|
/// Is exp an array element? (undeclared array elements display with [...]
/// in C)
fn arrayeltp(exp_ : Value) -> Value raise {
  let a = get(car(exp_), q_array)
  if a.truthy() {
    a
  } else {
    lbool(length(symtabget(Nil, car(exp_))) > 2)
  }
}

///|
fn delinstk(pr : Value) -> Value raise {
  let r = delete1(pr, symval(q_ear_instk))
  set(q_ear_instk, if r.truthy() { r } else { list1(symval(q_ear_stdin)) })
  |> ignore
  set(q_ear_currin, car(symval(q_ear_instk)))
}

///|
/// Remove all occurrences of a filepair from the output file stack.
fn delstk(pr : Value) -> Value raise {
  while member(pr, cdr(reverse(symval(q_ear_outstk)))).truthy() {
    popstk(pr) |> ignore
  }
  Nil
}

///|
fn flisteqp(flist1 : Value, flist2 : Value) -> Value raise {
  let mut flist1 = mapcar(f => mkfil(f), flist1)
  for f in flist2.iter() {
    flist1 = delete1(mkfil(f), flist1)
  }
  lbool(null(flist1))
}

///|
/// The filepair of fname in the stack stk.
fn filpr(fname : Value, stk : Value) -> Value raise {
  if !stk.truthy() {
    Nil
  } else if caar(stk).truthy() && equal(mkfil(fname), mkfil(caar(stk))) {
    car(stk)
  } else {
    filpr(fname, cdr(stk))
  }
}

///|
/// Open an output channel and return the filepair (fname . stream).
fn mkfilpr(fname : Value) -> Value raise {
  cons(
    fname,
    if streamp(fname) {
      fname
    } else {
      open_output_file(lstring(fname), append=true)
    },
  )
}

///|
/// The "parallel" filepair (nil f1 ... fn) of flist in the stack stk.
fn pfilpr(flist : Value, stk : Value) -> Value raise {
  if !stk.truthy() {
    Nil
  } else if !caar(stk).truthy() && flisteqp(flist, cdar(stk)).truthy() {
    car(stk)
  } else {
    pfilpr(flist, cdr(stk))
  }
}

///|
fn popinstk() -> Value raise {
  delinstk(symval(q_ear_currin))
}

///|
/// Remove the top-most occurrence of a filepair from the output stack.
fn popstk(pr : Value) -> Value raise {
  if car(pr).truthy() {
    resetstk(delete1(pr, symval(q_ear_outstk)))
  } else {
    let mut stk1 = symval(q_ear_outstk)
    let mut stk2 : Value = Nil
    while !equal(car(stk1), pr) {
      stk2 = aconc(stk2, car(stk1))
      stk1 = cdr(stk1)
    }
    while !equal(car(stk1), allgentran__nil_pair()) {
      stk1 = cdr(stk1)
    }
    resetstk(append(stk2, cdr(stk1)))
  }
}

///|
fn pushinstk(pr : Value) -> Value raise {
  set(q_ear_instk, cons(pr, symval(q_ear_instk))) |> ignore
  set(q_ear_currin, car(symval(q_ear_instk)))
}

///|
/// Push a filepair onto the output file stack.
fn pushstk(pr : Value) -> Value raise {
  set(q_ear_outstk, cons(pr, symval(q_ear_outstk))) |> ignore
  resetstkvars()
}

///|
fn resetstk(stk : Value) -> Value raise {
  let mut stk = stk
  let mut s : Value = Nil
  if stk.truthy() {
    while true {
      if caar(stk).truthy() || equal(car(stk), allgentran__nil_pair()) {
        s = aconc(s, car(stk))
      } else {
        for f in cdar(stk).iter() {
          if !filpr(f, symval(q_ear_outstk)).truthy() {
            stk = cons(delete1(f, car(stk)), cdr(stk))
          }
        }
        if equal(car(stk), allgentran__nil_pair()) {
          stk = cdr(stk)
        } else {
          s = aconc(s, car(stk))
        }
      }
      stk = cdr(stk)
      if !stk.truthy() {
        break
      }
    }
  }
  set(q_ear_outstk, if s.truthy() { s } else { list1(symval(q_ear_stdout)) })
  |> ignore
  resetstkvars()
}

///|
/// Reset the current output to the filepair on top of the output stack and
/// the channel list to the streams of the name(s) in it.
fn resetstkvars() -> Value raise {
  let outstk = symval(q_ear_outstk)
  let currout = set(q_ear_currout, car(outstk))
  set(
    q_ear_outchanl,
    if car(currout).truthy() {
      list1(cdr(currout))
    } else {
      mapcar(f => cdr(filpr(f, outstk)), cdr(currout))
    },
  )
}

///|
fn mkassign(var_ : Value, exp_ : Value) -> Value raise {
  list3(q_setq, var_, exp_)
}

///|
fn mkcond(pairs : Value) -> Value raise {
  cons(q_cond, pairs)
}

///|
fn mkdef(name : Value, params : Value, body : Value) -> Value raise {
  append(list3(q_defun, name, params), body)
}

///|
fn mkdo(var_ : Value, exitcond : Value, body : Value) -> Value raise {
  append(list3(q_do, var_, exitcond), body)
}

///|
fn mkreturn(exp_ : Value) -> Value raise {
  list2(q_return, exp_)
}

///|
fn mkstmtgp(vars : Value, stmts : Value) -> Value raise {
  if numberp(vars) {
    cons(q_progn, stmts)
  } else {
    cons(q_prog, cons(vars, stmts))
  }
}

///|
fn mkterpri() -> Value raise {
  list1(q_terpri)
}

///|
fn lispassignp(stmt : Value) -> Value raise {
  lbool(listp(stmt) && equal(car(stmt), q_setq))
}

///|
fn lispbreakp(form : Value) -> Value raise {
  lbool(equal(car(form), q_break))
}

///|
fn lispcallp(form : Value) -> Value raise {
  lbool(listp(form))
}

///|
fn lispcondp(stmt : Value) -> Value raise {
  lbool(listp(stmt) && equal(car(stmt), q_cond))
}

///|
fn lispdefp(form : Value) -> Value raise {
  if listp(form) {
    member(car(form), symval(q_ear_lispdefops))
  } else {
    Nil
  }
}

///|
fn lispdop(stmt : Value) -> Value raise {
  lbool(listp(stmt) && equal(car(stmt), q_do))
}

///|
fn lispexpp(form : Value) -> Value raise {
  if atom(form) {
    return t
  }
  let m = member(
    car(form),
    append(symval(q_ear_lisparithexpops), symval(q_ear_lisplogexpops)),
  )
  if m.truthy() {
    return m
  }
  lbool(
    !member(
      car(form),
      append(
        append(symval(q_ear_lispstmtops), symval(q_ear_lispstmtgpops)),
        symval(q_ear_lispdefops),
      ),
    ).truthy(),
  )
}

///|
fn lispendp(form : Value) -> Value raise {
  lbool(listp(form) && equal(car(form), q_end))
}

///|
fn lispgop(form : Value) -> Value raise {
  lbool(equal(car(form), q_go))
}

///|
fn lisplabelp(form : Value) -> Value raise {
  lbool(atom(form))
}

///|
fn lisplogexpp(form : Value) -> Value raise {
  if atom(form) {
    return t
  }
  let m = member(car(form), symval(q_ear_lisplogexpops))
  if m.truthy() {
    return m
  }
  lbool(
    !member(
      car(form),
      append(
        append(symval(q_ear_lisparithexpops), symval(q_ear_lispstmtops)),
        append(symval(q_ear_lispstmtgpops), symval(q_ear_lispdefops)),
      ),
    ).truthy(),
  )
}

///|
fn lispprintp(form : Value) -> Value raise {
  lbool(equal(car(form), q_princ))
}

///|
fn lispreadp(form : Value) -> Value raise {
  lbool(
    equal(car(form), q_setq) &&
    listp(caddr(form)) &&
    equal(car(caddr(form)), q_read),
  )
}

///|
fn lispreturnp(stmt : Value) -> Value raise {
  lbool(listp(stmt) && equal(car(stmt), q_return))
}

///|
fn lispstmtp(form : Value) -> Value raise {
  if atom(form) {
    return t
  }
  let m = member(car(form), symval(q_ear_lispstmtops))
  if m.truthy() {
    return m
  }
  lbool(
    atom(car(form)) &&
    !member(
      car(form),
      append(
        append(symval(q_ear_lisparithexpops), symval(q_ear_lisplogexpops)),
        append(symval(q_ear_lispstmtgpops), symval(q_ear_lispdefops)),
      ),
    ).truthy(),
  )
}

///|
fn lispstmtgpp(form : Value) -> Value raise {
  if listp(form) {
    member(car(form), symval(q_ear_lispstmtgpops))
  } else {
    Nil
  }
}

///|
fn lispstopp(form : Value) -> Value raise {
  lbool(equal(car(form), q_stop))
}

///|
/// Does stmt contain an assignment to name, (setq name exp), or a
/// (return exp) statement?
fn gfunctionp(stmt : Value, name : Value) -> Value raise {
  if null(stmt) || atom(stmt) {
    Nil
  } else if equal(car(stmt), q_setq) && equal(cadr(stmt), name) {
    t
  } else if equal(car(stmt), q_return) && cdr(stmt).truthy() {
    t
  } else {
    let rs = mapcar(st => gfunctionp(st, name), stmt)
    for r in rs.iter() {
      if r.truthy() {
        return r
      }
    }
    Nil
  }
}

///|
/// Does the type name start like "implicit"?
fn implicitp(type_ : Value) -> Value raise {
  let (xtype0, ximp0) = if stringp(type_) {
    (exploden(type_), exploden(q_implicit))
  } else {
    (explode2(type_), explode2(q_implicit))
  }
  let mut xtype = xtype0
  let mut ximp = ximp0
  let mut r = true
  while true {
    r = r && equal(car(xtype), car(ximp))
    xtype = cdr(xtype)
    if null(xtype) {
      break
    }
    ximp = cdr(ximp)
    if null(ximp) {
      break
    }
  }
  lbool(r)
}

///|
fn inttypep(type_ : Value) -> Value raise {
  let m = member(type_, list([q_integer, q_int, q_long, q_short]))
  if m.truthy() {
    return m
  }
  let mut xtype = exploden(type_)
  let mut xint = exploden(q_integer)
  let mut r = true
  while true {
    r = r && equal(car(xtype), car(xint))
    xtype = cdr(xtype)
    if null(xtype) {
      break
    }
    xint = cdr(xint)
    if null(xint) {
      break
    }
  }
  lbool(r)
}

///|
fn complexdop(dostmt : Value) -> Value raise {
  lbool(
    lispdop(dostmt).truthy() &&
    (length(cadr(dostmt)) > 1 || length(caddr(dostmt)) > 1),
  )
}

///|
/// ((var type d1 d2 ..) ...)  -->  ((type (var d1 d2 ..) ..) ...)
fn formtypelists(varlists : Value) -> Value raise {
  let mut typelists : Value = Nil
  for vl0 in varlists.iter() {
    let type_ = cadr(vl0)
    let mut vl = delete1(type_, vl0)
    if onep(int(length(vl))).truthy() {
      vl = car(vl)
    }
    let mut tl = assoc(type_, typelists)
    if tl.truthy() {
      typelists = delete1(tl, typelists)
    } else {
      tl = list1(type_)
    }
    typelists = aconc(typelists, aconc(tl, vl))
  }
  typelists
}

///|
fn insertcommas(lst : Value) -> Value raise {
  if null(lst) {
    return Nil
  }
  let mut result = list1(car(lst))
  let mut lst = cdr(lst)
  while lst.truthy() {
    result = cons(car(lst), cons(q_op_cm, result))
    lst = cdr(lst)
  }
  reverse(result)
}

///|
/// MEVALP without the call to MERROR.
fn noerrmevalp(pred : Value) -> Value raise {
  let ans = mevalp1(pred)
  if member(ans, list2(t, Nil)).truthy() {
    ans
  } else {
    q_d_unknown
  }
}

///|
fn simplifydo(dostmt : Value) -> Value raise {
  if !lispdop(dostmt).truthy() {
    return dostmt
  }
  let mut varlst = reverse(cadr(dostmt))
  let mut exitlst = caddr(dostmt)
  let stmtlst = mapcar(st => simplifydo(st), cdddr(dostmt))
  let mut result = mapcar(st => simplifydo(st), cdr(exitlst))
  exitlst = list1(car(exitlst))
  let mut tmp1 : Value = Nil
  let mut tmp2 : Value = Nil
  for var_ in cdr(varlst).iter() {
    tmp1 = cons(mkassign(car(var_), cadr(var_)), tmp1)
    if cddr(var_).truthy() {
      tmp2 = cons(mkassign(car(var_), caddr(var_)), tmp2)
    }
  }
  varlst = list1(car(varlst))
  result = cons(mkdo(varlst, exitlst, append(stmtlst, tmp2)), result)
  result = append(tmp1, result)
  result
}

///|
fn seqtogp(lst : Value) -> Value raise {
  if null(lst) ||
    atom(lst) ||
    lispstmtp(lst).truthy() ||
    lispstmtgpp(lst).truthy() {
    lst
  } else if onep(int(length(lst))).truthy() && listp(car(lst)) {
    seqtogp(car(lst))
  } else {
    mkstmtgp(Fix(0L), mapcar(st => seqtogp(st), lst))
  }
}

///|
fn stripdollar1(x : Value) -> Value raise {
  if !atom(x) {
    if eq(caar(x), q_bigfloat) && !minusp(cadr(x)) {
      implode(fpformat(x))
    } else {
      merr("atomic arg required; found ~M", [x])
    }
  } else if numberp(x) {
    x
  } else {
    let s = lstring(string(x))
    if s.length() > 0 && (s[0] == '$' || s[0] == '%') {
      sym(s.unsafe_substring(start=1, end=s.length()))
    } else {
      x
    }
  }
}

// ---------------------------------------------------------------------------
// output.l: code formatting & printing, error handler

///|
fn princ_invert_case(sym_ : Value) -> Value raise {
  princ(print_invert_case(sym_))
}

///|
/// Print a token list: a list token is a form to evaluate, any other token
/// is printed, starting a continuation line first when it would not fit.
fn allgentran__format1(
  lst : Value,
  linelen : Value,
  contline : () -> Value raise,
) -> Value raise {
  for elt in lst.iter() {
    if listp(elt) {
      allgentran__eval(elt) |> ignore
    } else {
      if num_gt(
          num_add(posn(), int(length(explode2(elt)))),
          symval(linelen),
        ) {
        contline() |> ignore
      }
      princ_invert_case(elt) |> ignore
    }
  }
  Nil
}

///|
fn formatfort(lst : Value) -> Value raise {
  for c in symval(q_ear_outchanl).iter() {
    with_special(standard_output, c, () => formatfort1(lst)) |> ignore
  }
  Nil
}

///|
fn formatfort1(lst : Value) -> Value raise {
  allgentran__format1(lst, q_d_fortlinelen, fortcontline)
}

///|
fn fortcontline() -> Value raise {
  terpri()
  princ(Str("     .")) |> ignore
  forttab(num_sub(symval(q_d_fortcurrind), Fix(6L))) |> ignore
  spaces(Fix(1L))
}

///|
fn forttab(n : Value) -> Value raise {
  set(
    q_d_fortcurrind,
    num_min(num_add(n, Fix(6L)), num_sub(symval(q_d_fortlinelen), Fix(40L))),
  )
  |> ignore
  spaces(num_sub(symval(q_d_fortcurrind), posn()))
}

///|
fn formatrat(lst : Value) -> Value raise {
  for c in symval(q_ear_outchanl).iter() {
    with_special(standard_output, c, () => formatrat1(lst)) |> ignore
  }
  Nil
}

///|
fn formatrat1(lst : Value) -> Value raise {
  allgentran__format1(lst, q_d_ratlinelen, ratcontline)
}

///|
fn ratcontline() -> Value raise {
  terpri()
  rattab(symval(q_d_ratcurrind)) |> ignore
  spaces(Fix(1L))
}

///|
fn rattab(n : Value) -> Value raise {
  set(q_d_ratcurrind, num_min(n, num_sub(symval(q_d_ratlinelen), Fix(40L))))
  |> ignore
  spaces(num_sub(symval(q_d_ratcurrind), posn()))
}

///|
fn formatc(lst : Value) -> Value raise {
  for c in symval(q_ear_outchanl).iter() {
    with_special(standard_output, c, () => formatc1(lst)) |> ignore
  }
  Nil
}

///|
fn formatc1(lst : Value) -> Value raise {
  allgentran__format1(lst, q_d_clinelen, ccontline)
}

///|
fn ccontline() -> Value raise {
  terpri()
  ctab(symval(q_d_ccurrind)) |> ignore
  spaces(Fix(1L))
}

///|
fn ctab(n : Value) -> Value raise {
  set(q_d_ccurrind, num_min(n, num_sub(symval(q_d_clinelen), Fix(40L))))
  |> ignore
  spaces(num_sub(symval(q_d_ccurrind), posn()))
}

///|
/// Print arg on every current output channel.
fn pprin2(arg : Value) -> Value raise {
  if eql(arg, symval(q_ear_cr)) {
    for c in symval(q_ear_outchanl).iter() {
      terpri(stream=c)
    }
  } else {
    for c in symval(q_ear_outchanl).iter() {
      princ(arg, stream=c) |> ignore
    }
  }
  Nil
}

///|
/// Error (msgtype e) & warning message printing routine.
fn gentranerr(msgtype : Value, exp_ : Value, msg1 : Value) -> Value raise {
  if eq(msgtype, q_e) {
    if exp_.truthy() {
      d_error(list([Str("gentran:"), exp_, msg1]))
    } else {
      d_error(list([Str("gentran:"), msg1]))
    }
  } else if exp_.truthy() {
    mtell(list([Str("gentran: ~M " + lstring(msg1)), exp_]))
  } else {
    mtell(list([Str("gentran: " + lstring(msg1))]))
  }
}

// ---------------------------------------------------------------------------
// vaxlsp.l: Maxima -> Lisp translation
//
// genfloat (option variable) floats all constants; dblfloat displays all
// floats as doubles.

///|
fn safe_car(x : Value) -> Value raise {
  if listp(x) {
    car(x)
  } else {
    Nil
  }
}

///|
fn safe_caar(x : Value) -> Value raise {
  if listp(x) {
    let a = safe_car(x)
    if !listp(a) {
      // CAR of a non-list
      raise type_error(a, "list")
    }
    car(a)
  } else {
    Nil
  }
}

///|
/// Translate forms from Maxima's internal representation into Lisp.
fn franz(form : Value) -> Value raise {
  mapcar(
    f => if member(f, list2(q_d_begin_group, q_d_end_group)).truthy() {
      f
    } else if macexpp(f).truthy() {
      franzexp(f, Fix(0L), f)
    } else {
      franzstmt(f)
    },
    form,
  )
}

///|
fn allgentran__rat_context_p(context : Value) -> Bool {
  listp(context) && listp(car(context)) && equal(caar(context), q_rat)
}

///|
fn allgentran__cexp_ind() -> Value raise {
  if equal(allgentran__lang(), q_c) {
    Fix(3L)
  } else {
    Fix(1L)
  }
}

///|
fn franzexp(exp_ : Value, ind : Value, context : Value) -> Value raise {
  // flag: are all items of the expression numbers?
  set(q_allnum, t) |> ignore
  if atom(exp_) {
    if numberp(exp_) &&
      !symval(q_d_genfloat).truthy() &&
      !equal(ind, Fix(3L)) &&
      !allgentran__rat_context_p(context) {
      // integers in denominators are floated
      exp_
    } else if numberp(exp_) {
      if equal(ind, Fix(0L)) {
        set(q_expty, exptype(context)) |> ignore
        if symval(q_allnum).truthy() {
          set(q_expty, symval(q_lefttype)) |> ignore
        }
        let expty = symval(q_expty)
        if eq(expty, q_integer) {
          exp_
        } else if eq(expty, q_real) {
          lfloat(exp_)
        } else if eq(expty, q_double) {
          lfloat(exp_)
        } else if eq(expty, q_complex) {
          gcomplex(exp_)
        } else {
          lfloat(exp_)
        }
      } else if equal(ind, Fix(1L)) {
        // integers in rational powers are floated
        if allgentran__rat_context_p(context) {
          lfloat(exp_)
        } else {
          exp_
        }
      } else if equal(ind, Fix(2L)) {
        lfloat(exp_)
      } else if equal(ind, Fix(3L)) {
        lfloat(exp_)
      } else if equal(ind, Fix(4L)) {
        gcomplex(exp_)
      } else {
        Nil
      }
    } else if stringp(exp_) {
      Str("\"" + lstring(exp_) + "\"")
    } else if eq(exp_, t) {
      if eq(allgentran__lang(), q_c) {
        Fix(1L)
      } else {
        q_n_sp_dot_ct__cr__cu__ce__dot_sp
      }
    } else {
      stripdollar1(exp_)
    }
  } else if eq(caar(exp_), q_d_gquote) {
    cadr(exp_)
  } else if eq(caar(exp_), q_mtimes) {
    simptimes1(mapcar(term => franzexp(term, ind, exp_), cdr(exp_)))
  } else if eq(caar(exp_), q_mexpt) {
    // ((mexpt) x -1) --> (quotient 1.0 x)
    // ((mexpt) x ((mminus) i)) --> (quotient 1.0 (expt x i))
    // ((mexpt) $%e x) --> (exp x)
    let var_ = cadr(exp_)
    let pow = caddr(exp_)
    if eq(var_, q_d__pcte) {
      list2(q_exp, franzexp(pow, Fix(3L), context))
    } else if eql(pow, Fix(-1L)) ||
      (listp(pow) && eq(caar(pow), q_mminus) && onep(cadr(pow)).truthy()) {
      list3(
        q_quotient,
        franzexp(Fix(1L), ind, exp_),
        franzexp(var_, ind, exp_),
      )
    } else if numberp(pow) && minusp(pow) {
      list3(
        q_quotient,
        franzexp(Fix(1L), ind, exp_),
        list3(
          q_expt,
          franzexp(var_, ind, exp_),
          franzexp(num_abs(pow), allgentran__cexp_ind(), Nil),
        ),
      )
    } else if listp(pow) && eq(caar(pow), q_mminus) {
      list3(
        q_quotient,
        franzexp(Fix(1L), ind, exp_),
        list3(
          q_expt,
          franzexp(var_, ind, exp_),
          franzexp(cadr(pow), allgentran__cexp_ind(), Nil),
        ),
      )
    } else {
      // powers are double floats in C
      list3(
        q_expt,
        franzexp(cadr(exp_), ind, exp_),
        franzexp(caddr(exp_), allgentran__cexp_ind(), Nil),
      )
    }
  } else if eq(caar(exp_), q_mminus) &&
    numberp(cadr(exp_)) &&
    length(car(exp_)) == 1 &&
    numberp(cadr(exp_)) &&
    numberp(caddr(exp_)) {
    let notn = get(caar(exp_), q_franznotn)
    if notn.truthy() {
      cons(notn, mapcar(elt => franzexp(elt, ind, context), cdr(exp_)))
    } else {
      cons(
        franzexp(caar(exp_), Fix(1L), Nil),
        mapcar(elt => franzexp(elt, Fix(1L), Nil), cdr(exp_)),
      )
    }
  } else if set(q_fnotn, get(caar(exp_), q_franznotn)).truthy() {
    let fnotn = symval(q_fnotn)
    if equal(fnotn, q_plus) && equal(car(exp_), list2(q_mplus, q_simp)) {
      // the terms of a simplified sum in reverse order (as Macsyma 2.4)
      cons(fnotn, mapcar(elt => franzexp(elt, ind, exp_), reverse(cdr(exp_))))
    } else {
      cons(fnotn, mapcar(elt => franzexp(elt, ind, exp_), cdr(exp_)))
    }
  } else {
    // mark undeclared array indices for [...] in C
    if member(q_array, car(exp_)).truthy() {
      put(stripdollar1(caar(exp_)), q_array, t) |> ignore
    }
    cons(
      franzexp(caar(exp_), Fix(1L), Nil),
      mapcar(elt => franzexp(elt, Fix(1L), Nil), cdr(exp_)),
    )
  }
}

///|
fn exptype(exp_ : Value) -> Value raise {
  if null(exp_) {
    return q_integer
  }
  if atom(exp_) {
    return itemtype(exp_)
  }
  if listp(car(exp_)) && eq(q_array, cadar(exp_)) {
    return exptype(caar(exp_))
  }
  // (member (car exp) '((mplus) (mminus) (mtimes) (mquotient) (mexpt)))
  // compares with EQL, so it never holds for an operator header.
  let ty1 = exptype(car(exp_))
  let ty2 = exptype(cdr(exp_))
  if eq(ty1, q_complex) || eq(ty2, q_complex) {
    q_complex
  } else if eq(ty1, q_double) || eq(ty2, q_double) {
    q_double
  } else if eq(ty1, q_real) || eq(ty2, q_real) {
    q_real
  } else if eq(ty1, q_integer) && eq(ty2, q_integer) {
    q_integer
  } else {
    Nil
  }
}

///|
fn itemtype(item : Value) -> Value raise {
  if numberp(item) {
    if floatp(item) {
      q_real
    } else {
      q_integer
    }
  } else {
    // not all items of the expression are numbers
    set(q_allnum, Nil) |> ignore
    getvartype(stripdollar1(item))
  }
}

///|
/// A purely syntactic mechanism to display floats as doubles.
fn dfix(c : Value) -> Value raise {
  if member(c, list([Char('e'), Char('d'), Char('E'), Char('D')])).truthy() {
    Char('d')
  } else {
    c
  }
}

///|
fn double(num : Value) -> Value raise {
  if floatp(num) {
    let mut dnum = exploden(num)
    dnum = mapcar(c => dfix(c), dnum)
    if !member(Char('d'), dnum).truthy() {
      dnum = append(dnum, list2(Char('d'), Char('0')))
    }
    implode(dnum)
  } else {
    num
  }
}

///|
/// Print real numbers in Fortran complex format (syntactically).
fn gcomplex(num : Value) -> Value raise {
  if symval(q_d_usefortcomplex).truthy() && !equal(allgentran__lang(), q_c) {
    if floatp(num) {
      let cnum = append(
        exploden(num),
        list([Char(','), Char('0'), Char('.'), Char('0'), Char(')')]),
      )
      implode(cons(q_op_u0028, cnum))
    } else {
      sym(format_to_string("(~a.0,0.0)", [num]))
    }
  } else {
    lfloat(num)
  }
}

///|
fn simptimes1(terms : Value) -> Value raise {
  let mut neg = false
  let mut denoms : Value = Nil
  let one = list2(Fix(1L), Flo(1.0))
  let mut terms = mapcan(
    trm => if atom(trm) {
      if member(trm, one).truthy() {
        Nil
      } else if member(trm, list2(Fix(-1L), Flo(-1.0))).truthy() {
        neg = !neg
        Nil
      } else {
        list1(trm)
      }
    } else if eq(car(trm), q_minus) && member(cadr(trm), one).truthy() {
      neg = !neg
      Nil
    } else if eq(car(trm), q_quotient) && member(cadr(trm), one).truthy() {
      denoms = aconc(denoms, caddr(trm))
      Nil
    } else {
      list1(trm)
    },
    simptimes2(terms),
  )
  if !terms.truthy() {
    terms = list1(franzexp(Fix(1L), Fix(0L), terms))
  }
  if neg {
    terms = cons(list2(q_minus, car(terms)), cdr(terms))
  }
  terms = if onep(int(length(terms))).truthy() {
    car(terms)
  } else {
    cons(q_times, terms)
  }
  for d in denoms.iter() {
    terms = list3(q_quotient, terms, d)
  }
  terms
}

///|
fn simptimes2(terms : Value) -> Value raise {
  mapcan(
    trm => if atom(trm) {
      list1(trm)
    } else if eq(car(trm), q_times) {
      simptimes2(cdr(trm))
    } else {
      list1(trm)
    },
    terms,
  )
}

///|
/// The Lisp equivalent of a statement.
fn franzstmt(stmt : Value) -> Value raise {
  if member(safe_caar(stmt), list2(q_msetq, q_mdo)).truthy() {
    set(q_lefttype, exptype(cadr(stmt))) |> ignore
  }
  if null(stmt) {
    Nil
  } else if maclabelp(stmt).truthy() {
    franzlabel(stmt)
  } else if macstmtgpp(stmt).truthy() {
    franzstmtgp(stmt)
  } else if macdefp(stmt).truthy() {
    franzdef(stmt)
  } else if macreadp(stmt).truthy() {
    franzread(stmt)
  } else if macmatassignp(stmt).truthy() {
    franzmatassign(stmt)
  } else if macnestassignp(stmt).truthy() {
    franznestassign(stmt)
  } else if macassignp(stmt).truthy() {
    franzassign(stmt)
  } else if macifp(stmt).truthy() {
    franzif(stmt)
  } else if macforp(stmt).truthy() {
    franzfor(stmt)
  } else if macforinp(stmt).truthy() {
    franzforin(stmt)
  } else if macgop(stmt).truthy() {
    franzgo(stmt)
  } else if macretp(stmt).truthy() {
    franzret(stmt)
  } else if macprintp(stmt).truthy() {
    franzprint(stmt)
  } else if macstopp(stmt).truthy() {
    franzstop()
  } else if macendp(stmt).truthy() {
    franzend()
  } else if mac_dolliteralp(stmt).truthy() {
    franzliteral(stripdollar1(caar(stmt)), stmt)
  } else {
    // anything else is a call
    franzcall(stmt)
  }
}

///|
/// Is stmt a $literal (or $data) form?
fn mac_dolliteralp(stmt : Value) -> Value raise {
  memq(caar(stmt), list([q_d_literal, q_literal, q_d_data, q_data]))
}

///|
fn franzliteral(fn_ : Value, stmt : Value) -> Value raise {
  cons(
    fn_,
    mapcar(
      exp_ => if memq(exp_, list2(q_d_tab, q_d_cr)).truthy() {
        exp_
      } else if listp(exp_) {
        franzexp(exp_, Fix(0L), stmt)
      } else {
        stripdollar1(exp_)
      },
      cdr(stmt),
    ),
  )
}

///|
fn franzlabel(label : Value) -> Value raise {
  stripdollar1(label)
}

///|
fn franzstmtgp(stmtgp : Value) -> Value raise {
  append(list2(q_prog, Nil), mapcar(s => franzstmt(s), cdr(stmtgp)))
}

///|
/// case 1: ((msetq) id ((lambda) ((mlist) id ... id) exp))
///           -->  (defun id (id ... id) (prog () (return exp)))
/// case 2: ((mdefine) ((id) id ... id) exp)
///           -->  (defun id (id ... id) (prog () (return exp)))
/// case 3: ((mdefine) ((id) id ... id) stmtgp)
///           -->  (defun id  (id ... id) (prog () stmt ... stmt))
fn franzdef(def : Value) -> Value raise {
  if equal(caar(def), q_msetq) {
    list([
      q_defun,
      franzexp(cadr(def), Fix(0L), cadr(def)),
      mapcar(elt => franzexp(elt, Fix(0L), elt), cdadaddr(def)),
      list3(
        q_prog,
        Nil,
        list2(q_return, franzexp(caddaddr(def), Fix(0L), caddaddr(def))),
      ),
    ])
  } else if macexpp(caddr(def)).truthy() {
    list([
      q_defun,
      franzexp(caaadr(def), Fix(0L), caaadr(def)),
      mapcar(elt => franzexp(elt, Fix(0L), elt), cdadr(def)),
      list3(
        q_prog,
        Nil,
        list2(q_return, franzexp(caddr(def), Fix(0L), caddr(def))),
      ),
    ])
  } else {
    list([
      q_defun,
      franzexp(caaadr(def), Fix(0L), caaadr(def)),
      mapcar(elt => franzexp(elt, Fix(0L), elt), cdadr(def)),
      franzstmt(caddr(def)),
    ])
  }
}

///|
fn franzread(stmt : Value) -> Value raise {
  let mut varlist : Value = Nil
  let mut outlist : Value = Nil
  let mut s = stmt
  while !(null(s) || atom(s) || !macstmtp(s).truthy()) {
    if equal(caar(s), q_msetq) {
      varlist = cons(franzexp(cadr(s), Fix(0L), cadr(s)), varlist)
    } else {
      outlist = mapcar(elt => franzexp(elt, Fix(0L), elt), cdr(s))
    }
    s = caddr(s)
  }
  let mut fr : Value = Nil
  if outlist.truthy() {
    fr = append1(fr, cons(q_princ, outlist))
  }
  if varlist.truthy() {
    fr = append1(fr, list3(q_setq, car(varlist), list1(q_read)))
  }
  let mut v = varlist
  while cdr(v).truthy() {
    fr = append1(fr, list3(q_setq, cadr(v), car(v)))
    v = cdr(v)
  }
  if length(fr) > 1 {
    cons(q_progn, fr)
  } else {
    car(fr)
  }
}

///|
fn franzmatassign(stmt : Value) -> Value raise {
  // print matrix elements with [...] in C
  put(stripdollar1(cadr(stmt)), q_array, t) |> ignore
  let mut fr = list1(q_progn)
  let mut rows = cdaddr(stmt)
  let mut r = 1L
  while !null(rows) {
    let mut cols = cdar(rows)
    let mut c = 1L
    while !null(cols) {
      let elt = list3(list1(cadr(stmt)), Fix(r), Fix(c))
      fr = append1(
        fr,
        list3(
          q_setq,
          franzexp(elt, Fix(0L), list3(list1(cadr(stmt)), Fix(r), Fix(c))),
          franzexp(car(cols), Fix(0L), car(cols)),
        ),
      )
      cols = cdr(cols)
      c = c + 1L
    }
    rows = cdr(rows)
    r = r + 1L
  }
  fr
}

///|
fn franznestassign(stmt : Value) -> Value raise {
  let mut varlist : Value = Nil
  let mut s = stmt
  while !(atom(s) || !macstmtp(s).truthy()) {
    varlist = cons(franzexp(cadr(s), Fix(0L), cadr(s)), varlist)
    s = caddr(s)
  }
  let exp_ = franzexp(s, Fix(0L), s)
  let mut fr = list2(q_progn, list3(q_setq, car(varlist), exp_))
  let mut v = varlist
  while cdr(v).truthy() {
    fr = append1(fr, list3(q_setq, cadr(v), car(v)))
    v = cdr(v)
  }
  fr
}

///|
fn franzassign(stmt : Value) -> Value raise {
  list3(
    q_setq,
    franzexp(cadr(stmt), Fix(0L), cadr(stmt)),
    franzexp(caddr(stmt), Fix(0L), caddr(stmt)),
  )
}

///|
/// `(destructuring-bind (x exp stmt1 y stmt2) stmt ...)`
fn allgentran__destructure(l : Value, n : Int) -> Array[Value] raise {
  let a = list_to_array(l)
  if a.length() != n {
    raise LispError::SimpleError(
      "Error while parsing arguments to DESTRUCTURING-BIND: \{princ_to_string(l)} does not have \{n} elements",
    )
  }
  a
}

///|
fn franzif(stmt : Value) -> Value raise {
  let a = allgentran__destructure(stmt, 5)
  let exp_ = a[1]
  let stmt1 = a[2]
  let stmt2 = a[4]
  let mut fr = list1(q_cond)
  fr = append1(fr, list2(franzexp(exp_, Fix(0L), exp_), franzstmt(stmt1)))
  if !equal(stmt2, q_d_false) {
    append1(fr, list2(t, franzstmt(stmt2)))
  } else {
    fr
  }
}

///|
/// ((mdo) var lo incr nextexp hi exitcond dobody)
///   -->  (do ((var lo (plus var incr))  =or=  (var lo nextexp))
///            ((or (greaterp var hi) exitcond))
///            dobody)
fn franzfor(stmt : Value) -> Value raise {
  let a = allgentran__destructure(cdr(stmt), 7)
  set(q_oincr, a[2]) |> ignore
  set(q_onextexp, a[3]) |> ignore
  let mut var_ = franzexp(a[0], Fix(0L), a[0])
  let mut lo = franzexp(a[1], Fix(0L), a[1])
  let mut incr = franzexp(a[2], Fix(0L), a[2])
  let nextexp = franzexp(a[3], Fix(0L), a[3])
  let mut hi = franzexp(a[4], Fix(0L), a[4])
  let exitcond = franzexp(a[5], Fix(0L), a[5])
  let dobody = franzstmt(a[6])
  let mut dovars : Value = Nil
  let mut doexit : Value = Nil
  if !var_.truthy() &&
    (lo.truthy() || incr.truthy() || nextexp.truthy() || hi.truthy()) {
    set(q_tvname, symval(q_d_tempvarname)) |> ignore
    set(q_d_tempvarname, q_i) |> ignore
    var_ = d_tempvar(Nil)
    set(q_d_tempvarname, symval(q_tvname)) |> ignore
  }
  if !lo.truthy() && (var_.truthy() || incr.truthy() || hi.truthy()) {
    lo = Fix(1L)
  }
  if !incr.truthy() &&
    !nextexp.truthy() &&
    (var_.truthy() || lo.truthy() || hi.truthy()) {
    incr = Fix(1L)
  }
  if incr.truthy() {
    if null(getvartype(var_)) || inttypep(getvartype(var_)).truthy() {
      if numberp(lo) {
        lo = floor1(lo)
      }
      if numberp(hi) {
        hi = floor1(hi)
      }
      if numberp(incr) {
        incr = floor1(incr)
      }
    }
    dovars = list1(list3(var_, lo, list3(q_plus, var_, incr)))
  }
  if nextexp.truthy() {
    dovars = list1(list3(var_, lo, nextexp))
  }
  if hi.truthy() {
    let posincr = if nextexp.truthy() {
      noerrmevalp(list3(list1(q_mgeqp), q_onextexp, Fix(0L)))
    } else {
      noerrmevalp(list3(list1(q_mgeqp), q_oincr, Fix(0L)))
    }
    if posincr.truthy() {
      doexit = list1(list3(q_greaterp, var_, hi))
    } else {
      doexit = list1(list3(q_lessp, var_, hi))
    }
  }
  if exitcond.truthy() {
    doexit = append1(doexit, exitcond)
  }
  if length(doexit) > 1 {
    doexit = list1(cons(q_or, doexit))
  }
  list([q_do, dovars, doexit, dobody])
}

///|
/// ((mdoin) dovar dolist nil nil nil doexitcond dobody)
///   -->  (do ((genvar 1 (+ genvar 1)))
///            ((> genvar listlength))
///            (cond ((equal genvar 1) (setq dovar list(1)))
///                    ...
///                  ((equal genvar listlength) (setq dovar list(length))))
///            (cond ((doexitcond) (break)))
///            dobody)
fn franzforin(stmt : Value) -> Value raise {
  let a = allgentran__destructure(cdr(stmt), 7)
  let dolist = cdr(a[1])
  let doexitcond = a[5]
  let dobody = a[6]
  set(q_tvname, symval(q_d_tempvarname)) |> ignore
  set(q_d_tempvarname, q_i) |> ignore
  let gvar = d_tempvar(Nil)
  set(q_d_tempvarname, symval(q_tvname)) |> ignore
  let dovar = franzexp(a[0], Fix(0L), a[0])
  let mut condbody : Value = Nil
  let n = length(dolist)
  for i = 1; i <= n; i = i + 1 {
    let e = nthelem(int(i), dolist)
    condbody = append(
      condbody,
      list1(
        list2(
          list3(q_equal, gvar, int(i)),
          list3(q_setq, dovar, franzexp(e, Fix(0L), nthelem(int(i), dolist))),
        ),
      ),
    )
  }
  let dovars = list1(
    list3(gvar, Fix(1L), list3(q_op_plus, gvar, Fix(1L))),
  )
  let doexit = list1(list3(q_op_gt, gvar, int(n)))
  if doexitcond.truthy() {
    list([
      q_do,
      dovars,
      doexit,
      list([
        q_progn,
        cons(q_cond, condbody),
        list2(
          q_cond,
          list2(franzexp(doexitcond, Fix(0L), doexitcond), list1(q_break)),
        ),
        franz(dobody),
      ]),
    ])
  } else {
    list([
      q_do,
      dovars,
      doexit,
      list3(q_progn, cons(q_cond, condbody), franz(dobody)),
    ])
  }
}

///|
fn franzgo(stmt : Value) -> Value raise {
  list2(q_go, franzlabel(cadr(stmt)))
}

///|
fn franzret(stmt : Value) -> Value raise {
  if cdr(stmt).truthy() {
    list2(q_return, franzexp(cadr(stmt), Fix(0L), cadr(stmt)))
  } else {
    list1(q_return)
  }
}

///|
fn franzprint(stmt : Value) -> Value raise {
  cons(q_princ, mapcar(elt => franzexp(elt, Fix(0L), elt), cdr(stmt)))
}

///|
fn franzstop() -> Value raise {
  list1(q_stop)
}

///|
fn franzend() -> Value raise {
  list1(q_end)
}

///|
fn franzcall(exp_ : Value) -> Value raise {
  if cdr(exp_).truthy() {
    cons(
      franzexp(caar(exp_), Fix(0L), caar(exp_)),
      mapcar(elt => franzexp(elt, Fix(0L), elt), cdr(exp_)),
    )
  } else {
    list1(franzexp(caar(exp_), Fix(0L), caar(exp_)))
  }
}

///|
/// Is exp an arithmetic or logical Maxima expression?
fn macexpp(exp_ : Value) -> Value raise {
  if null(exp_) {
    Nil
  } else if atom(exp_) {
    t
  } else if atom(car(exp_)) {
    Nil
  } else {
    lbool(
      !memq(
        caar(exp_),
        list([
          q_mcond,
          q_mdefine,
          q_mdo,
          q_mdoin,
          q_mgo,
          q_mprog,
          q_mprogn,
          q_mreturn,
          q_msetq,
          q_d_end,
          q_d_ev,
          q_d_literal,
          q_d_print,
          q_d_readonly,
          q_d_stop,
          q_d_data,
        ]),
      ).truthy(),
    )
  }
}

///|
/// Is exp a Maxima logical expression?
fn maclogexpp(exp_ : Value) -> Value raise {
  if atom(exp_) {
    lbool(!numberp(exp_))
  } else if listp(car(exp_)) {
    lbool(
      !memq(
        caar(exp_),
        list([
          q_mcond,
          q_mdefine,
          q_mdo,
          q_mdoin,
          q_mgo,
          q_mexpt,
          q_mminus,
          q_mplus,
          q_mprog,
          q_mprogn,
          q_mquotient,
          q_mreturn,
          q_msetq,
          q_mtimes,
          q_rat,
          q_d_end,
          q_d_ev,
          q_d_print,
          q_d_readonly,
          q_d_stop,
        ]),
      ).truthy(),
    )
  } else {
    Nil
  }
}

///|
/// Is stmt a Maxima statement?
fn macstmtp(stmt : Value) -> Value raise {
  if null(stmt) {
    Nil
  } else if atom(stmt) {
    t
  } else if atom(car(stmt)) {
    Nil
  } else if member(
      caar(stmt),
      list([
        q_mcond,
        q_mdo,
        q_mdoin,
        q_mgo,
        q_mreturn,
        q_msetq,
        q_d_end,
        q_d_print,
        q_d_readonly,
        q_d_stop,
      ]),
    ).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// Is stmt a Maxima statement group?
fn macstmtgpp(stmt : Value) -> Value raise {
  if null(stmt) || atom(stmt) || atom(car(stmt)) {
    Nil
  } else if member(caar(stmt), list([q_mprog, q_mprogn, q_d_ev])).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// Is stmt a Maxima function or procedure definition?
fn macdefp(stmt : Value) -> Value raise {
  if null(stmt) || atom(stmt) || atom(car(stmt)) {
    Nil
  } else {
    lbool(
      equal(caar(stmt), q_mdefine) ||
      (equal(caar(stmt), q_msetq) &&
      listp(caddr(stmt)) &&
      listp(car(caddr(stmt))) &&
      equal(caaaddr(stmt), q_lambda)),
    )
  }
}

///|
fn macassignp(stmt : Value) -> Value raise {
  lbool(equal(safe_caar(stmt), q_msetq))
}

///|
fn macnestassignp(stmt : Value) -> Value raise {
  lbool(
    macassignp(stmt).truthy() &&
    listp(caddr(stmt)) &&
    listp(car(caddr(stmt))) &&
    macassignp(caddr(stmt)).truthy(),
  )
}

///|
fn macmatassignp(stmt : Value) -> Value raise {
  if null(stmt) || atom(stmt) || atom(car(stmt)) {
    Nil
  } else if equal(caar(stmt), q_d_matrix) {
    t
  } else if equal(caar(stmt), q_msetq) {
    macmatassignp(caddr(stmt))
  } else {
    Nil
  }
}

///|
fn macifp(stmt : Value) -> Value raise {
  lbool(equal(safe_caar(stmt), q_mcond))
}

///|
fn macforp(stmt : Value) -> Value raise {
  lbool(equal(safe_caar(stmt), q_mdo))
}

///|
fn macforinp(stmt : Value) -> Value raise {
  lbool(equal(safe_caar(stmt), q_mdoin))
}

///|
fn macgop(stmt : Value) -> Value raise {
  lbool(equal(safe_caar(stmt), q_mgo))
}

///|
fn maclabelp(stmt : Value) -> Value raise {
  lbool(atom(stmt))
}

///|
fn macretp(stmt : Value) -> Value raise {
  lbool(equal(safe_caar(stmt), q_mreturn))
}

///|
fn macreadp(stmt : Value) -> Value raise {
  if null(stmt) || atom(stmt) || atom(car(stmt)) {
    Nil
  } else if equal(safe_caar(stmt), q_d_readonly) {
    t
  } else if equal(safe_caar(stmt), q_msetq) {
    macreadp(caddr(stmt))
  } else {
    Nil
  }
}

///|
fn macprintp(stmt : Value) -> Value raise {
  lbool(equal(safe_caar(stmt), q_d_print))
}

///|
fn macstopp(stmt : Value) -> Value raise {
  lbool(equal(safe_caar(stmt), q_d_stop))
}

///|
fn macendp(stmt : Value) -> Value raise {
  lbool(equal(safe_caar(stmt), q_d_end))
}
