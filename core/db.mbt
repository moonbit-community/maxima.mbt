// Port of src/db.lisp: the fact database underlying assume/is/declare.
//
// Representation (as in the Lisp, via mrgmac's ATOM modes): every "selector"
// (+labs, -labs, data, ulabs, con, cmark, subc ...) is a property. Symbols are
// their own nodes and keep properties on their plist; numbers and compound
// expressions are one-element cells `(x . plist)` whose CDR is the property
// list (ZL-GET / PUTPROP_ / ZL-REMPROP handle both). A datum is a cell
// `((r a b) . plist)`. Labels are cells `(fixnum)` mutated in place.
//
// `(sel x prop)` is `zl_get(x, q_prop)`; `(push+sto (sel x prop) v)` is
// `cput(x, v, q_prop)`.

///|
fn db__high_bit() -> Value {
  symval(q_n_pluslab_high_bit_plus)
}

///|
/// `(delete x l :test #'eq :count 1)`, non-destructively.
fn db__delete1_eq(x : Value, l : Value) -> Value {
  let c = Collector::new()
  let mut p = l
  while p is Cons(cell) {
    if eq(cell.car, x) {
      c.append_list(cell.cdr)
      return c.result()
    }
    c.add(cell.car)
    p = cell.cdr
  }
  c.result()
}

///|
/// `(subp a b)`: every bit of (unlab a) is set in (unlab b).
fn db__subp2(a : Value, b : Value) -> Bool raise {
  let x = car(a)
  num_eq(x, logand(x, car(b)))
}

// --- macros -----------------------------------------------------------------

///|
fn unlab(cell : Value) -> Value raise {
  car(cell)
}

///|
fn copyn(n : Value) -> Value raise {
  list1(n)
}

///|
fn iorm(cell : Value, n : Value) -> Value raise {
  rplaca(cell, logior(car(cell), car(n)))
}

///|
fn xorm(cell : Value, n : Value) -> Value raise {
  rplaca(cell, logxor(car(cell), car(n)))
}

///|
fn n_pluslabz(x : Value) -> Value raise {
  let v = zl_get(x, q_n_pluslabs)
  if v.truthy() {
    v
  } else {
    list1(Fix(0L))
  }
}

///|
fn n_labz(x : Value) -> Value raise {
  let v = zl_get(x, q_n_labs)
  if v.truthy() {
    v
  } else {
    list1(Fix(0L))
  }
}

///|
fn n_eqlabz(x : Value) -> Value raise {
  let v = zl_get(x, q_n_eqlabs)
  if v.truthy() {
    v
  } else {
    list1(Fix(0L))
  }
}

///|
fn nlabz(x : Value) -> Value raise {
  let v = zl_get(x, q_nlabs)
  if v.truthy() {
    v
  } else {
    list1(Fix(0L))
  }
}

///|
fn ulabz(x : Value) -> Value raise {
  let v = zl_get(x, q_ulabs)
  if v.truthy() {
    v
  } else {
    list1(Fix(0L))
  }
}

///|
/// `(subp c1 c2 ...)`: `(= (unlab c1) (logand (unlab c1) (unlab c2) ...))`.
fn subp(x : Value) -> Value raise {
  let first = car(x)
  let mut acc = car(first)
  for c in cdr(x).iter() {
    acc = logand(acc, car(c))
  }
  lbool(num_eq(car(first), acc))
}

// --- marks ------------------------------------------------------------------

///|
fn mark(x : Value) -> Value raise {
  putprop_(x, t, q_mark)
}

///|
fn markp(x : Value) -> Value raise {
  if symbolp(x) {
    get(x, q_mark)
  } else {
    Nil
  }
}

///|
fn unmrk(x : Value) -> Value raise {
  zl_remprop(x, q_mark)
}

///|
fn marks(x : Value) -> Value raise {
  if numberp(x) {
    t
  } else if atom(x) {
    mark(x)
  } else {
    mapc(y => marks(y) |> ignore, x)
  }
}

///|
fn unmrks(x : Value) -> Value raise {
  if numberp(x) {
    t
  } else if atom(x) || numberp(car(x)) {
    unmrk(x)
  } else {
    mapc(y => unmrks(y) |> ignore, x)
  }
}

// --- nodes ------------------------------------------------------------------

///|
fn dbnode(x : Value) -> Value raise {
  if symbolp(x) {
    x
  } else {
    list1(x)
  }
}

///|
fn nodep(x : Value) -> Value raise {
  if atom(x) {
    t
  } else {
    mnump(car(x))
  }
}

///|
fn dbvarp(x : Value) -> Value raise {
  getl(x, list2(q_un, q_ex))
}

///|
/// Is ND a node cell standing for a number?
fn dnump(nd : Value) -> Value raise {
  if consp(nd) {
    mnump(car(nd))
  } else {
    Nil
  }
}

///|
fn lab(n : Value) -> Value raise {
  ash(Fix(1L), to_int(n) - 1)
}

///|
fn lpr(m : Value, n : Value) -> Value raise {
  let mut l = symval(q_ear_lprs)
  while l is Cons(c) {
    if labeq(m, caaar(l)).truthy() && labeq(n, cdaar(l)).truthy() {
      let r = cdar(l)
      if r.truthy() {
        return r
      }
      break
    }
    l = c.cdr
  }
  let idx = num_sub(symval(q_ear_lprindex), Fix(1L))
  set(q_ear_lprindex, idx) |> ignore
  if num_eq(idx, symval(q_ear_labindex)) {
    lisp_error("break: database label space exhausted (LPR)")
  } else {
    push_special(cons(cons(m, n), ash(Fix(1L), to_int(idx))), q_ear_lprs)
    |> ignore
    cdar(symval(q_ear_lprs))
  }
}

///|
fn labeq(x : Value, y : Value) -> Value raise {
  let h = db__high_bit()
  lbool(num_eq(logior(x, h), logior(y, h)))
}

///|
fn marknd(nd : Value) -> Value raise {
  let v = zl_get(nd, q_n_pluslabs)
  if v.truthy() {
    return v
  }
  let idx = num_add(symval(q_ear_labindex), Fix(1L))
  set(q_ear_labindex, idx) |> ignore
  if num_eq(symval(q_ear_lprindex), idx) {
    lisp_error("break: database label space exhausted (MARKND)")
  } else {
    push_special(cons(nd, lab(idx)), q_ear_labs) |> ignore
    beg(nd, lab(idx)) |> ignore
    cdar(symval(q_ear_labs))
  }
}

///|
fn dbv(x : Value, r : Value) -> Value raise {
  let mut y : Value = Fix(0L)
  for e in symval(q_ear_lprs).iter() {
    if !(zerop(logand(r, cdr(e))) || zerop(logand(x, caar(e)))) {
      y = logior(cdar(e), y)
    }
  }
  y
}

///|
fn dba(r : Value, y : Value) -> Value raise {
  let mut x : Value = Fix(0L)
  for e in symval(q_ear_lprs).iter() {
    if !(zerop(logand(r, cdr(e))) || zerop(logand(cdar(e), y))) {
      x = logior(x, caar(e))
    }
  }
  x
}

///|
fn prlab(x : Value) -> Value raise {
  let x = unlab(x)
  if x.truthy() {
    format(t, " ~,,' ,3:B", [logand(lognot(db__high_bit()), x)])
  } else {
    Nil
  }
}

///|
fn onp(cl : Value, lab : Value) -> Value raise {
  lbool(db__subp2(lab, n_pluslabz(cl)))
}

///|
fn offp(cl : Value, lab : Value) -> Value raise {
  lbool(db__subp2(lab, n_labz(cl)))
}

///|
fn onpu(lab : Value, fact : Value) -> Value raise {
  lbool(db__subp2(lab, ulabz(fact)))
}

///|
fn visiblep(dat : Value) -> Value raise {
  if zl_get(dat, q_ulabs).truthy() {
    Nil
  } else {
    cntp(dat)
  }
}

///|
fn cancel(lab : Value, dat : Value) -> Value raise {
  let db = set(q_ear_db, zl_get(dat, q_ulabs))
  if db.truthy() {
    iorm(db, lab)
  } else {
    push_special(dat, q_ulabs) |> ignore
    let lab = unlab(lab)
    putprop_(dat, copyn(lab), q_ulabs)
  }
}

///|
fn queue_plusp(nd : Value, lab : Value) -> Value raise {
  let db = set(q_ear_db, zl_get(nd, q_n_pluslabs))
  if atom(db) {
    // No label, or a stale sign symbol left by DMARK: Start fresh.
    push_special(nd, q_n_pluslabs) |> ignore
    let lab = unlab(lab)
    putprop_(nd, copyn(logior(db__high_bit(), lab)), q_n_pluslabs)
  } else if db__subp2(lab, db) {
    Nil
  } else if db__subp2(symval(q_ear_lab_high_lab), db) {
    iorm(db, lab) |> ignore
    Nil
  } else {
    iorm(db, copyn(logior(db__high_bit(), unlab(lab))))
  }
}

///|
fn beg(nd : Value, lab : Value) -> Value raise {
  let lab = copyn(lab)
  if queue_plusp(nd, lab).truthy() {
    if symval(q_n_pluss) is Nil {
      let s = set(q_n_pluss, list1(nd))
      set(q_n_plussm, s) |> ignore
      set(q_n_plussl, s)
    } else {
      push_special(nd, q_n_pluss)
    }
  } else {
    Nil
  }
}

///|
fn queue_p(nd : Value, lab : Value) -> Value raise {
  let db = set(q_ear_db, zl_get(nd, q_n_labs))
  if db is Nil {
    push_special(nd, q_n_labs) |> ignore
    let lab = unlab(lab)
    putprop_(nd, copyn(logior(db__high_bit(), lab)), q_n_labs)
  } else if db__subp2(lab, db) {
    Nil
  } else if db__subp2(symval(q_ear_lab_high_lab), db) {
    iorm(db, lab) |> ignore
    Nil
  } else {
    iorm(db, copyn(logior(db__high_bit(), unlab(lab))))
  }
}

///|
fn beg_(nd : Value, lab : Value) -> Value raise {
  let lab = copyn(lab)
  if queue_p(nd, lab).truthy() {
    if symval(q_n_s) is Nil {
      let s = set(q_n_s, list1(nd))
      set(q_n_sm, s) |> ignore
      set(q_n_sl, s)
    } else {
      set(q_n_s, cons(nd, symval(q_n_s)))
    }
  } else {
    Nil
  }
}

///|
fn mid(nd : Value, lab : Value) -> Value raise {
  if queue_plusp(nd, lab).truthy() {
    if symval(q_n_plussm) is Nil {
      let s = set(q_n_pluss, list1(nd))
      set(q_n_plussm, s) |> ignore
      set(q_n_plussl, s)
    } else {
      let sm = symval(q_n_plussm)
      rplacd(sm, cons(nd, cdr(sm))) |> ignore
      if eq(sm, symval(q_n_plussl)) {
        set(q_n_plussl, cdr(symval(q_n_plussl))) |> ignore
      }
      set(q_n_plussm, cdr(sm))
    }
  } else {
    Nil
  }
}

///|
fn mid_(nd : Value, lab : Value) -> Value raise {
  if queue_p(nd, lab).truthy() {
    if symval(q_n_sm) is Nil {
      let s = set(q_n_s, list1(nd))
      set(q_n_sm, s) |> ignore
      set(q_n_sl, s)
    } else {
      let sm = symval(q_n_sm)
      rplacd(sm, cons(nd, cdr(sm))) |> ignore
      if eq(sm, symval(q_n_sl)) {
        set(q_n_sl, cdr(symval(q_n_sl))) |> ignore
      }
      set(q_n_sm, cdr(sm))
    }
  } else {
    Nil
  }
}

///|
fn end(nd : Value, lab : Value) -> Value raise {
  if queue_plusp(nd, lab).truthy() {
    if symval(q_n_plussl) is Nil {
      let s = set(q_n_pluss, list1(nd))
      set(q_n_plussm, s) |> ignore
      set(q_n_plussl, s)
    } else {
      let sl = symval(q_n_plussl)
      rplacd(sl, list1(nd)) |> ignore
      set(q_n_plussl, cdr(sl))
    }
  } else {
    Nil
  }
}

///|
fn end_(nd : Value, lab : Value) -> Value raise {
  if queue_p(nd, lab).truthy() {
    if symval(q_n_sl) is Nil {
      let s = set(q_n_s, list1(nd))
      set(q_n_sm, s) |> ignore
      set(q_n_sl, s)
    } else {
      let sl = symval(q_n_sl)
      rplacd(sl, list1(nd)) |> ignore
      set(q_n_sl, cdr(sl))
    }
  } else {
    Nil
  }
}

///|
fn dq_plus() -> Value raise {
  let s = symval(q_n_pluss)
  if s is Nil {
    return Nil
  }
  xorm(zl_get(car(s), q_n_pluslabs), symval(q_ear_lab_high_lab)) |> ignore
  let r = car(s)
  if !eq(s, symval(q_n_plussm)) {
    set(q_n_pluss, cdr(s)) |> ignore
  } else if !eq(s, symval(q_n_plussl)) {
    let s2 = set(q_n_pluss, cdr(s))
    set(q_n_plussm, s2) |> ignore
  } else {
    set(q_n_pluss, Nil) |> ignore
    set(q_n_plussm, Nil) |> ignore
    set(q_n_plussl, Nil) |> ignore
  }
  r
}

///|
fn dq_() -> Value raise {
  let s = symval(q_n_s)
  if s is Nil {
    return Nil
  }
  xorm(zl_get(car(s), q_n_labs), symval(q_ear_lab_high_lab)) |> ignore
  let r = car(s)
  if !eq(s, symval(q_n_sm)) {
    set(q_n_s, cdr(s)) |> ignore
  } else if !eq(s, symval(q_n_sl)) {
    let s2 = set(q_n_s, cdr(s))
    set(q_n_sm, s2) |> ignore
  } else {
    set(q_n_s, Nil) |> ignore
    set(q_n_sm, Nil) |> ignore
    set(q_n_sl, Nil) |> ignore
  }
  r
}

///|
fn clear() -> Value raise {
  if symval(q_dbtrace).truthy() {
    format(t, "~%CLEAR: clearing ~A", [symval(q_ear_marks)]) |> ignore
  }
  mapc(s => cput(s, Nil, q_n_pluslabs) |> ignore, symval(q_n_pluslabs))
  |> ignore
  mapc(s => cput(s, Nil, q_n_labs) |> ignore, symval(q_n_labs)) |> ignore
  mapc(s => zl_remprop(s, q_ulabs) |> ignore, symval(q_ulabs)) |> ignore
  set(q_n_pluss, Nil) |> ignore
  set(q_n_plussm, Nil) |> ignore
  set(q_n_plussl, Nil) |> ignore
  set(q_n_s, Nil) |> ignore
  set(q_n_sm, Nil) |> ignore
  set(q_n_sl, Nil) |> ignore
  set(q_ear_labs, Nil) |> ignore
  set(q_ear_lprs, Nil) |> ignore
  set(q_ear_labindex, Fix(0L)) |> ignore
  set(q_ear_lprindex, symval(q_n_pluslabnumber_plus)) |> ignore
  set(q_ear_marks, Fix(0L)) |> ignore
  set(q_n_pluslabs, Nil) |> ignore
  set(q_n_labs, Nil) |> ignore
  set(q_ulabs, Nil) |> ignore
  contextmark()
}

///|
fn truep(pat : Value) -> Value raise {
  clear() |> ignore
  if atom(pat) {
    return pat
  }
  let pat = mapcar(p => query_semant(p), pat)
  if eq(car(pat), q_kind) {
    beg(cadr(pat), Fix(1L)) |> ignore
    beg_(caddr(pat), Fix(1L)) |> ignore
    propg()
  } else {
    beg(cadr(pat), Fix(1L)) |> ignore
    beg_(caddr(pat), Fix(2L)) |> ignore
    beg(car(pat), lpr(Fix(1L), Fix(2L))) |> ignore
    propg()
  }
}

///|
fn falsep(pat : Value) -> Value raise {
  clear() |> ignore
  if eq(car(pat), q_kind) {
    beg(cadr(pat), Fix(1L)) |> ignore
    beg(caddr(pat), Fix(1L)) |> ignore
    propg()
  } else {
    Nil
  }
}

///|
fn isp(pat : Value) -> Value raise {
  let r = errset(fn() {
    let v = truep(pat)
    if v.truthy() {
      v
    } else if falsep(pat).truthy() {
      Nil
    } else {
      q_unknown
    }
  })
  match r {
    Some(v) => v
    None => q_unknown
  }
}

///|
/// Return NIL for all non-symbols.
fn kindp(x : Value, y : Value) -> Value raise {
  if symbolp(x) && get(x, q_data).truthy() {
    clear() |> ignore
    beg(x, Fix(1L)) |> ignore
    while symval(q_n_pluss).truthy() {
      let p = dq_plus()
      if eq(y, p) {
        return t
      }
      mark_plus(p, zl_get(p, q_n_pluslabs)) |> ignore
    }
    Nil
  } else {
    Nil
  }
}

///|
/// The first kind of the symbol X that is a member of KINDS (which should be
/// mutually exclusive), or NIL. One database query.
fn kind_any_of(x : Value, kinds : Value) -> Value raise {
  if symbolp(x) && get(x, q_data).truthy() {
    clear() |> ignore
    beg(x, Fix(1L)) |> ignore
    while symval(q_n_pluss).truthy() {
      let p = dq_plus()
      let k = memq(p, kinds)
      if k.truthy() {
        return car(k)
      }
      mark_plus(p, zl_get(p, q_n_pluslabs)) |> ignore
    }
    Nil
  } else {
    Nil
  }
}

///|
/// T iff (KINDP X K) would hold for all K in KINDS (no repeated items).
fn kind_all_of_p(x : Value, kinds : Value) -> Value raise {
  let mut remaining = length(kinds)
  if symbolp(x) && get(x, q_data).truthy() {
    clear() |> ignore
    beg(x, Fix(1L)) |> ignore
    while symval(q_n_pluss).truthy() {
      let p = dq_plus()
      if memq(p, kinds).truthy() {
        remaining -= 1
        if remaining == 0 {
          break
        }
      }
      mark_plus(p, zl_get(p, q_n_pluslabs)) |> ignore
    }
  }
  lbool(remaining == 0)
}

///|
/// '$IMAGINARY if the symbol X is declared imaginary, '$COMPLEX if declared
/// complex but not imaginary, else NIL.
fn decl_complex_kind(x : Value) -> Value raise {
  if symbolp(x) && get(x, q_data).truthy() {
    clear() |> ignore
    beg(x, Fix(1L)) |> ignore
    let mut complexp = false
    while symval(q_n_pluss).truthy() {
      let p = dq_plus()
      if eq(p, q_d_imaginary) {
        return q_d_imaginary
      }
      if eq(p, q_d_complex) {
        complexp = true
      }
      mark_plus(p, zl_get(p, q_n_pluslabs)) |> ignore
    }
    if complexp {
      q_d_complex
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn true_star(pat : Value) -> Value raise {
  if eq(car(pat), q_kind) {
    mkind(cadr(pat), caddr(pat))
  } else {
    let dum = semant(pat)
    if dum.truthy() {
      cntxt(ind(list1(dum)), symval(q_context))
    } else {
      Nil
    }
  }
}

///|
fn fact(fun : Value, arg : Value, val : Value) -> Value raise {
  cntxt(ind(datum(list3(fun, arg, val))), symval(q_context))
}

///|
fn kind(x : Value, y : Value) -> Value raise {
  let y = datum(list3(q_kind, x, y))
  cntxt(y, symval(q_context)) |> ignore
  addf(y, x)
}

///|
fn par(s : Value, y : Value) -> Value raise {
  let y = datum(list3(q_par, s, y))
  cntxt(y, symval(q_context)) |> ignore
  mapc(lis => addf(y, lis) |> ignore, s)
}

///|
fn datum(pat : Value) -> Value raise {
  list1(pat)
}

///|
fn ind(dat : Value) -> Value raise {
  mapc(lis => ind1(dat, lis) |> ignore, cdar(dat)) |> ignore
  mapc(nd => ind2(nd) |> ignore, cdar(dat)) |> ignore
  dat
}

///|
fn ind1(dat : Value, pat : Value) -> Value raise {
  if !nodep(pat).truthy() {
    mapc(lis => ind1(dat, lis) |> ignore, pat)
  } else if markp(pat).truthy() || eq(q_unknown, pat) {
    t
  } else {
    addf(dat, pat) |> ignore
    mark(pat)
  }
}

///|
fn ind2(nd : Value) -> Value raise {
  if nodep(nd).truthy() {
    unmrk(nd)
  } else {
    mapc(x => ind2(x) |> ignore, nd)
  }
}

///|
fn addf(dat : Value, nd : Value) -> Value raise {
  cput(nd, cons(dat, zl_get(nd, q_data)), q_data)
}

///|
fn maxima_remf(dat : Value, nd : Value) -> Value raise {
  cput(nd, fdel(dat, zl_get(nd, q_data)), q_data)
}

///|
fn uncntxt(dat : Value) -> Value raise {
  let c = zl_get(dat, q_con)
  let ctxt = if c.truthy() { c } else { q_global }
  let l = zl_get(ctxt, q_data)
  if l.truthy() {
    putprop_(ctxt, db__delete1_eq(dat, l), q_data) |> ignore
  }
  dat
}

///|
/// Can the datum DAT be removed from the current context? A datum with no CON
/// is one of DINTNUM's chain edges; one owned by $GLOBAL can only be removed
/// from within $GLOBAL itself.
fn removablep(dat : Value) -> Value raise {
  let con = zl_get(dat, q_con)
  if con is Nil {
    Nil
  } else if !eq(con, q_d_global) {
    t
  } else if eq(symval(q_context), q_d_global) {
    t
  } else {
    set(q_ear_fact_protected, t) |> ignore
    Nil
  }
}

///|
fn fdel(fact : Value, data : Value) -> Value raise {
  if eq(car(fact), caaar(data)) &&
    eq(cadr(fact), cadr(caar(data))) &&
    eq(caddr(fact), caddar(car(data))) &&
    removablep(car(data)).truthy() {
    let rest = cdr(data)
    uncntxt(car(data)) |> ignore
    set(q_ear_fact_removed, t) |> ignore
    rest
  } else {
    let mut ds = data
    while cdr(ds).truthy() {
      let dat = cadr(ds)
      if eq(car(fact), caar(dat)) &&
        eq(cadr(fact), cadar(dat)) &&
        eq(caddr(fact), caddar(dat)) &&
        removablep(dat).truthy() {
        rplacd(ds, cddr(ds)) |> ignore
        uncntxt(dat) |> ignore
        set(q_ear_fact_removed, t) |> ignore
        break
      }
      ds = cdr(ds)
    }
    data
  }
}

///|
fn semantics(pat : Value) -> Value raise {
  if atom(pat) {
    pat
  } else {
    list1(semant(pat))
  }
}

///|
fn db_mnump(x : Value) -> Value raise {
  lbool(
    numberp(x) ||
    (!atom(x) &&
    !atom(car(x)) &&
    (eq(caar(x), q_rat) || eq(caar(x), q_bigfloat))),
  )
}

///|
fn semant(pat : Value) -> Value raise {
  if symbolp(pat) {
    let v = get(pat, q_var)
    if v.truthy() {
      v
    } else {
      pat
    }
  } else if db_mnump(pat).truthy() {
    dintnum(pat)
  } else {
    mapcar(p => semant(p), pat)
  }
}

///|
fn query_semant(pat : Value) -> Value raise {
  if symbolp(pat) {
    let v = get(pat, q_var)
    if v.truthy() {
      v
    } else {
      pat
    }
  } else if db_mnump(pat).truthy() {
    let v = dinternp(pat)
    if v.truthy() {
      v
    } else {
      dbnode(pat)
    }
  } else {
    mapcar(p => query_semant(p), pat)
  }
}

///|
/// The database node for X, or NIL when the database has none.
fn dinternp(x : Value) -> Value raise {
  if mnump(x).truthy() {
    assol(x, symval(q_ear_nobjects))
  } else if atom(x) {
    x
  } else {
    assol(x, symval(q_dobjects))
  }
}

///|
fn dintern(x : Value) -> Value raise {
  if mnump(x).truthy() {
    dintnum(x)
  } else if atom(x) {
    x
  } else {
    let v = assol(x, symval(q_dobjects))
    if v.truthy() {
      v
    } else {
      set(q_dobjects, cons(dbnode(x), symval(q_dobjects))) |> ignore
      car(symval(q_dobjects))
    }
  }
}

///|
/// Where the number X belongs in the *NOBJECTS* chain, without putting it
/// there: the node X equals, if any; otherwise the nearest nodes above and
/// below X (either NIL when that side is empty).
fn dnum_neighbors(x : Value) -> (Value, Value, Value) raise {
  let mut above : Value = Nil
  let mut lis = symval(q_ear_nobjects)
  while lis is Cons(c) {
    let r = rgrp(x, caar(lis))
    if eq(q_d_zero, r) {
      return (car(lis), Nil, Nil)
    } else if eq(q_d_pos, r) {
      return (Nil, above, car(lis))
    } else {
      above = car(lis)
    }
    lis = c.cdr
  }
  (Nil, above, Nil)
}

///|
fn db__unlink_edge_below(node : Value) -> Unit raise {
  for d in zl_get(node, q_data).iter() {
    let p = car(d)
    if eq(q_mgrp, car(p)) && eq(node, cadr(p)) && zl_get(d, q_con) is Nil {
      remov(d) |> ignore
      putprop_(q_global, db__delete1_eq(d, get(q_global, q_data)), q_data)
      |> ignore
      return
    }
  }
}

///|
fn dintnum(x : Value) -> Value raise {
  let found = assol(x, symval(q_ear_nobjects))
  if found.truthy() {
    return found
  }
  let x = dbnode(x)
  let nobj = symval(q_ear_nobjects)
  if nobj is Nil {
    set(q_ear_nobjects, list1(x)) |> ignore
    return x
  }
  let foo = rgrp(car(x), caar(nobj))
  if eq(q_d_zero, foo) {
    with_special(q_context, q_global, () => fact(q_meqp, x, car(nobj)))
    |> ignore
    push_special(x, q_ear_nobjects) |> ignore
    return x
  }
  if eq(q_d_pos, foo) {
    with_special(q_context, q_global, () => fact(q_mgrp, x, car(nobj)))
    |> ignore
    push_special(x, q_ear_nobjects) |> ignore
    return x
  }
  with_special(q_context, q_d_global, fn() {
    let mut lis = symval(q_ear_nobjects)
    while true {
      if cdr(lis) is Nil {
        with_special(q_context, q_global, () => fact(q_mgrp, car(lis), x))
        |> ignore
        rplacd(lis, list1(x)) |> ignore
        return x
      }
      let foo = rgrp(car(x), caadr(lis))
      if eq(q_d_zero, foo) {
        with_special(q_context, q_global, () => fact(q_meqp, cadr(lis), x))
        |> ignore
        rplacd(lis, cons(x, cdr(lis))) |> ignore
        return x
      } else if eq(q_d_pos, foo) {
        // X goes strictly between (CAR LIS) and (CADR LIS). Drop the edge
        // leaving (CAR LIS) so that the number nodes stay a chain.
        db__unlink_edge_below(car(lis))
        with_special(q_context, q_global, fn() {
          fact(q_mgrp, car(lis), x) |> ignore
          fact(q_mgrp, x, cadr(lis))
        })
        |> ignore
        rplacd(lis, cons(x, cdr(lis))) |> ignore
        return x
      }
      lis = cdr(lis)
    }
    x
  })
}

///|
fn doutern(x : Value) -> Value raise {
  if atom(x) {
    x
  } else {
    car(x)
  }
}

///|
fn unkind(x : Value, y : Value) -> Value raise {
  let y = car(datum(list3(q_kind, x, y)))
  kcntxt(y, symval(q_context)) |> ignore
  maxima_remf(y, x)
}

///|
fn remov(fact : Value) -> Value raise {
  mapc(arg => remov4(fact, arg) |> ignore, cdar(fact))
}

///|
fn remov4(fact : Value, cl : Value) -> Value raise {
  if symbolp(cl) || (consp(cl) && mnump(car(cl)).truthy()) {
    // A symbol or an interned number: take FACT off its property list.
    cput(cl, remove(fact, zl_get(cl, q_data)), q_data)
  } else if atom(cl) || atom(car(cl)) {
    t
  } else if atom(caar(cl)) {
    // An expression: REMOV4 FACT from its parts.
    mapc(lis => remov4(fact, lis) |> ignore, cdr(cl))
  } else if atom(caaar(cl)) {
    // The node DINTERN made for a compound expression.
    cput(cl, remove(fact, zl_get(cl, q_data)), q_data) |> ignore
    mapc(lis => remov4(fact, lis) |> ignore, cdar(cl))
  } else {
    Nil
  }
}

///|
fn killframe(cl : Value) -> Value raise {
  mapc(
    dat => {
      uncntxt(dat) |> ignore
      remov(dat) |> ignore
    },
    zl_get(cl, q_data),
  )
  |> ignore
  zl_remprop(cl, q_n_pluslabs) |> ignore
  zl_remprop(cl, q_n_labs) |> ignore
  zl_remprop(cl, q_obj) |> ignore
  zl_remprop(cl, q_var) |> ignore
  zl_remprop(cl, q_fact)
}

///|
fn activate(l : Value) -> Value raise {
  for e in l.iter() {
    if memq(e, symval(q_contexts)) is Nil {
      push_special(e, q_contexts) |> ignore
      cmark(e) |> ignore
    }
  }
  Nil
}

///|
fn deactivate(l : Value) -> Value raise {
  for e in l.iter() {
    if memq(e, symval(q_contexts)).truthy() {
      cunmrk(e) |> ignore
      set(q_contexts, remove(e, symval(q_contexts))) |> ignore
    }
  }
  Nil
}

///|
fn gccon() -> Value raise {
  gccon1() |> ignore
  if num_gt(symval(q_ear_conindex), symval(q_ear_connumber)) {
    gccon1() |> ignore
    if num_gt(symval(q_ear_conindex), symval(q_ear_connumber)) {
      merr("context: too many contexts.", []) |> ignore
    }
  }
  Nil
}

///|
fn gccon1() -> Value raise {
  set(q_ear_conindex, Fix(0L)) |> ignore
  let n = to_int(symval(q_ear_connumber))
  let conmark = symval(q_conmark)
  let conunmrk = symval(q_conunmrk)
  for i in 0..=n {
    if !eq(aref1(conmark, i), cdr(aref1(conunmrk, i))) {
      killc(aref1(conmark, i)) |> ignore
    } else {
      let ci = to_int(symval(q_ear_conindex))
      aset1(conunmrk, ci, aref1(conunmrk, i)) |> ignore
      aset1(conmark, ci, aref1(conmark, i)) |> ignore
      set(q_ear_conindex, Fix((ci + 1).to_int64())) |> ignore
    }
  }
  Nil
}

///|
fn cntxt(dat : Value, con : Value) -> Value raise {
  let con = if atom(con) { con } else { cdr(con) }
  putprop_(con, cons(dat, zl_get(con, q_data)), q_data) |> ignore
  if !eq(q_global, con) {
    putprop_(dat, con, q_con) |> ignore
  }
  dat
}

///|
fn kcntxt(fact : Value, con : Value) -> Value raise {
  let con = if atom(con) { con } else { cdr(con) }
  putprop_(con, fdel(fact, zl_get(con, q_data)), q_data) |> ignore
  if !eq(q_global, con) {
    zl_remprop(fact, q_con) |> ignore
  }
  fact
}

///|
fn cntp(f : Value) -> Value raise {
  let f = zl_get(f, q_con)
  if f is Nil {
    return t
  }
  let f = zl_get(f, q_cmark)
  if f.truthy() {
    lbool(num_gt(f, Fix(0L)))
  } else {
    Nil
  }
}

///|
fn contextmark() -> Value raise {
  let con = symval(q_context)
  if !eq(symval(q_current), con) {
    cunmrk(symval(q_current)) |> ignore
    set(q_current, con) |> ignore
    cmark(con)
  } else {
    Nil
  }
}

///|
fn cmark(con : Value) -> Value raise {
  let con = if atom(con) { con } else { cdr(con) }
  let cm = zl_get(con, q_cmark)
  putprop_(
    con,
    if cm.truthy() {
      num_add(cm, Fix(1L))
    } else {
      Fix(1L)
    },
    q_cmark,
  )
  |> ignore
  mapc(c => cmark(c) |> ignore, zl_get(con, q_subc))
}

///|
fn cunmrk(con : Value) -> Value raise {
  let con = if atom(con) { con } else { cdr(con) }
  let cm = zl_get(con, q_cmark)
  if cm.truthy() {
    putprop_(con, num_sub(cm, Fix(1L)), q_cmark) |> ignore
  }
  mapc(c => cunmrk(c) |> ignore, zl_get(con, q_subc))
}

// Garbage collection of the interning tables. A node is worth keeping exactly
// as long as some fact names it; number nodes additionally carry the chain
// edges (datums with no CON property) made by DINTNUM.

///|
/// Does some fact still name the node ND?
fn dnode_live_p(nd : Value) -> Value raise {
  lbool(zl_get(nd, q_data).truthy())
}

///|
/// Does some fact other than its own chain edges name the number node ND?
fn dnum_live_p(nd : Value) -> Value raise {
  for dat in zl_get(nd, q_data).iter() {
    if zl_get(dat, q_con).truthy() {
      return t
    }
  }
  Nil
}

///|
/// Drop the database nodes that no longer carry a fact.
fn db_gc() -> Value raise {
  db_gc_dobjects() |> ignore
  db_gc_nobjects()
}

///|
fn db_gc_dobjects() -> Value raise {
  if !every(x => dnode_live_p(x).truthy(), symval(q_dobjects)) {
    set(
      q_dobjects,
      remove_if_not(x => dnode_live_p(x).truthy(), symval(q_dobjects)),
    )
  } else {
    Nil
  }
}

///|
fn db_gc_nobjects() -> Value raise {
  if every(x => dnum_live_p(x).truthy(), symval(q_ear_nobjects)) {
    return Nil
  }
  // Take the chain down ...
  for dat in get(q_global, q_data).iter() {
    remov(dat) |> ignore
  }
  remprop(q_global, q_data) |> ignore
  set(
    q_ear_nobjects,
    remove_if_not(x => dnum_live_p(x).truthy(), symval(q_ear_nobjects)),
  )
  |> ignore
  // ... and lay it again over what is left (*NOBJECTS* is sorted descending).
  with_special(q_context, q_global, fn() {
    let mut l = symval(q_ear_nobjects)
    while cdr(l).truthy() {
      fact(
        if eq(q_d_zero, rgrp(caar(l), caadr(l))) {
          q_meqp
        } else {
          q_mgrp
        },
        car(l),
        cadr(l),
      )
      |> ignore
      l = cdr(l)
    }
    Nil
  })
}

///|
fn killc(con : Value) -> Value raise {
  contextmark() |> ignore
  if con.truthy() {
    mapc(d => remov(d) |> ignore, zl_get(con, q_data)) |> ignore
    zl_remprop(con, q_data) |> ignore
    zl_remprop(con, q_cmark) |> ignore
    zl_remprop(con, q_subc) |> ignore
  }
  t
}

///|
fn propg() -> Value raise {
  while true {
    if symval(q_n_pluss).truthy() {
      let x = dq_plus()
      let lab = zl_get(x, q_n_pluslabs)
      if zerop(logand(unlab(lab), unlab(n_labz(x)))) {
        mark_plus(x, lab) |> ignore
      } else {
        return t
      }
    } else if symval(q_n_s).truthy() {
      let x = dq_()
      let lab = zl_get(x, q_n_labs)
      if zerop(logand(unlab(lab), unlab(n_pluslabz(x)))) {
        mark_(x, lab) |> ignore
      } else {
        return t
      }
    } else {
      return Nil
    }
  }
  Nil
}

///|
fn mark_plus(cl : Value, lab : Value) -> Value raise {
  if symval(q_dbtrace).truthy() {
    set(q_ear_marks, num_add(symval(q_ear_marks), Fix(1L))) |> ignore
    format(t, "~%MARK+: marking ~A +", [cl]) |> ignore
    prlab(lab) |> ignore
  }
  mapc(lis => mark_plus0(cl, lab, lis) |> ignore, zl_get(cl, q_data))
}

///|
fn mark_plus0(cl : Value, lab : Value, fact : Value) -> Value raise {
  if symval(q_ear_dbcheck).truthy() {
    format(t, "~%MARK+0: checking ~a from ~A+", [car(fact), cl]) |> ignore
    prlab(lab) |> ignore
  }
  let v = onpu(lab, fact)
  if v.truthy() {
    v
  } else if !cntp(fact).truthy() {
    t
  } else {
    mark_plus1(cl, lab, fact)
  }
}

///|
fn mark_plus1(cl : Value, lab : Value, dat : Value) -> Value raise {
  if eq(caar(dat), q_kind) {
    if eq(cadar(dat), cl) {
      mid(caddar(dat), lab) // E1
    } else {
      Nil
    }
  } else if eq(caar(dat), q_par) {
    if !eq(caddar(dat), cl) {
      cancel(lab, dat) |> ignore // PR1
      mid(caddar(dat), lab) |> ignore
      for x in cadar(dat).iter() {
        if !eq(x, cl) {
          mid_(x, lab) |> ignore
        }
      }
    }
    Nil
  } else if eq(cadar(dat), cl) {
    if zl_get(caar(dat), q_n_pluslabs).truthy() { // V1
      end(caddar(dat), dbv(lab, zl_get(caar(dat), q_n_pluslabs))) |> ignore
    }
    if zl_get(caddar(dat), q_n_labs).truthy() { // F4
      end_(caar(dat), lpr(lab, zl_get(caddar(dat), q_n_labs)))
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn mark_(cl : Value, lab : Value) -> Value raise {
  if symval(q_dbtrace).truthy() {
    set(q_ear_marks, num_add(symval(q_ear_marks), Fix(1L))) |> ignore
    format(t, "~%MARK-: marking ~A -", [cl]) |> ignore
    prlab(lab) |> ignore
  }
  mapc(lis => mark_0(cl, lab, lis) |> ignore, zl_get(cl, q_data))
}

///|
fn mark_0(cl : Value, lab : Value, fact : Value) -> Value raise {
  if symval(q_ear_dbcheck).truthy() {
    format(t, "~%MARK-0: checking ~A from ~A-", [car(fact), cl]) |> ignore
    prlab(lab) |> ignore
  }
  let v = onpu(lab, fact)
  if v.truthy() {
    v
  } else if !cntp(fact).truthy() {
    t
  } else {
    mark_1(cl, lab, fact)
  }
}

///|
fn mark_1(cl : Value, lab : Value, dat : Value) -> Value raise {
  if eq(caar(dat), q_kind) {
    if !eq(cadar(dat), cl) {
      mid_(cadar(dat), lab) // E4
    } else {
      Nil
    }
  } else if eq(caar(dat), q_par) {
    if eq(caddar(dat), cl) {
      cancel(lab, dat) |> ignore // S4
      for x in cadar(dat).iter() {
        mid_(x, lab) |> ignore
      }
      Nil
    } else {
      let mut l = unlab(lab) // ALL4
      for x in cadar(dat).iter() {
        l = logand(unlab(n_labz(x)), l)
      }
      let lab = copyn(l)
      cancel(lab, dat) |> ignore
      mid_(caddar(dat), lab)
    }
  } else if eq(caddar(dat), cl) {
    if zl_get(caar(dat), q_n_pluslabs).truthy() { // A2
      end_(cadar(dat), dba(zl_get(caar(dat), q_n_pluslabs), lab)) |> ignore
    }
    if zl_get(cadar(dat), q_n_pluslabs).truthy() { // F6
      end_(caar(dat), lpr(zl_get(cadar(dat), q_n_pluslabs), lab))
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn uni(p1 : Value, p2 : Value, al : Value) -> Value raise {
  if dbvarp(p1).truthy() {
    dbunivar(p1, p2, al)
  } else if nodep(p1).truthy() {
    if dbvarp(p2).truthy() {
      dbunivar(p2, p1, al)
    } else if nodep(p2).truthy() {
      if eq(p1, p2) {
        al
      } else {
        Nil
      }
    } else {
      Nil
    }
  } else if dbvarp(p2).truthy() {
    dbunivar(p2, p1, al)
  } else if nodep(p2).truthy() {
    Nil
  } else {
    let al = uni(car(p1), car(p2), al)
    if al.truthy() {
      uni(cdr(p1), cdr(p2), al)
    } else {
      Nil
    }
  }
}

///|
fn dbunivar(p : Value, v : Value, al : Value) -> Value raise {
  let dum = assq(p, al)
  if dum is Nil {
    cons(cons(p, v), al)
  } else {
    uni(cdr(dum), v, al)
  }
}

///|
fn init_db() -> Unit raise {
  set(q_n_pluslab_high_bit_plus, most_negative_fixnum) |> ignore
  set(
    q_n_pluslabnumber_plus,
    Fix((integer_length(most_negative_fixnum) - 1).to_int64()),
  )
  |> ignore
  defvar_init(q_ear_lab_high_lab, list1(most_negative_fixnum))
  putprop(q_global, Fix(1L), q_cmark) |> ignore
  let n = to_int(symval(q_ear_connumber)) + 1
  defvar_init(q_conunmrk, make_array([n], initial=Nil))
  defvar_init(q_conmark, make_array([n], initial=Nil))
}
