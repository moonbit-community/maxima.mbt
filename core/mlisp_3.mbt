// Port of src/mlisp.lisp, part 3: arrays (hashed and declared), function
// definition (:=, define, fundef, ...), control structures (if, do, block,
// return, go) and Maxima macro expansion.

///|
/// Modulus used by the HASHER function - must be a power of 2.
let mlisp__hasher_mod : Int = 32768

///|
/// `(symbol-array x)` = `(get x 'array)`.
fn mlisp__symbol_array(x : Value) -> Value {
  get(x, q_array)
}

///|
/// Integer contents of a cell of a hashed-array vector.
fn mlisp__aref_int(ary : Value, i : Int) -> Int raise {
  to_int(aref1(ary, i))
}

///|
/// A fresh hashed-array vector (the HASHAR property's array).
fn mlisp__new_hashar(nsubs : Int) -> Value raise {
  let ary = gensym()
  putprop(ary, make_array([7], initial=Nil), q_array) |> ignore
  let a = mlisp__symbol_array(ary)
  aset1(a, 0, Fix(4L)) |> ignore
  aset1(a, 1, Fix(0L)) |> ignore
  aset1(a, 2, int(nsubs)) |> ignore
  ary
}

///|
/// Define $matrix so that apply(matrix,...) does not need to use Lisp apply.
fn d_matrix(rows : Value) -> Value raise {
  matrixhelper(rows)
}

///|
/// Call ONLY from $matrix
fn matrixhelper(rows : Value) -> Value raise {
  for row in rows.iter() {
    if !d_listp(row).truthy() {
      merr("matrix: row must be a list; found: ~M", [row]) |> ignore
    }
  }
  matcheck(rows) |> ignore
  cons(list1(q_d_matrix), rows)
}

///|
fn matcheck(l : Value) -> Value raise {
  let n = length(car(l))
  for l1 in cdr(l).iter() {
    if n != length(l1) {
      merr("matrix: all rows must be the same length.", []) |> ignore
    }
  }
  Nil
}

///|
fn d_has_key(a : Value, sub : Value) -> Value raise {
  if !d_listp(sub).truthy() {
    merr("has_key: second argument must be a list; found: ~M", [sub])
  } else if symbolp(a) {
    has_key_for_undeclared_array(a, sub)
  } else if hash_table_p(a) {
    has_key_for_lisp_hash_table(a, sub)
  } else {
    merr("has_key: ~M is neither an undeclared array nor a hash table.", [a])
  }
}

///|
/// This is adapted from the first part of HARRFIND.
fn has_key_for_undeclared_array(a : Value, sub : Value) -> Value raise {
  let ary = mlisp__symbol_array(mget(a, q_hashar))
  if ary is Nil {
    merr("has_key: ~M doesn't appear to be an undeclared array.", [a]) |> ignore
  }
  if mlisp__aref_int(ary, 2) != length(cdr(sub)) {
    merr("has_key: array ~:M must have ~:M indices; found: ~M", [
      a,
      aref1(ary, 2),
      sub,
    ])
    |> ignore
  }
  let sub = cdr(sub)
  let mut iteml = aref1(
    ary,
    3 + to_int(num_rem(hasher(sub), aref1(ary, 0))),
  )
  while iteml.truthy() {
    if alike(caar(iteml), sub).truthy() {
      return t
    }
    iteml = cdr(iteml)
  }
  Nil
}

///|
fn has_key_for_lisp_hash_table(a : Value, sub : Value) -> Value raise {
  // If SUB looks like [something], then assume the key is something. But
  // if SUB looks like [something, something else, ...], then assume the
  // key is (something, something else, ...).
  let key = if length(cdr(sub)) == 1 { cadr(sub) } else { cdr(sub) }
  let (_, is_present) = gethash2(key, a)
  lbool(is_present)
}

///|
fn harrfind(form : Value) -> Value raise {
  let mut ary = mlisp__symbol_array(mget(caar(form), q_hashar))
  if mlisp__aref_int(ary, 2) != length(cdr(form)) {
    merr("evaluation: array ~:M must have ~:M indices; found: ~M", [
      caar(form),
      aref1(ary, 2),
      form,
    ])
    |> ignore
  }
  let sub = cdr(form)
  let mut lispsub = 3 + to_int(num_rem(hasher(sub), aref1(ary, 0)))
  let mut iteml = aref1(ary, lispsub)
  while iteml.truthy() {
    if alike(caar(iteml), sub).truthy() {
      return cdar(iteml)
    }
    iteml = cdr(iteml)
  }
  if symval(q_evarrp).truthy() {
    return throw_tag(q_evarrp, q_notexist)
  }
  let y = arrfunp(caar(form))
  if y is Nil {
    return meval2(sub, form)
  }
  let y = arrfuncall(y, sub, form)
  ary = mlisp__symbol_array(mget(caar(form), q_hashar))
  lispsub = 3 + to_int(num_rem(hasher(sub), aref1(ary, 0)))
  iteml = aref1(ary, lispsub)
  let subc = list1(cons(sub, y))
  if iteml.truthy() {
    nconc(iteml, subc) |> ignore
  } else {
    aset1(ary, lispsub, subc) |> ignore
  }
  let nitems = mlisp__aref_int(ary, 1) + 1
  aset1(ary, 1, int(nitems)) |> ignore
  // Same growth rule as in ARRSTORE: HASHER only produces values below
  // +HASHER-MOD+, so growing past that many buckets is pure waste.
  let ncells = mlisp__aref_int(ary, 0)
  if nitems > ncells && ncells < mlisp__hasher_mod {
    let n = if 2 * ncells < mlisp__hasher_mod {
      2 * ncells
    } else {
      mlisp__hasher_mod
    }
    arraysize(caar(form), int(n)) |> ignore
  }
  y
}

///|
/// The element type of a Lisp array (as ARRAY-ELEMENT-TYPE reports it).
fn mlisp__array_element_type(ar : Value) -> Value {
  match ar {
    Vec(a) =>
      match a.elt {
        "fixnum" => q_fixnum
        "flonum" | "double-float" => q_flonum
        _ => t
      }
    _ => t
  }
}

///|
fn arrfind(form : Value) -> Value raise {
  let sub = cdr(form)
  let v = dimcheck(caar(form), sub, Nil)
  let type_ = if v.truthy() {
    car(arraydims(mget(caar(form), q_array)))
  } else {
    Nil
  }
  if v.truthy() {
    let arr = mlisp__symbol_array(mget(caar(form), q_array))
    let u = aref(arr, mlisp__int_indices(sub))
    let bound = if eq(type_, q_flonum) {
      !(numberp(u) && num_eq(u, symval(q_flounbound)))
    } else if eq(type_, q_fixnum) {
      !(numberp(u) && num_eq(u, symval(q_fixunbound)))
    } else {
      !eq(u, symval(q_munbound))
    }
    if bound {
      return u
    }
  }
  if symval(q_evarrp).truthy() {
    return throw_tag(q_evarrp, q_notexist)
  }
  let u = if v.truthy() { arrfunp(caar(form)) } else { Nil }
  if !v.truthy() || u is Nil {
    if eq(type_, q_flonum) {
      Flo(0.0)
    } else if eq(type_, q_fixnum) {
      Fix(0L)
    } else {
      meval2(sub, form)
    }
  } else {
    let u = arrfuncall(u, sub, form)
    aset(
      mlisp__symbol_array(mget(caar(form), q_array)),
      mlisp__int_indices(sub),
      u,
    )
    |> ignore
    u
  }
}

///|
fn d_array(x : Value) -> Value raise {
  let x = cdr(x)
  if symbolp(car(x)) {
    if symval(q_d_use_fast_arrays).truthy() {
      // Only the known type keywords denote an element type; any other
      // symbol is a (symbolic) dimension.
      let typep = member(
        cadr(x),
        list([q_d_any, q_d_fixnum, q_d_flonum, q_d_float, q_d_hashed, q_d_functional]),
      ).truthy()
      let type_ = if typep { cadr(x) } else { q_d_any }
      let name = car(x)
      let diml = if typep { cddr(x) } else { cdr(x) }
      // let make_array catch bad vals
      return mset(
        name,
        d_make_array(type_, mapcar(dim => add2(Fix(1L), meval(dim)), diml)),
      )
    }
    let compp0 = assoc(
      cadr(x),
      list([
        cons(q_d_complete, t),
        cons(q_d_integer, q_fixnum),
        cons(q_d_fixnum, q_fixnum),
        cons(q_d_float, q_flonum),
        cons(q_d_flonum, q_flonum),
      ]),
    )
    let fun = car(x)
    let mut compp : Value = Nil
    let mut diml = if compp0.truthy() {
      compp = cdr(compp0)
      cddr(x)
    } else {
      cdr(x)
    }
    let mut funp = false
    if memq(q_d_function, diml).truthy() {
      diml = mlisp__delete1_eq(q_d_function, diml)
      funp = true
    }
    diml = mapcar(d => meval(d), diml)
    if diml is Nil {
      wna_err(q_d_array) |> ignore
    } else if length(diml) > 5 {
      merr("array: number of dimensions must be 5 or less; found: ~M", [
        int(length(diml)),
      ])
      |> ignore
    } else if !every(d => fixnump(d), diml) {
      merr("array: all dimensions must be integers.", []) |> ignore
    }
    diml = mapcar(d => one_plus(d), diml)
    let new_ = if compp.truthy() { fun } else { gensym() }
    let dims = mlisp__int_indices(diml)
    putprop(
      new_,
      make_array(
        dims,
        initial=if eq(compp, q_fixnum) {
          Fix(0L)
        } else if eq(compp, q_flonum) {
          Flo(0.0)
        } else {
          symval(q_munbound)
        },
      ),
      q_array,
    )
    |> ignore
    // A memoizing function needs MUNBOUND in the unset cells so that
    // ARRFIND calls the function.
    if (funp || arrfunp(fun).truthy()) &&
      (eq(compp, q_fixnum) || eq(compp, q_flonum)) {
      fillarray(new_, list1(symval(q_munbound))) |> ignore
    }
    let old = mget(fun, q_hashar)
    if old is Nil {
      mputprop(fun, new_, q_array) |> ignore
    } else {
      let olda = mlisp__symbol_array(old)
      if mlisp__aref_int(olda, 2) != length(diml) {
        merr("array: array ~:M must have ~:M dimensions; found: ~M", [
          fun,
          aref1(olda, 2),
          int(length(diml)),
        ])
        |> ignore
      }
      let ncells = 2 + mlisp__aref_int(olda, 0)
      for n in 3..=ncells {
        for item in aref1(olda, n).iter() {
          let mut xs = car(item)
          let mut ys = diml
          while xs is Cons(_) {
            if !fixnump(car(xs)) ||
              num_lt(car(xs), Fix(0L)) ||
              !num_lt(car(xs), car(ys)) {
              merr(
                "array: index must be nonnegative integer less than ~M; found: ~M",
                [car(ys), car(xs)],
              )
              |> ignore
            }
            xs = cdr(xs)
            ys = cdr(ys)
          }
          if (eq(compp, q_fixnum) || eq(compp, q_flonum)) &&
            !eq(ml_typep(cdr(item)), compp) {
            merr("array: existing elements must be ~M; found: ~M", [
              compp,
              cdr(item),
            ])
            |> ignore
          }
          aset(mlisp__symbol_array(new_), mlisp__int_indices(car(item)), cdr(item))
          |> ignore
        }
      }
      mremprop(fun, q_hashar) |> ignore
      mputprop(fun, new_, q_array) |> ignore
    }
    add2lnc(fun, symval(q_d_arrays)) |> ignore
    if eq(compp, q_fixnum) {
      putprop(fun, q_d_fixnum, q_array_mode) |> ignore
    }
    if eq(compp, q_flonum) {
      putprop(fun, q_d_float, q_array_mode) |> ignore
    }
    fun
  } else if d_listp(car(x)).truthy() {
    cons(
      list1(q_mlist),
      mapcar(u => meval(cons(list1(q_d_array), cons(u, cdr(x)))), cdar(x)),
    )
  } else {
    merr("array: first argument must be a symbol or a list; found: ~M", [car(x)])
  }
}

///|
fn d_show_hash_array(x : Value) -> Value raise {
  maphash((k, v) => format(t, "~%~A-->~A", [k, v]) |> ignore, x)
  Nil
}

///|
fn arrstore(l : Value, r : Value) -> Value raise {
  let mut l = l
  let mut fun = caar(l)
  let mut mqapplyp = false
  let ary0 = mget(fun, q_array)
  if ary0.truthy() {
    let sub = mapcar(x => meval(x), cdr(l))
    dimcheck(fun, sub, t) |> ignore
    fun = car(arraydims(ary0))
    if (eq(fun, q_fixnum) || eq(fun, q_flonum)) && !eq(ml_typep(r), fun) {
      merr("assignment: attempt to assign ~M to an array of type ~M.", [r, fun])
      |> ignore
    }
    return aset(mlisp__symbol_array(ary0), mlisp__int_indices(sub), r)
  }
  let ary1 = mget(fun, q_hashar)
  if ary1.truthy() {
    let s = mlisp__symbol_array(ary1)
    if mlisp__aref_int(s, 2) != length(cdr(l)) {
      merr("assignment: array ~:M has dimension ~:M, but it was called by ~:M", [
        fun,
        aref1(s, 2),
        l,
      ])
      |> ignore
    }
    let sub = mapcar(x => meval(x), cdr(l))
    let lispsub = 3 + to_int(num_rem(hasher(sub), aref1(s, 0)))
    let hashl = aref1(s, lispsub)
    let mut hashl1 = hashl
    let mut found = false
    while hashl1 is Cons(_) {
      if alike(caar(hashl1), sub).truthy() {
        if eq(r, symval(q_munbound)) {
          aset1(s, 1, int(mlisp__aref_int(s, 1) - 1)) |> ignore
        } else {
          nconc(hashl, list1(cons(sub, r))) |> ignore
        }
        aset1(s, lispsub, mlisp__delete1_equal(car(hashl1), hashl)) |> ignore
        found = true
        break
      }
      hashl1 = cdr(hashl1)
    }
    if !found && !eq(r, symval(q_munbound)) {
      let subc = list1(cons(sub, r))
      if hashl is Nil {
        aset1(s, lispsub, subc) |> ignore
      } else {
        nconc(hashl, subc) |> ignore
      }
      aset1(s, 1, int(mlisp__aref_int(s, 1) + 1)) |> ignore
    }
    let s_ary = mlisp__symbol_array(ary1)
    let num_buckets = mlisp__aref_int(s_ary, 0)
    let num_elements = mlisp__aref_int(s_ary, 1)
    if num_elements > num_buckets && num_buckets < mlisp__hasher_mod {
      let n = if 2 * num_buckets < mlisp__hasher_mod {
        2 * num_buckets
      } else {
        mlisp__hasher_mod
      }
      arraysize(fun, int(n)) |> ignore
    }
    return r
  }
  let mut ary : Value = Nil
  if eq(fun, q_mqapply) {
    ary = meval(cadr(l))
    if mxorlistp(ary).truthy() || (arrayp(ary) && !stringp(ary)) {
      // strings are Lisp arrays but not something to store into
      mqapplyp = true
      l = cdr(l)
    }
  }
  let is_store = (a : Value) => mxorlistp(a).truthy() ||
    (arrayp(a) && !stringp(a)) ||
    hash_table_p(a) ||
    struct_typep(a, "mgenarray")
  if !mqapplyp &&
    (
      !boundp(fun) ||
      {
        ary = symval(fun)
        !is_store(ary)
      }
    ) {
    if eq(fun, q_mqapply) || eq(fun, q_d_op_pct) {
      merr("assignment: cannot assign to ~M", [l]) |> ignore
    }
    if symval(q_d_use_fast_arrays).truthy() {
      // Call MSET directly. The hash table argument is only an arity flag,
      // so the raw subscript list (CDDR L) does fine.
      mset(fun, make_equal_hash_table(cddr(l))) |> ignore
    } else {
      add2lnc(fun, symval(q_d_arrays)) |> ignore
      let a = mlisp__new_hashar(length(cdr(l)))
      mputprop(fun, a, q_hashar) |> ignore
    }
    return arrstore(l, r)
  }
  if arrayp(ary) || hash_table_p(ary) || struct_typep(ary, "mgenarray") {
    return arrstore_extend(ary, mevalargs(cdr(l)), r)
  }
  if eq(caar(ary), q_mlist) || length(l) == 2 {
    if eq(caar(ary), q_d_matrix) {
      if !d_listp(r).truthy() || length(cadr(ary)) != length(r) {
        merr(
          "assignment: matrix row must be a list, and same length as first row;~%found:~%~M",
          [r],
        )
        |> ignore
      }
    } else if length(l) != 2 {
      merr("assignment: matrix row must have one index; found: ~M", [
        cons(list1(q_mlist), cdr(l)),
      ])
      |> ignore
    }
    let index = meval(cadr(l))
    if !fixnump(index) {
      merr("assignment: matrix row index must be an integer; found: ~M", [index])
      |> ignore
    } else if num_gt(index, Fix(0L)) && num_lt(index, int(length(ary))) {
      rplaca(nthcdr(to_int(index) - 1, cdr(ary)), r) |> ignore
    } else {
      merr("assignment: matrix row index ~A out of range.", [index]) |> ignore
    }
    r
  } else {
    if length(l) != 3 {
      merr("assignment: matrix must have two indices; found: ~M", [
        cons(list1(q_mlist), cdr(l)),
      ])
      |> ignore
    }
    let i = meval(cadr(l))
    let j = meval(caddr(l))
    d_setelmx(r, i, j, ary) |> ignore
    r
  }
}

///|
fn arrfunp(x : Value) -> Value raise {
  if symval(q_d_transrun).truthy() {
    let g = getl(x, list1(q_a_subr))
    if g.truthy() {
      return g
    }
  }
  mgetl(x, list1(q_aexpr))
}

///|
fn arrfuncall(arrfun : Value, subs : Value, form : Value) -> Value raise {
  with_special(q_aexprp, t, () => if eq(car(arrfun), q_aexpr) {
    mapply1(cadr(arrfun), subs, cadr(arrfun), form)
  } else if eq(car(arrfun), q_a_subr) {
    apply(cadr(arrfun), subs)
  } else {
    Nil
  })
}

///|
/// SXHASH: a non-negative hash code that depends only on the printed
/// identity of an atom.
fn mlisp__sxhash(x : Value) -> Value {
  let h = match x {
    Sym(s) => s.name.hash()
    _ => hash_equal(x)
  }
  Fix((h & 0x3FFFFFFF).to_int64())
}

///|
/// This is not the best way to write a hasher.  But, please don't change
/// this code or you're liable to break SAVE files.
fn hasher(l : Value) -> Value raise {
  if l is Nil {
    return Fix(0L)
  }
  let x = car(l)
  let h = if specrepp(x).truthy() {
    merr(
      "hash function: cannot hash a special expression (CRE, Taylor or Poisson).",
      [],
    )
  } else if fixnump(x) || floatp(x) {
    num_add(
      if fixnump(x) {
        x
      } else {
        floor1(num_add(x, Flo(5.000000237487257e-4)))
      },
      num_mul(Fix(7L), hasher(cdr(l))),
    )
  } else if atom(x) {
    num_add(mlisp__sxhash(x), hasher(cdr(l)))
  } else {
    num_add(
      num_add(num_add(Fix(1L), mlisp__sxhash(caar(x))), hasher(cdr(x))),
      hasher(cdr(l)),
    )
  }
  // NOTE: Assumes that +hasher-mod+ is 2^n.
  logand(int(mlisp__hasher_mod - 1), h)
}

///|
fn arraysize(fun : Value, n : Value) -> Value raise {
  let n = to_int(n)
  let old = mlisp__symbol_array(mget(fun, q_hashar))
  let newsym = gensym()
  mputprop(fun, newsym, q_hashar) |> ignore
  putprop(newsym, make_array([n + 3], initial=Nil), q_array) |> ignore
  let new_ = mlisp__symbol_array(newsym)
  aset1(new_, 0, int(n)) |> ignore
  aset1(new_, 1, aref1(old, 1)) |> ignore
  aset1(new_, 2, aref1(old, 2)) |> ignore
  let ncells = 2 + mlisp__aref_int(old, 0)
  for indx in 3..=ncells {
    for item in aref1(old, indx).iter() {
      let i = 3 + to_int(num_rem(hasher(car(item)), int(n)))
      let y = aref1(new_, i)
      if y.truthy() {
        nconc(y, list1(item)) |> ignore
      } else {
        aset1(new_, i, list1(item)) |> ignore
      }
    }
  }
  t
}

///|
fn dimcheck(ary : Value, sub : Value, fixpp : Value) -> Value raise {
  let dims = cdr(arraydims(mget(ary, q_array)))
  let mut x = sub
  let mut ret = t
  let mut y = dims
  while true {
    if y is Nil {
      if x.truthy() {
        merr("Array ~:M has dimensions ~:M, but was called with ~:M", [
          ary,
          cons(list1(q_mlist), mapcar(d => one_minus(d), dims)),
          cons(list1(q_mlist), sub),
        ])
        |> ignore
      }
      break
    }
    if x is Nil ||
      (
        fixnump(car(x)) &&
        (num_lt(car(x), Fix(0L)) || !num_lt(car(x), car(y)))
      ) {
      y = Nil
      x = cons(Nil, t)
    } else if !fixnump(car(x)) {
      if fixpp.truthy() {
        y = Nil
        x = cons(Nil, t)
      } else {
        ret = Nil
      }
    }
    x = cdr(x)
    y = cdr(y)
  }
  ret
}

///|
fn constlam(x : Value) -> Value raise {
  let lam = x
  if symval(q_aexprp).truthy() {
    let vars = mparams(cadr(lam))
    list_star([
      car(lam),
      cadr(lam),
      mlisp__mbinding(vars, vars, Nil, () => mapcar(e => meval(e), cddr(lam))),
    ])
  } else {
    lam
  }
}

///|
fn d_define(l : Value) -> Value raise {
  twoargcheck(l) |> ignore
  let l = cdr(l)
  let fun = if mquotep(car(l)).truthy() {
    cadar(l)
  } else if !atom(car(l)) &&
    (
      eq(caaar(l), q_d_ev) ||
      eq(caaar(l), q_d_funmake) ||
      eq(caaar(l), q_d_arraymake)
    ) {
    meval(car(l))
  } else {
    disp2(car(l))
  }
  let body = meval(cadr(l))
  meval(list3(list1(q_mdefine), fun, body))
}

///|
fn set_lineinfo(fnname : Value, lineinfo : Value, body : Value) -> Value raise {
  if consp(lineinfo) && eq(q_src, third(lineinfo)) {
    rplacd(cddr(lineinfo), list2(fnname, first(lineinfo))) |> ignore
    putprop(fnname, body, q_lineinfo)
  } else {
    remprop(fnname, q_lineinfo)
  }
}

///|
fn mdefine(l : Value) -> Value raise {
  // for mdefine's we allow use the oldstyle hasharrays
  with_special(q_d_use_fast_arrays, Nil, () => {
    twoargcheck(l) |> ignore
    let l = cdr(l)
    let mut fun = car(l)
    let body = cadr(l)
    let mut args : Value = Nil
    let mut subs : Value = Nil
    let mut ary : Value = Nil
    let mut fnname : Value = Nil
    let mut mqdef = false
    if atom(fun) ||
      {
        mqdef = eq(caar(fun), q_mqapply)
        mqdef && memq(q_array, cdar(fun)).truthy()
      } {
      merr(
        "define: argument cannot be an atom or a subscripted memoizing function; found: ~M",
        [fun],
      )
      |> ignore
    } else if mqdef {
      if atom(cadr(fun)) ||
        {
          ary = memq(q_array, cdr(caadr(fun)))
          ary is Nil
        } {
        merr("define: expected a subscripted expression; found: ~M", [cadr(fun)])
        |> ignore
      }
      subs = cdadr(fun)
      args = cddr(fun)
      fun = cadr(fun)
      fnname = caar(fun)
      if !mgetl(fnname, list2(q_hashar, q_array)).truthy() &&
        get(fnname, q_specsimp).truthy() {
        mtell(
          list([
            Str("define: warning: redefining built-in subscripted function ~:M~%"),
            fnname,
          ]),
        )
        |> ignore
      }
    } else {
      fnname = caar(fun)
      if mopp(fnname).truthy() ||
        fnname is Nil ||
        eq(fnname, t) ||
        eq(fnname, q_d_all) ||
        eq(fnname, q_d_allbut) ||
        eq(fnname, q_d_op_pct) {
        merr(
          "define: function name cannot be a built-in operator or special symbol; found: ~:@M",
          [fnname],
        )
        |> ignore
      } else {
        ary = memq(q_array, cdar(fun))
        if ary.truthy() {
          subs = cdr(fun)
        } else {
          args = cdr(fun)
          mredef_check(fnname) |> ignore
        }
      }
    }
    if !ary.truthy() {
      remove1(list1(fnname), q_mmacro, t, symval(q_d_macros), t) |> ignore
    }
    mdefchk(
      fnname,
      if args.truthy() {
        args
      } else if !mqdef {
        subs
      } else {
        Nil
      },
      ary,
      lbool(mqdef),
    )
    |> ignore
    if !eq(fnname, caar(fun)) {
      rplaca(car(fun), fnname) |> ignore
    }
    if !ary.truthy() {
      if symval(q_evp).truthy() && memq(fnname, car(symval(q_loclist))).truthy() {
        mputprop(fnname, t, q_local_fun) |> ignore
      } else {
        remove_transl_fun_props(fnname) |> ignore
      }
      add2lnc(cons(list1(fnname), args), symval(q_d_functions)) |> ignore
      set_lineinfo(fnname, cadar(fun), body) |> ignore
      mputprop(fnname, mdefine1(args, body), q_mexpr) |> ignore
      if symval(q_d_translate).truthy() {
        merr("translate-function: not supported in this port", []) |> ignore
      }
    } else {
      add2lnc(fnname, symval(q_d_arrays)) |> ignore
      ary = mgetl(fnname, list2(q_hashar, q_array))
      remove_transl_array_fun_props(fnname) |> ignore
      if ary.truthy() {
        let nsubs = if eq(car(ary), q_hashar) {
          mlisp__aref_int(mlisp__symbol_array(cadr(ary)), 2)
        } else {
          length(cdr(arraydims(cadr(ary))))
        }
        if nsubs != length(subs) {
          merr("define: ~:M already defined with different number of subscripts.", [
            fnname,
          ])
          |> ignore
        }
        mdefarray(fnname, subs, args, body, lbool(mqdef)) |> ignore
      } else {
        let a = mlisp__new_hashar(length(subs))
        mputprop(fnname, a, q_hashar) |> ignore
        mdefarray(fnname, subs, args, body, lbool(mqdef)) |> ignore
      }
    }
    cons(list2(q_mdefine, q_simp), copy_list(l))
  })
}

///|
/// Checks to see if a user is clobbering the name of a system function.
/// Prints a warning and returns T if he is, and NIL if he isn't.
fn mredef_check(fnname : Value) -> Value raise {
  if !mget(fnname, q_mexpr).truthy() &&
    (
      (
        (
          get(fnname, q_autoload).truthy() ||
          getl_lm_fcn_prop(fnname, list1(q_subr)).truthy()
        ) &&
        !get(fnname, q_translated).truthy()
      ) ||
      mopp(fnname).truthy()
    ) {
    format(
      t,
      "define: warning: redefining the built-in ~:[function~;operator~] ~a~%",
      [getl(fnname, list2(q_verb, q_operators)), stripdollar(fnname)],
    )
    |> ignore
    t
  } else {
    Nil
  }
}

///|
fn mdefarray(
  fun : Value,
  subs : Value,
  args : Value,
  body : Value,
  mqdef : Value,
) -> Value raise {
  if hash_table_p(fun) {
    // PRETTY SURE THIS NEXT MESSAGE IS UNREACHABLE
    raise LispError::SimpleError(
      format_to_string("~a is already a hash table.  Make it a function first", [
        fun,
      ]),
    )
  }
  if args is Nil && !mqdef.truthy() {
    mputprop(fun, mdefine1(subs, body), q_aexpr)
  } else if every(
      u => consp(u) || d_constantp(u).truthy() || stringp(u),
      subs,
    ) {
    arrstore(cons(list1(fun), subs), mdefine1(args, body))
  } else {
    mdefchk(fun, subs, t, Nil) |> ignore
    mputprop(fun, mdefine1(subs, mdefine1(args, body)), q_aexpr)
  }
}

///|
fn mspecfunp(fun : Value) -> Value raise {
  lbool(
    (
      getl_lm_fcn_prop(fun, list1(q_macro)).truthy() ||
      getl(fun, list1(q_mfexpr_star)).truthy() ||
      (
        symval(q_d_transrun).truthy() &&
        get(fun, q_translated_mmacro).truthy()
      ) ||
      mget(fun, q_mmacro).truthy()
    ) &&
    !get(fun, q_evok).truthy(),
  )
}

///|
fn mdefine1(args : Value, body : Value) -> Value raise {
  list3(list1(q_lambda), cons(list1(q_mlist), args), body)
}

///|
fn mdefchk(fun : Value, args : Value, ary : Value, mqdef : Value) -> Value raise {
  let dup = find_duplicate(args, test_=mlisp__eq_fn, key=q_mparam)
  if dup.truthy() {
    merr("define: ~M occurs more than once in the parameter list", [mparam(dup)])
    |> ignore
  }
  let mfexprp = symval(q_mfexprp).truthy()
  let mut l = args
  let mut mfex = false
  let mut mlex = false
  while l is Cons(_) {
    let ok = mdefparam(car(l)).truthy() ||
      (
        (!ary.truthy() || mqdef.truthy()) &&
        (
          (
            mfexprp &&
            mquotep(car(l)).truthy() &&
            mdefparam(cadar(l)).truthy() &&
            {
              mfex = true
              true
            }
          ) ||
          (
            mdeflistp(l).truthy() &&
            (
              mdefparam(cadar(l)).truthy() ||
              (
                mfexprp &&
                mquotep(cadar(l)).truthy() &&
                mdefparam(cadr(cadar(l))).truthy() &&
                {
                  mfex = true
                  true
                }
              )
            ) &&
            {
              mlex = true
              true
            }
          )
        )
      )
    if !ok {
      merr(
        "define: in definition of ~:M, parameter must be a symbol and must not be a system constant; found: ~M",
        [fun, car(l)],
      )
      |> ignore
    }
    l = cdr(l)
  }
  if mfex && !mqdef.truthy() {
    mputprop(fun, t, q_mfexprp) |> ignore
  }
  if mlex && !mqdef.truthy() {
    mputprop(fun, t, q_mlexprp)
  } else {
    Nil
  }
}

///|
fn mdefparam(x : Value) -> Value raise {
  lbool(symbolp(x) && !get(x, q_sysconst).truthy())
}

///|
fn mdeflistp(l : Value) -> Value raise {
  lbool(
    cdr(l) is Nil &&
    d_listp(car(l)).truthy() &&
    cdar(l).truthy() &&
    cddar(l) is Nil,
  )
}

///|
fn mopp(fun : Value) -> Value raise {
  lbool(
    !eq(fun, q_mqapply) &&
    (
      mopp1(fun).truthy() ||
      // TELLSIMP rules give FUN an OPERATORS property too, so with rules
      // check the simplifier FUN had before them, last in its OLDRULES.
      (
        get(fun, q_operators).truthy() &&
        (
          !rulechk(fun).truthy() ||
          car(last(mget(fun, q_oldrules))).truthy()
        ) &&
        !memq(fun, symval(q_rulefcnl)).truthy() &&
        !get(fun, q_opers).truthy()
      )
    ),
  )
}

///|
fn mopp1(fun : Value) -> Value raise {
  let op = get(fun, q_op)
  lbool(op.truthy() && !memq(op, cdr(symval(q_d_props))).truthy())
}

///|
/// maybe should have a separate version, or a macro..
fn mapply(a : Value, b : Value, c : Value) -> Value raise {
  mapply1(a, b, c, Nil)
}

///|
fn d_apply(fun : Value, arg : Value) -> Value raise {
  if !d_listp(arg).truthy() {
    merr("apply: second argument must be a list; found: ~M", [arg]) |> ignore
  }
  let fun_opr = getopr(fun)
  autoldchk(fun_opr) |> ignore
  mapply1(fun_opr, cdr(arg), fun, list3(list1(q_d_apply), fun, arg))
}

///|
fn autoldchk(fun : Value) -> Value raise {
  if symbolp(fun) &&
    get(fun, q_autoload).truthy() &&
    !(fboundp(fun) || mfboundp(fun).truthy()) {
    load_function(fun, t)
  } else {
    Nil
  }
}

///|
fn d_dispfun(l : Value) -> Value raise {
  let l = cdr(l)
  if cdr(l).truthy() || !eq(car(l), q_d_all) {
    dispfun1(l, Nil, Nil)
  } else {
    cons(
      list2(q_mlist, q_simp),
      append_n([
        cdr(dispfun1(cdr(symval(q_d_functions)), t, Nil)),
        cdr(
          dispfun1(
            mapcan(
              x => if mget(x, q_aexpr).truthy() { list1(x) } else { Nil },
              cdr(symval(q_d_arrays)),
            ),
            Nil,
            t,
          ),
        ),
        cdr(dispfun1(cdr(symval(q_d_macros)), t, Nil)),
      ]),
    )
  }
}

///|
fn dispfun1(l : Value, flag : Value, maexprp : Value) -> Value raise {
  cons(
    list2(q_mlist, q_simp),
    mapcar(
      fun => cadr(
        d_ldisp(
          list1(
            consfundef(
              if flag.truthy() {
                caar(fun)
              } else {
                fun
              },
              maexprp,
              Nil,
            ),
          ),
        ),
      ),
      l,
    ),
  )
}

///|
fn d_fundef(x : Value) -> Value raise {
  consfundef(fexprcheck(x), Nil, Nil)
}

///|
fn consfundef(x : Value, maexprp : Value, stringp_ : Value) -> Value raise {
  let arryp = !atom(x) &&
    !eq(caar(x), q_mqapply) &&
    memq(q_array, cdar(x)).truthy()
  let mut name : Value = Nil
  let mut fun : Value = Nil
  if atom(x) {
    name = if stringp(x) { d_verbify(x) } else { x }
    fun = if !maexprp.truthy() {
      mgetl(name, list2(q_mexpr, q_mmacro))
    } else {
      Nil
    }
    if !fun.truthy() {
      fun = mgetl(name, list1(q_aexpr))
    }
  } else if arryp {
    name = cons(list2(caar(x), q_array), cdr(x))
    fun = meval1(name).0
    if atom(fun) || !eq(caar(fun), q_lambda) {
      fun = Nil
    }
  }
  if !fun.truthy() {
    if stringp_.truthy() {
      return x
    }
    merr("fundef: no such function: ~:M", [x]) |> ignore
  }
  cons(
    if eq(car(fun), q_mmacro) {
      list2(q_mdefmacro, q_simp)
    } else {
      list2(q_mdefine, q_simp)
    },
    if arryp {
      cons(cons(list1(q_mqapply), cons(name, cdadr(fun))), cddr(fun))
    } else {
      let body = caddr(cadr(fun))
      if eq(car(fun), q_aexpr) && !atom(body) && eq(caar(body), q_lambda) {
        list2(
          cons(
            list1(q_mqapply),
            cons(cons(cons(name, list1(q_array)), cdr(cadadr(fun))), cdadr(body)),
          ),
          caddr(body),
        )
      } else {
        list2(
          cons(
            cons(
              name,
              if eq(car(fun), q_aexpr) {
                list1(q_array)
              } else {
                Nil
              },
            ),
            cdr(cadadr(fun)),
          ),
          body,
        )
      }
    },
  )
}

///|
fn d_funmake(fun : Value, args : Value) -> Value raise {
  if !(
      stringp(fun) ||
      symbolp(fun) ||
      d_subvarp(fun).truthy() ||
      (!atom(fun) && eq(caar(fun), q_lambda))
    ) {
    merr(
      "funmake: first argument must be a symbol, subscripted symbol, string, or lambda expression; found: ~M",
      [fun],
    )
    |> ignore
  }
  if !d_listp(args).truthy() {
    merr("funmake: second argument must be a list; found: ~M", [args]) |> ignore
  }
  mcons_op_args(getopr(fun), cdr(args))
}

///|
fn mcons_op_args(op : Value, args : Value) -> Value raise {
  if symbolp(op) {
    cons(list1(op), args)
  } else {
    list_star([list1(q_mqapply), op, args])
  }
}

///|
fn optionp(x : Value) -> Value raise {
  lbool(
    boundp(x) &&
    !memq(x, cdr(symval(q_d_values))).truthy() &&
    !memq(x, cdr(symval(q_d_labels))).truthy(),
  )
}

///|
fn mcond(form : Value) -> Value raise {
  let mut u = cdr(form)
  while u is Cons(_) {
    let v = mevalp(car(u))
    if eq(v, t) {
      return meval(cadr(u))
    } else if v.truthy() {
      return list_star([
        list1(q_mcond),
        v,
        mapcar(x => mcond_eval_symbols(q_meval1, x), cdr(u)),
      ])
    }
    u = cddr(u)
  }
  Nil
}

///|
fn mcond_eval_symbols(ev : Value, form : Value) -> Value raise {
  if symbolp(form) {
    funcall(ev, [form])
  } else if atom(form) {
    form
  } else if getl(caar(form), list1(q_mfexpr_star)).truthy() &&
    !memq(
      caar(form),
      list([q_mcond, q_mand, q_mor, q_mnot, q_mprogn, q_mdo, q_mdoin]),
    ).truthy() {
    form
  } else {
    recur_apply(
      lfunc("mcond-eval-symbols", a => mcond_eval_symbols(ev, arg(a, 0))),
      form,
    )
  }
}

///|
/// The body of a DO loop: run ACTION, catching RETURN/GO thrown to MPROG.
/// Returns Some(value) when the loop is left by a return.
fn mlisp__do_step(action : Value, bindl : Value) -> Value? raise {
  let val = catch_tag(q_mprog, () => {
    meval(action) |> ignore
    Nil
  })
  if val is Nil {
    None
  } else if atom(val) {
    merr("do loop: 'go' not within 'block': ~M", [val]) |> ignore
    None
  } else if !eq(bindl, symval(q_bindlist)) {
    merr("do loop: illegal 'return': ~M", [car(val)]) |> ignore
    None
  } else {
    Some(car(val))
  }
}

///|
fn mdo(form : Value) -> Value raise {
  let form = cdr(form)
  with_special(q_mdop, t, () => {
    let my_var = if car(form).truthy() { car(form) } else { q_mdo }
    let my_step = if caddr(form).truthy() {
      meval(caddr(form))
    } else {
      Fix(1L)
    }
    let next = if cadddr(form).truthy() {
      cadddr(form)
    } else {
      list3(list1(q_mplus), my_step, my_var)
    }
    let test_ = list3(
      list1(q_mor),
      if car(cddddr(form)) is Nil {
        Nil
      } else {
        list3(
          list1(
            if mnegp(d_numfactor(my_step)).truthy() {
              q_mlessp
            } else {
              q_mgreaterp
            },
          ),
          my_var,
          car(cddddr(form)),
        )
      },
      cadr(cddddr(form)),
    )
    let do_body = caddr(cddddr(form))
    let vars = list1(my_var)
    let vals = list1(
      if cadr(form) is Nil {
        Fix(1L)
      } else {
        meval(cadr(form))
      },
    )
    mlisp__mbinding(vars, vals, Nil, () => {
      let bindl = symval(q_bindlist)
      while !is_(test_).truthy() {
        match mlisp__do_step(do_body, bindl) {
          None => mset(my_var, meval(next)) |> ignore
          Some(v) => return v
        }
      }
      q_d_done
    })
  })
}

///|
fn key_value_pairs_given_key_lists(x : Value, key_lists : Value) -> Value raise {
  mapcar(
    l => list3(list1(q_mlist), l, mfuncall(q_d_arrayapply, list2(x, l))),
    key_lists,
  )
}

///|
fn key_value_pairs_for_hashed_array(x : Value) -> Value raise {
  let one_d_hash_table = gethash(q_dim1, x)
  let info = mfuncall(q_d_arrayinfo, list1(x))
  let keys_raw = cdddr(info)
  let key_lists = if one_d_hash_table.truthy() {
    mapcar(y => cons(list1(q_mlist), list1(y)), keys_raw)
  } else {
    keys_raw
  }
  key_value_pairs_given_key_lists(x, key_lists)
}

///|
fn key_value_pairs_for_undeclared_array(x : Value) -> Value raise {
  let info = mfuncall(q_d_arrayinfo, list1(x))
  let key_lists = cdddr(info)
  key_value_pairs_given_key_lists(x, key_lists)
}

///|
/// Return the list of values that "for x in e" assigns to x in turn, given
/// the value of e. Translated loops call this too.
fn mdoin_elements(set_ : Value) -> Value raise {
  let set_ = format1(set_)
  if d_atom(set_).truthy() {
    if hash_table_p(set_) {
      key_value_pairs_for_hashed_array(set_)
    } else if safe_mget(set_, q_hashar).truthy() {
      key_value_pairs_for_undeclared_array(set_)
    } else {
      merr(
        "do loop: atomic 'in' argument must be a hashed or undeclared array; found: ~M",
        [set_],
      )
    }
  } else {
    margs(set_)
  }
}

///|
fn mdoin(form : Value) -> Value raise {
  let form = cdr(form)
  let my_var = if car(form).truthy() { car(form) } else { q_mdo }
  with_special(q_mdop, t, () => {
    let mut set_ = mdoin_elements(meval(cadr(form)))
    let test_ = list3(
      list1(q_mor),
      if car(cddddr(form)).truthy() {
        list3(list1(q_mgreaterp), my_var, car(cddddr(form)))
      } else {
        Nil
      },
      cadr(cddddr(form)),
    )
    let action = caddr(cddddr(form))
    if atom(set_) {
      q_d_done
    } else {
      mlisp__mbinding(list1(my_var), list1(car(set_)), Nil, () => {
        let bindl = symval(q_bindlist)
        while !(atom(set_) || is_(test_).truthy()) {
          match mlisp__do_step(action, bindl) {
            None => {
              set_ = cdr(set_)
              if set_.truthy() {
                mset(my_var, car(set_)) |> ignore
              }
            }
            Some(v) => return v
          }
        }
        q_d_done
      })
    }
  })
}

///|
/// BLOCK. RETURN and GO inside it throw to the tag MPROG: RETURN throws
/// `(value)`, GO throws the (atomic) tag.
fn mprog(prog : Value) -> Value raise {
  let mut prog = cdr(prog)
  with_special(q_mlocp, t, () => {
    let mut vars : Value = Nil
    let mut vals : Value = Nil
    if d_listp(car(prog)).truthy() {
      vars = cdar(prog)
      prog = cdr(prog)
    }
    vals = vars
    for v in vars.iter() {
      if !atom(v) {
        vals = t
        break
      }
    }
    if eq(vals, t) {
      vals = mapcar(
        v => if atom(v) {
          v
        } else if eq(caar(v), q_msetq) {
          meval(caddr(v))
        } else {
          merr(
            "block: variable list must comprise only atoms and assignment expressions; found: ~M",
            [v],
          )
        },
        vars,
      )
      vars = mapcar(v => if atom(v) { v } else { cadr(v) }, vars)
    }
    let dup = find_duplicate(vars, test_=mlisp__eq_fn)
    if dup.truthy() {
      merr("block: ~M occurs more than once in the variable list", [dup])
      |> ignore
    }
    set(q_loclist, cons(Nil, symval(q_loclist))) |> ignore
    // Ensure that MUNLOCAL gets called so that we don't leak local
    // properties if we run into an error
    defer {
      munlocal() |> ignore
    }
    let mprogp = prog
    mlisp__mbinding(vars, vals, Nil, () => with_specials(
      [(q_mprogp, mprogp), (q_d_op_pct_pct, q_d_op_pct_pct)],
      () => {
        let bindl = symval(q_bindlist)
        let mut val = q_d_done
        let mut retp = false
        let mut p = mprogp
        while p is Cons(_) {
          if atom(car(p)) {
            if cdr(p) is Nil {
              retp = true
              val = meval(car(p))
            }
          } else {
            let stmt = car(p)
            let x = catch_tag(q_mprog, () => {
              val = meval(stmt)
              set(q_d_op_pct_pct, val) |> ignore
              Nil
            })
            if x is Nil {
              ()
            } else if !eq(bindl, symval(q_bindlist)) {
              if !atom(x) {
                merr("block: illegal 'return': ~M", [car(x)]) |> ignore
              } else {
                merr("block: illegal 'go': ~M", [x]) |> ignore
              }
            } else if !atom(x) {
              retp = true
              val = car(x)
            } else {
              p = member_equal(x, mprogp)
              if p is Nil {
                merr("block: no such tag: ~:M", [x]) |> ignore
              }
            }
          }
          if retp {
            p = list1(Nil)
          }
          p = cdr(p)
        }
        val
      },
    ))
  })
}

///|
fn mreturn(x? : Value = Nil, args : Value) -> Value raise {
  if args.truthy() {
    merr("return: too many arguments; found: ~M", [
      list_star([list1(q_mlist), x, args]),
    ])
  } else if !symval(q_mprogp).truthy() && !symval(q_mdop).truthy() {
    merr("return: not within 'block' or 'do'", [])
  } else {
    throw_tag(q_mprog, list1(x))
  }
}

///|
fn mgo(tag : Value) -> Value raise {
  let tag = fexprcheck(tag)
  if !symval(q_mprogp).truthy() {
    merr("go: not within 'block'", [])
  } else if atom(tag) {
    throw_tag(q_mprog, tag)
  } else {
    merr("go: argument must be an atom; found: ~M", [tag])
  }
}

///|
fn d_subvar(l : Value) -> Value raise {
  let l = cdr(l)
  if l is Nil {
    wna_err(q_d_subvar) |> ignore
  }
  meval(cons(list2(q_mqapply, q_array), l))
}

///|
fn rat(x : Value, y : Value) -> Value raise {
  list3(list2(q_rat, q_simp), x, y)
}

///|
fn add2lnc(item : Value, llist : Value) -> Value raise {
  if memalike(
      item,
      if d_listp(llist).truthy() {
        cdr(llist)
      } else {
        llist
      },
    ).truthy() {
    Nil
  } else {
    let mut llist = llist
    if !atom(item) {
      llist = mlisp__delete1_equal(assoc_equal(car(item), llist), llist)
    }
    nconc(llist, list1(item))
  }
}

///|
fn bigfloatm_star(bf : Value) -> Value raise {
  let mut bf = bf
  if !memq(q_simp, cdar(bf)).truthy() {
    bf = cons(list_star([caar(bf), q_simp, cdar(bf)]), cdr(bf))
  }
  if symval(q_d_float).truthy() {
    d_float(bf)
  } else {
    bf
  }
}

///|
fn d_allbut(args : Value) -> Value raise {
  cons(list1(q_d_allbut), args)
}

///|
fn dskrat(x : Value) -> Value raise {
  orderpointer(caddar(x)) |> ignore
  let mut a = symval(q_genvar)
  let mut b = cadddr(car(x))
  while a is Cons(_) && b is Cons(_) {
    // for TAYLOR forms
    dskrat_subst(car(a), car(b), cddddr(car(x))) |> ignore
    dskrat_subst(car(a), car(b), cdr(x)) |> ignore
    a = cdr(a)
    b = cdr(b)
  }
  rplaca(cdr(cddar(x)), symval(q_genvar)) |> ignore
  if memq(q_trunc, car(x)).truthy() {
    srconvert(x)
  } else {
    x
  }
}

///|
fn dskrat_subst(x : Value, y : Value, z : Value) -> Value raise {
  if atom(z) {
    z
  } else {
    if eq(y, car(z)) {
      rplaca(z, x) |> ignore
    } else {
      dskrat_subst(x, y, car(z)) |> ignore
    }
    dskrat_subst(x, y, cdr(z)) |> ignore
    z
  }
}

///|
fn displace(x : Value, y : Value) -> Value raise {
  setf_car(x, car(y)) |> ignore
  setf_cdr(x, cdr(y)) |> ignore
  x
}

///|
fn mmacro_displace(form : Value, expansion : Value) -> Value raise {
  displace(
    form,
    if atom(expansion) {
      list2(list1(q_mprogn), expansion)
    } else {
      expansion
    },
  )
}

///|
/// Does any reformatting necessary according to the current setting of
/// $MACROEXPANSION.  Note that it always returns the expansion returned by
/// displace, for future displacing.
fn mmacroexpansion_check(form : Value, expansion : Value) -> Value raise {
  let me = symval(q_d_macroexpansion)
  if me is Nil {
    if eq(caar(form), q_mmacroexpanded) {
      mmacro_displace(form, expansion)
    } else {
      expansion
    }
  } else if eq(me, q_d_expand) {
    if !eq(caar(form), q_mmacroexpanded) {
      let orig = copy1cons(form)
      displace(form, list3(list1(q_mmacroexpanded), expansion, orig)) |> ignore
    }
    expansion
  } else if eq(me, q_d_displace) {
    mmacro_displace(form, expansion)
  } else {
    mtell(list1(Str("warning: unrecognized value of 'macroexpansion'.~%")))
    |> ignore
    // Behave like the default setting (false).
    expansion
  }
}

///|
fn mmacro_apply(defn : Value, form : Value) -> Value raise {
  mmacroexpansion_check(
    form,
    if atom(defn) && !symbolp(defn) {
      // added this clause for NIL. MAPPLY doesn't really handle applying
      // interpreter closures and subrs very well.
      apply(defn, cdr(form))
    } else {
      mapply1(defn, cdr(form), caar(form), form)
    },
  )
}

///|
/// Only expands the form once.  If the form is not a valid macro form it
/// just gets returned (eq'ness is preserved).  Note that if the macros are
/// displacing, the returned form is also eq to the given form (which has
/// been bashed).
fn mmacroexpand1(form : Value) -> Value raise {
  if atom(form) ||
    atom(car(form)) ||
    memq(q_array, cdar(form)).truthy() ||
    !symbolp(mop(form)) {
    return form
  }
  let funname = mop(form)
  if eq(funname, q_mmacroexpanded) {
    return mmacroexpansion_check(form, cadr(form))
  }
  let mut macro_defn : Value = Nil
  if symval(q_d_transrun).truthy() {
    macro_defn = get(caar(form), q_translated_mmacro)
  }
  if !macro_defn.truthy() {
    macro_defn = mget(caar(form), q_mmacro)
  }
  if macro_defn.truthy() {
    mmacro_apply(macro_defn, form)
  } else {
    form
  }
}

///|
/// Expands the top-level form repeatedly until it is no longer a macro
/// form.  Has to copy the form each time because if macros are displacing
/// the form given to mmacroexpand1 will get bashed each time.
fn mmacroexpand(form : Value) -> Value raise {
  let test_form = if atom(form) { form } else { copy1cons(form) }
  let expansion = mmacroexpand1(form)
  if equal(expansion, test_form) {
    expansion
  } else {
    mmacroexpand(expansion)
  }
}

///|
/// Handles memo-ized forms.  Reformats them if $MACROEXPANSION has changed.
/// Format is ((MMACROEXPANDED) <expansion> <original form>)
fn mmacroexpanded(form : Value) -> Value raise {
  meval(mmacroexpansion_check(form, cadr(form)))
}

///|
/// The defmvar :SETTING-LIST option: an ASSIGN property allowing only the
/// listed values.
fn mlisp__setting_list(var_ : Value, possible_values : Value) -> Unit {
  putprop(
    var_,
    lfunc("setting-list", args => {
      let v = arg(args, 1)
      if member(v, possible_values) is Nil {
        mseterr(
          arg(args, 0),
          v,
          reason=Value::Str(
            format_to_string("must be one of: ~{~A~^, ~}", [
              mapcar(x => stripdollar(x), possible_values),
            ]),
          ),
        )
      } else {
        Nil
      }
    }),
    q_assign,
  )
  |> ignore
}

///|
fn init_mlisp() -> Unit raise {
  init_macdes_create_list()
  defvar_init(q_ear_lambda_expr_funs, make_hash_table(kind=HashTest::Eq))
  putprop(q_d_op_at, q_mrecord_assign, q_mset_extension_operator) |> ignore
  // Following property assignments comprise the Lisp code equivalent to
  // infix("@", 200, 201)
  putprop(q_d_op_at, q_p_op_at, q_verb) |> ignore
  let at_str : Value = Str("@")
  putprop(q_d_op_at, at_str, q_op) |> ignore
  putopr(at_str, q_d_op_at) |> ignore
  putprop(q_d_op_at, q_dimension_infix, q_dimension) |> ignore
  putprop(q_d_op_at, list1(Char('@')), q_dissym) |> ignore
  putprop(q_d_op_at, q_tex_infix, q_tex) |> ignore
  putprop(q_d_op_at, list1(Str("@")), q_texsym) |> ignore
  putprop(q_d_op_at, q_msize_infix, q_grind) |> ignore
  putprop(q_d_op_at, Fix(200L), q_lbp) |> ignore
  putprop(q_d_op_at, Fix(201L), q_rbp) |> ignore
  putprop(q_d_op_at, q_parse_infix, q_led) |> ignore
  putprop(q_p_op_at, q_dimension_infix, q_dimension) |> ignore
  putprop(q_p_op_at, list1(Char('@')), q_dissym) |> ignore
  putprop(q_p_op_at, q_d_op_at, q_noun) |> ignore
  // add MLIST to possible operators on the left hand side of an assignment
  // statement.
  putprop(q_mlist, q_mlist_assign, q_mset_extension_operator) |> ignore
  // assign properties
  putprop(q_d_all, q_neverset, q_assign) |> ignore
  // The defmspecs with properties.
  register_mspec(q_d_map, mlisp__d_map)
  register_mspec(q_d_maplist, mlisp__d_maplist)
  register_mspec(q_d_fullmap, mlisp__d_fullmap)
  register_mspec(q_d_matrixmap, mlisp__d_matrixmap)
  register_mspec(q_d_fullmapl, mlisp__d_fullmapl)
  for s in [q_d_map, q_d_maplist, q_d_fullmap, q_d_matrixmap, q_d_fullmapl, q_d_outermap, q_d_apply] {
    putprop(s, t, q_evok) |> ignore
  }
  // Float constants (read as double-floats).
  mputprop(q_d__pcte, Flo(2.718281828459045), q_d_numer) |> ignore
  mputprop(q_d__pctpi, Flo(3.141592653589793), q_d_numer) |> ignore
  mputprop(q_d__pctphi, Flo(1.618033988749895), q_d_numer) |> ignore
  mputprop(q_d__pctgamma, Flo(0.5772156649015329), q_d_numer) |> ignore
  mputprop(q_d__pctcatalan, Flo(0.915965594177219), q_d_numer) |> ignore
  mputprop(q_d_herald_package, list3(Nil, q_d_transload, t), q_d_props)
  |> ignore
  mputprop(q_d_load_package, list3(Nil, q_d_transload, t), q_d_props) |> ignore
  putprop(q_bigfloat, q_bigfloatm_star, q_mfexpr_star) |> ignore
  putprop(q_lambda, q_constlam, q_mfexpr_star) |> ignore
  // Needed by MATCOM/MATRUN.
  putprop(q_quote, lfunc("cadr", args => cadr(arg(args, 0))), q_mfexpr_star)
  |> ignore
}
