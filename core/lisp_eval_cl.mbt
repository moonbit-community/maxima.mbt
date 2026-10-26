// Lisp evaluator: Common Lisp functions (lists, sequences, numbers,
// characters, strings, hash tables) installed in the function cells.
// They complete (and, for functions that take keyword arguments or return
// several values, replace) the basic set of core/cl_functions.mbt.

///|
/// CL symbols that the Maxima package shadows: their function cells hold
/// Maxima's own definitions, which are kept.
let le__maxima_shadowed : Set[String] = Set::from_array([
  "float", "functionp", "array", "exp", "signum", "asin", "acos", "asinh", "acosh",
  "atanh", "tanh", "cosh", "sinh", "tan", "break", "gcd", "continue", "random",
  "make-random-state", "random-state-p",
])

///|
fn le__def(name : String, f : (Array[Value]) -> Value raise) -> Unit {
  let s = sym(name)
  if le__maxima_shadowed.contains(name) && fboundp(s) {
    return
  }
  defun(s, f)
}

///|
/// Define only when the cell is empty (for names Maxima might define).
fn le__def_weak(name : String, f : (Array[Value]) -> Value raise) -> Unit {
  let s = sym(name)
  if !fboundp(s) {
    defun(s, f)
  }
}

///|
fn le__arg(a : Array[Value], i : Int) -> Value {
  if i < a.length() {
    a[i]
  } else {
    Nil
  }
}

///|
/// Keyword argument `name` among `a[start:]`.
fn le__kwarg(a : Array[Value], start : Int, name : String) -> Value? {
  let mut i = start
  while i + 1 < a.length() {
    match a[i] {
      Sym(s) if s.name == name => return Some(a[i + 1])
      _ => ()
    }
    i += 2
  }
  None
}

///|
fn le__kwarg_or(a : Array[Value], start : Int, name : String, d : Value) -> Value {
  match le__kwarg(a, start, name) {
    Some(v) => v
    None => d
  }
}

///|
/// Function designator -> callable.
fn le__call1(f : Value, x : Value) -> Value raise {
  le__funcall(f, [x])
}

///|
fn le__call2(f : Value, x : Value, y : Value) -> Value raise {
  le__funcall(f, [x, y])
}

///|
/// The :KEY function of a sequence function call.
fn le__key_fn(a : Array[Value], start : Int) -> ((Value) -> Value raise)? {
  match le__kwarg(a, start, ":key") {
    Some(Nil) | None => None
    Some(k) => Some(x => le__call1(k, x))
  }
}

///|
fn le__apply_key(k : ((Value) -> Value raise)?, x : Value) -> Value raise {
  match k {
    Some(f) => f(x)
    None => x
  }
}

///|
/// The two-argument test (:TEST / :TEST-NOT, default EQL).
fn le__test_fn(a : Array[Value], start : Int) -> (Value, Value) -> Bool raise {
  match le__kwarg(a, start, ":test") {
    Some(Nil) | None => ()
    Some(f) =>
      match f {
        Sym({ name: "eq", .. }) => return (x, y) => eq(x, y)
        Sym({ name: "eql", .. }) => return (x, y) => eql(x, y)
        Sym({ name: "equal", .. }) => return (x, y) => equal(x, y)
        _ => return (x, y) => le__call2(f, x, y).truthy()
      }
  }
  match le__kwarg(a, start, ":test-not") {
    Some(Nil) | None => ()
    Some(f) => return (x, y) => !le__call2(f, x, y).truthy()
  }
  (x, y) => eql(x, y)
}

///|
/// Elements of a sequence (list, vector, string).
fn le__seq_elems(s : Value) -> Array[Value] raise {
  match s {
    Nil => []
    Cons(_) => list_to_array(s)
    Str(str) => string_chars(str).map(c => Char(c))
    Vec(v) => {
      let n = match v.fill {
        Some(f) => f
        None => v.data.length()
      }
      v.data[0:n].to_array()
    }
    _ => {
      le__error("not a sequence: " + prin1_to_string(s)) |> ignore
      []
    }
  }
}

///|
/// A new sequence of the same kind as `like` with the given elements.
fn le__seq_like(like : Value, elems : Array[Value]) -> Value {
  match like {
    Str(_) => Str(chars_to_string(elems.map(c => if c is Char(ch) { ch } else { ' ' })))
    Vec(v) if v.elt == "character" =>
      Str(chars_to_string(elems.map(c => if c is Char(ch) { ch } else { ' ' })))
    Vec(_) => vector(elems)
    _ => list(elems)
  }
}

///|
fn le__start_end(a : Array[Value], start : Int, n : Int) -> (Int, Int) raise {
  let s = match le__kwarg(a, start, ":start") {
    Some(Nil) | None => 0
    Some(v) => to_int(v)
  }
  let e = match le__kwarg(a, start, ":end") {
    Some(Nil) | None => n
    Some(v) => to_int(v)
  }
  (s, e)
}

///|
fn le__int(v : Value) -> Int raise {
  to_int(v)
}

///|
fn le__bool(b : Bool) -> Value {
  lbool(b)
}

///|
fn le__str(v : Value) -> String raise {
  match v {
    Str(s) => s
    Sym(_) | Nil => symbol_name(v)
    Char(c) => c.to_string()
    Vec(_) => lstring(v)
    _ => {
      le__error("not a string designator: " + prin1_to_string(v)) |> ignore
      ""
    }
  }
}

///|
fn le__char(v : Value) -> Char raise {
  match v {
    Char(c) => c
    Str(s) if string_length(s) == 1 => string_chars(s)[0]
    Sym(_) =>
      match string_chars(symbol_name(v)) {
        [c] => c
        _ => {
          le__error("not a character: " + prin1_to_string(v)) |> ignore
          ' '
        }
      }
    _ => {
      le__error("not a character: " + prin1_to_string(v)) |> ignore
      ' '
    }
  }
}

///|
fn le__register_cl_lists() -> Unit {
  // c[ad]r combinations
  let combos = [
    "caar", "cadr", "cdar", "cddr", "caaar", "caadr", "cadar", "caddr", "cdaar",
    "cdadr", "cddar", "cdddr", "caaaar", "caaadr", "caadar", "caaddr", "cadaar",
    "cadadr", "caddar", "cadddr", "cdaaar", "cdaadr", "cdadar", "cdaddr", "cddaar",
    "cddadr", "cdddar", "cddddr",
  ]
  for name in combos {
    let letters = string_chars(name.substring(start=1, end=name.length() - 1))
    le__def(name, a => {
      let mut x = le__arg(a, 0)
      for k = letters.length() - 1; k >= 0; k = k - 1 {
        x = if letters[k] == 'a' { car(x) } else { cdr(x) }
      }
      x
    })
  }
  le__def("car", a => car_strict(le__arg(a, 0)))
  le__def("cdr", a => cdr_strict(le__arg(a, 0)))
  let nths = [
    "first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth", "ninth",
    "tenth",
  ]
  for i, name in nths {
    le__def(name, a => nth(i, le__arg(a, 0)))
  }
  le__def("rest", a => cdr(le__arg(a, 0)))
  le__def("endp", a => le__bool(le__arg(a, 0) is Nil))
  le__def("list-length", a => llength(le__arg(a, 0)))
  le__def("make-list", a => {
    let n = le__int(le__arg(a, 0))
    let init = le__kwarg_or(a, 1, ":initial-element", Nil)
    list(Array::make(n, init))
  })
  le__def("nreverse", a => {
    match le__arg(a, 0) {
      Vec(v) as x => {
        let n = match v.fill {
          Some(f) => f
          None => v.data.length()
        }
        let r = v.data[0:n].to_array().rev()
        for i in 0..<n {
          v.data[i] = r[i]
        }
        x
      }
      Str(s) => Str(chars_to_string(string_chars(s).rev()))
      x => nreverse(x)
    }
  })
  le__def("reverse", a => {
    match le__arg(a, 0) {
      (Vec(_) | Str(_)) as x => le__seq_like(x, le__seq_elems(x).rev())
      x => reverse(x)
    }
  })
  le__def("nconc", a => nconc_n(a))
  le__def("revappend", a => revappend(le__arg(a, 0), le__arg(a, 1)))
  le__def("nreconc", a => nreconc(le__arg(a, 0), le__arg(a, 1)))
  le__def("last", a => {
    let l = le__arg(a, 0)
    if a.length() > 1 {
      let n = le__int(a[1])
      let len = length(l)
      nthcdr(if len > n { len - n } else { 0 }, l)
    } else {
      last(l)
    }
  })
  le__def("butlast", a => butlast(le__arg(a, 0), n=if a.length() > 1 {
    le__int(a[1])
  } else {
    1
  }))
  le__def("nbutlast", a => nbutlast(le__arg(a, 0), n=if a.length() > 1 {
    le__int(a[1])
  } else {
    1
  }))
  le__def("ldiff", a => ldiff(le__arg(a, 0), le__arg(a, 1)))
  le__def("tailp", a => le__bool(tailp(le__arg(a, 0), le__arg(a, 1))))
  le__def("acons", a => cons(cons(le__arg(a, 0), le__arg(a, 1)), le__arg(a, 2)))
  le__def("pairlis", a => {
    let ks = list_to_array(le__arg(a, 0))
    let vs = list_to_array(le__arg(a, 1))
    let mut r = le__arg(a, 2)
    for k = ks.length() - 1; k >= 0; k = k - 1 {
      r = cons(cons(ks[k], if k < vs.length() { vs[k] } else { Nil }), r)
    }
    r
  })
  le__def("copy-alist", a => mapcar(
    x => match x {
      Cons({ car, cdr }) => cons(car, cdr)
      _ => x
    },
    le__arg(a, 0),
  ))
  le__def("member", a => {
    let item = le__arg(a, 0)
    let tst = le__test_fn(a, 2)
    let key = le__key_fn(a, 2)
    let mut l = le__arg(a, 1)
    while l is Cons({ car: x, cdr: rest }) {
      if tst(item, le__apply_key(key, x)) {
        return l
      }
      l = rest
    }
    Nil
  })
  le__def("member-if", a => {
    let f = le__arg(a, 0)
    let key = le__key_fn(a, 2)
    let mut l = le__arg(a, 1)
    while l is Cons({ car: x, cdr: rest }) {
      if le__call1(f, le__apply_key(key, x)).truthy() {
        return l
      }
      l = rest
    }
    Nil
  })
  le__def("member-if-not", a => {
    let f = le__arg(a, 0)
    let key = le__key_fn(a, 2)
    let mut l = le__arg(a, 1)
    while l is Cons({ car: x, cdr: rest }) {
      if !le__call1(f, le__apply_key(key, x)).truthy() {
        return l
      }
      l = rest
    }
    Nil
  })
  le__def("si::memql", a => {
    let item = le__arg(a, 0)
    let mut l = le__arg(a, 1)
    while l is Cons({ car: x, cdr: rest }) {
      if eql(item, x) {
        return l
      }
      l = rest
    }
    Nil
  })
  le__def("assoc", a => {
    let item = le__arg(a, 0)
    let tst = le__test_fn(a, 2)
    let key = le__key_fn(a, 2)
    for p in le__arg(a, 1).iter() {
      if p is Cons({ car: k, .. }) && tst(item, le__apply_key(key, k)) {
        return p
      }
    }
    Nil
  })
  le__def("assoc-if", a => {
    let f = le__arg(a, 0)
    for p in le__arg(a, 1).iter() {
      if p is Cons({ car: k, .. }) && le__call1(f, k).truthy() {
        return p
      }
    }
    Nil
  })
  le__def("rassoc", a => {
    let item = le__arg(a, 0)
    let tst = le__test_fn(a, 2)
    let key = le__key_fn(a, 2)
    for p in le__arg(a, 1).iter() {
      if p is Cons({ cdr: v, .. }) && tst(item, le__apply_key(key, v)) {
        return p
      }
    }
    Nil
  })
  le__def("rassoc-if", a => {
    let f = le__arg(a, 0)
    for p in le__arg(a, 1).iter() {
      if p is Cons({ cdr: v, .. }) && le__call1(f, v).truthy() {
        return p
      }
    }
    Nil
  })
  le__def("adjoin", a => {
    let item = le__arg(a, 0)
    let l = le__arg(a, 1)
    let tst = le__test_fn(a, 2)
    let key = le__key_fn(a, 2)
    let ki = le__apply_key(key, item)
    for x in l.iter() {
      if tst(ki, le__apply_key(key, x)) {
        return l
      }
    }
    cons(item, l)
  })
  le__def("union", a => {
    let tst = le__test_fn(a, 2)
    let key = le__key_fn(a, 2)
    let l1 = le__arg(a, 0)
    let l2 = le__arg(a, 1)
    let r = Collector::new()
    for x in l1.iter() {
      let kx = le__apply_key(key, x)
      if !l2.iter().any(y => tst(kx, le__apply_key(key, y)) catch { _ => false }) {
        r.add(x)
      }
    }
    r.append_list(copy_list(l2))
    r.result()
  })
  le__def("nunion", a => funcall(sym("union"), a))
  le__def("intersection", a => {
    let tst = le__test_fn(a, 2)
    let key = le__key_fn(a, 2)
    let l2 = le__arg(a, 1)
    let r = Collector::new()
    for x in le__arg(a, 0).iter() {
      let kx = le__apply_key(key, x)
      let mut found = false
      for y in l2.iter() {
        if tst(kx, le__apply_key(key, y)) {
          found = true
          break
        }
      }
      if found {
        r.add(x)
      }
    }
    r.result()
  })
  le__def("nintersection", a => funcall(sym("intersection"), a))
  le__def("set-difference", a => {
    let tst = le__test_fn(a, 2)
    let key = le__key_fn(a, 2)
    let l2 = le__arg(a, 1)
    let r = Collector::new()
    for x in le__arg(a, 0).iter() {
      let kx = le__apply_key(key, x)
      let mut found = false
      for y in l2.iter() {
        if tst(kx, le__apply_key(key, y)) {
          found = true
          break
        }
      }
      if !found {
        r.add(x)
      }
    }
    r.result()
  })
  le__def("nset-difference", a => funcall(sym("set-difference"), a))
  le__def("set-exclusive-or", a => {
    let d1 = funcall(sym("set-difference"), a)
    let b = a.copy()
    b[0] = le__arg(a, 1)
    b[1] = le__arg(a, 0)
    append(d1, funcall(sym("set-difference"), b))
  })
  le__def("subsetp", a => {
    let tst = le__test_fn(a, 2)
    let key = le__key_fn(a, 2)
    let l2 = le__arg(a, 1)
    for x in le__arg(a, 0).iter() {
      let kx = le__apply_key(key, x)
      let mut found = false
      for y in l2.iter() {
        if tst(kx, le__apply_key(key, y)) {
          found = true
          break
        }
      }
      if !found {
        return Nil
      }
    }
    t
  })
  le__def("getf", a => getf(le__arg(a, 0), le__arg(a, 1), default=le__arg(a, 2)))
  le__def("get-properties", a => {
    let inds = le__arg(a, 1)
    let mut p = le__arg(a, 0)
    while p is Cons({ car: k, cdr: Cons({ car: v, cdr: rest }) }) {
      if memq(k, inds).truthy() {
        return le__values([k, v, p])
      }
      p = rest
    }
    le__values([Nil, Nil, Nil])
  })
  le__def("si::putf", a => {
    // (si::putf plist ind value) => new plist
    let pl = le__arg(a, 0)
    let ind = le__arg(a, 1)
    let v = le__arg(a, 2)
    let mut p = pl
    while p is Cons({ car: k, cdr: Cons(c2) }) {
      if eq(k, ind) {
        c2.car = v
        return pl
      }
      p = c2.cdr
    }
    cons(ind, cons(v, pl))
  })
  le__def("si::remf", a => {
    let pl = le__arg(a, 0)
    let ind = le__arg(a, 1)
    let mut prev : Value = Nil
    let mut p = pl
    while p is Cons({ car: k, cdr: Cons({ cdr: rest, .. }) }) {
      if eq(k, ind) {
        if prev is Nil {
          return le__values([rest, t])
        }
        setf_cdr(cdr(prev), rest) |> ignore
        return le__values([pl, t])
      }
      prev = p
      p = rest
    }
    le__values([pl, Nil])
  })
  le__def("rplaca", a => rplaca(le__arg(a, 0), le__arg(a, 1)))
  le__def("rplacd", a => rplacd(le__arg(a, 0), le__arg(a, 1)))
  le__def("si::setcar", a => {
    rplaca(le__arg(a, 0), le__arg(a, 1)) |> ignore
    le__arg(a, 1)
  })
  le__def("si::setcdr", a => {
    rplacd(le__arg(a, 0), le__arg(a, 1)) |> ignore
    le__arg(a, 1)
  })
  le__def("si::setnth", a => {
    let c = nthcdr(le__int(le__arg(a, 0)), le__arg(a, 1))
    rplaca(c, le__arg(a, 2)) |> ignore
    le__arg(a, 2)
  })
  le__def("subst", a => {
    let new_ = le__arg(a, 0)
    let old = le__arg(a, 1)
    let tst = le__test_fn(a, 3)
    let key = le__key_fn(a, 3)
    fn walk(x : Value) -> Value raise {
      if tst(old, le__apply_key(key, x)) {
        return new_
      }
      match x {
        Cons({ car, cdr }) => {
          let a1 = walk(car)
          let d1 = walk(cdr)
          if physical_equal_value(a1, car) && physical_equal_value(d1, cdr) {
            x
          } else {
            cons(a1, d1)
          }
        }
        _ => x
      }
    }

    walk(le__arg(a, 2))
  })
  le__def("nsubst", a => funcall(sym("subst"), a))
  le__def("subst-if", a => {
    let new_ = le__arg(a, 0)
    let f = le__arg(a, 1)
    fn walk(x : Value) -> Value raise {
      if le__call1(f, x).truthy() {
        return new_
      }
      match x {
        Cons({ car, cdr }) => cons(walk(car), walk(cdr))
        _ => x
      }
    }

    walk(le__arg(a, 2))
  })
  le__def("sublis", a => {
    let alist = le__arg(a, 0)
    let tst = le__test_fn(a, 2)
    fn walk(x : Value) -> Value raise {
      for p in alist.iter() {
        if tst(car(p), x) {
          return cdr(p)
        }
      }
      match x {
        Cons({ car, cdr }) => cons(walk(car), walk(cdr))
        _ => x
      }
    }

    walk(le__arg(a, 1))
  })
  le__def("nsublis", a => funcall(sym("sublis"), a))
  le__def("copy-list", a => copy_list(le__arg(a, 0)))
  le__def("copy-tree", a => copy_tree(le__arg(a, 0)))
  // mapping
  le__def("mapcar", a => le__map_lists(a, false, false, true))
  le__def("mapc", a => {
    le__map_lists(a, false, false, false) |> ignore
    le__arg(a, 1)
  })
  le__def("mapcan", a => nconc_n(list_to_array(le__map_lists(a, false, false, true))))
  le__def("maplist", a => le__map_lists(a, true, false, true))
  le__def("mapl", a => {
    le__map_lists(a, true, false, false) |> ignore
    le__arg(a, 1)
  })
  le__def("mapcon", a => nconc_n(list_to_array(le__map_lists(a, true, false, true))))
}

///|
/// MAPCAR & co: `tails` maps over the tails, `collect` builds the list.
fn le__map_lists(
  a : Array[Value],
  tails : Bool,
  _unused : Bool,
  collect : Bool,
) -> Value raise {
  let f = le__arg(a, 0)
  let ls = a[1:].to_array()
  let r = Collector::new()
  if ls.length() == 1 {
    let mut l = ls[0]
    while l is Cons({ car: x, cdr: rest }) {
      let v = le__funcall(f, [if tails { l } else { x }])
      if collect {
        r.add(v)
      }
      l = rest
    }
    return r.result()
  }
  let cur = ls.copy()
  while cur.iter().all(l => l is Cons(_)) && cur.length() > 0 {
    let args = cur.map(l => if tails { l } else { car(l) })
    let v = le__funcall(f, args)
    if collect {
      r.add(v)
    }
    for i in 0..<cur.length() {
      cur[i] = cdr(cur[i])
    }
  }
  r.result()
}

///|
fn le__register_cl_sequences() -> Unit {
  le__def("length", a => {
    match le__arg(a, 0) {
      Str(s) => int(string_length(s))
      Vec(v) =>
        int(
          match v.fill {
            Some(f) => f
            None => v.data.length()
          },
        )
      x => llength(x)
    }
  })
  le__def("elt", a => elt(le__arg(a, 0), le__int(le__arg(a, 1))))
  le__def("si::setelt", a => {
    let s = le__arg(a, 0)
    let i = le__int(le__arg(a, 1))
    let v = le__arg(a, 2)
    match s {
      Cons(_) => rplaca(nthcdr(i, s), v) |> ignore
      _ => aset1(s, i, v) |> ignore
    }
    v
  })
  le__def("subseq", a => {
    let s = le__arg(a, 0)
    let st = le__int(le__arg(a, 1))
    match le__arg(a, 2) {
      Nil => subseq(s, st)
      e => subseq(s, st, end=le__int(e))
    }
  })
  le__def("copy-seq", a => copy_seq(le__arg(a, 0)))
  le__def("concatenate", a => {
    let ty = le__arg(a, 0)
    let elems = []
    for s in a[1:] {
      for x in le__seq_elems(s) {
        elems.push(x)
      }
    }
    match ty {
      Sym({ name: "string" | "simple-string" | "base-string", .. }) =>
        Str(chars_to_string(elems.map(c => if c is Char(ch) { ch } else { ' ' })))
      Sym({ name: "list", .. }) => list(elems)
      Cons({ car: Sym({ name: "vector" | "array" | "simple-array", .. }), .. })
      | Sym({ name: "vector" | "simple-vector", .. }) => vector(elems)
      _ =>
        if elems.iter().all(x => x is Char(_)) {
          Str(chars_to_string(elems.map(c => if c is Char(ch) { ch } else { ' ' })))
        } else {
          list(elems)
        }
    }
  })
  le__def("find", a => le__find(a, false, 0))
  le__def("find-if", a => le__find(a, false, 1))
  le__def("find-if-not", a => le__find(a, false, 2))
  le__def("position", a => le__find(a, true, 0))
  le__def("position-if", a => le__find(a, true, 1))
  le__def("position-if-not", a => le__find(a, true, 2))
  le__def("count", a => le__count(a, 0))
  le__def("count-if", a => le__count(a, 1))
  le__def("count-if-not", a => le__count(a, 2))
  le__def("remove", a => le__remove(a, 0))
  le__def("remove-if", a => le__remove(a, 1))
  le__def("remove-if-not", a => le__remove(a, 2))
  le__def("delete", a => le__remove(a, 0))
  le__def("delete-if", a => le__remove(a, 1))
  le__def("delete-if-not", a => le__remove(a, 2))
  le__def("substitute", a => le__substitute(a, 0))
  le__def("substitute-if", a => le__substitute(a, 1))
  le__def("nsubstitute", a => le__substitute(a, 0))
  le__def("nsubstitute-if", a => le__substitute(a, 1))
  le__def("remove-duplicates", a => {
    let s = le__arg(a, 0)
    let tst = le__test_fn(a, 1)
    let key = le__key_fn(a, 1)
    let from_end = le__kwarg_or(a, 1, ":from-end", Nil).truthy()
    let elems = le__seq_elems(s)
    let keep = []
    if from_end {
      for x in elems {
        let kx = le__apply_key(key, x)
        if !keep.iter().any(y => tst(le__apply_key(key, y) catch { _ => y }, kx) catch {
            _ => false
          }) {
          keep.push(x)
        }
      }
    } else {
      for i, x in elems {
        let kx = le__apply_key(key, x)
        let mut later = false
        for j in (i + 1)..<elems.length() {
          if tst(kx, le__apply_key(key, elems[j])) {
            later = true
            break
          }
        }
        if !later {
          keep.push(x)
        }
      }
    }
    le__seq_like(s, keep)
  })
  le__def("delete-duplicates", a => funcall(sym("remove-duplicates"), a))
  le__def("reduce", a => {
    let f = le__arg(a, 0)
    let s = le__arg(a, 1)
    let key = le__key_fn(a, 2)
    let from_end = le__kwarg_or(a, 2, ":from-end", Nil).truthy()
    let elems0 = le__seq_elems(s)
    let (st, en) = le__start_end(a, 2, elems0.length())
    let elems = elems0[st:en].to_array().map(x => le__apply_key(key, x) catch {
      _ => x
    })
    let init = le__kwarg(a, 2, ":initial-value")
    if from_end {
      let mut acc = match init {
        Some(v) => v
        None =>
          if elems.length() == 0 {
            return le__funcall(f, [])
          } else {
            elems.pop().unwrap()
          }
      }
      for k = elems.length() - 1; k >= 0; k = k - 1 {
        acc = le__call2(f, elems[k], acc)
      }
      acc
    } else {
      let mut i = 0
      let mut acc = match init {
        Some(v) => v
        None =>
          if elems.length() == 0 {
            return le__funcall(f, [])
          } else {
            i = 1
            elems[0]
          }
      }
      while i < elems.length() {
        acc = le__call2(f, acc, elems[i])
        i += 1
      }
      acc
    }
  })
  le__def("every", a => {
    let f = le__arg(a, 0)
    let seqs = a[1:].to_array().map(s => le__seq_elems(s) catch { _ => [] })
    let n = seqs.fold(init=if seqs.length() == 0 { 0 } else { seqs[0].length() }, (m, s) => m.min(s.length()))
    for i in 0..<n {
      if !le__funcall(f, seqs.map(s => s[i])).truthy() {
        return Nil
      }
    }
    t
  })
  le__def("some", a => {
    let f = le__arg(a, 0)
    let seqs = a[1:].to_array().map(s => le__seq_elems(s) catch { _ => [] })
    let n = seqs.fold(init=if seqs.length() == 0 { 0 } else { seqs[0].length() }, (m, s) => m.min(s.length()))
    for i in 0..<n {
      let v = le__funcall(f, seqs.map(s => s[i]))
      if v.truthy() {
        return v
      }
    }
    Nil
  })
  le__def("notany", a => le__bool(!funcall(sym("some"), a).truthy()))
  le__def("notevery", a => le__bool(!funcall(sym("every"), a).truthy()))
  le__def("map", a => {
    let ty = le__arg(a, 0)
    let f = le__arg(a, 1)
    let seqs = a[2:].to_array().map(s => le__seq_elems(s) catch { _ => [] })
    let n = seqs.fold(init=if seqs.length() == 0 { 0 } else { seqs[0].length() }, (m, s) => m.min(s.length()))
    let out = []
    for i in 0..<n {
      out.push(le__funcall(f, seqs.map(s => s[i])))
    }
    match ty {
      Nil => Nil
      Sym({ name: "list", .. }) => list(out)
      Sym({ name: "string" | "simple-string", .. }) =>
        Str(chars_to_string(out.map(c => if c is Char(ch) { ch } else { ' ' })))
      _ => vector(out)
    }
  })
  le__def("map-into", a => {
    let target = le__arg(a, 0)
    let f = le__arg(a, 1)
    let seqs = a[2:].to_array().map(s => le__seq_elems(s) catch { _ => [] })
    let tl = le__seq_elems(target).length()
    let n = seqs.fold(init=tl, (m, s) => m.min(s.length()))
    for i in 0..<n {
      let v = le__funcall(f, seqs.map(s => s[i]))
      match target {
        Cons(_) => rplaca(nthcdr(i, target), v) |> ignore
        _ => aset1(target, i, v) |> ignore
      }
    }
    target
  })
  le__def("sort", a => le__sort(a))
  le__def("stable-sort", a => le__sort(a))
  le__def("merge", a => {
    let elems = le__seq_elems(le__arg(a, 1)) + le__seq_elems(le__arg(a, 2))
    let sorted = le__sort([list(elems), le__arg(a, 3)] + a[4:].to_array())
    le__coerce(sorted, le__arg(a, 0))
  })
  le__def("fill", a => {
    let s = le__arg(a, 0)
    let v = le__arg(a, 1)
    let n = le__seq_elems(s).length()
    let (st, en) = le__start_end(a, 2, n)
    for i in st..<en {
      match s {
        Cons(_) => rplaca(nthcdr(i, s), v) |> ignore
        _ => aset1(s, i, v) |> ignore
      }
    }
    s
  })
  le__def("replace", a => {
    let s1 = le__arg(a, 0)
    let s2 = le__seq_elems(le__arg(a, 1))
    let s1n = le__seq_elems(s1).length()
    let st1 = to_int(le__kwarg_or(a, 2, ":start1", Fix(0L)))
    let en1 = match le__kwarg_or(a, 2, ":end1", Nil) {
      Nil => s1n
      v => to_int(v)
    }
    let st2 = to_int(le__kwarg_or(a, 2, ":start2", Fix(0L)))
    let en2 = match le__kwarg_or(a, 2, ":end2", Nil) {
      Nil => s2.length()
      v => to_int(v)
    }
    let n = (en1 - st1).min(en2 - st2)
    for i in 0..<n {
      let v = s2[st2 + i]
      match s1 {
        Cons(_) => rplaca(nthcdr(st1 + i, s1), v) |> ignore
        _ => aset1(s1, st1 + i, v) |> ignore
      }
    }
    s1
  })
  le__def("search", a => {
    let p = le__seq_elems(le__arg(a, 0))
    let s = le__seq_elems(le__arg(a, 1))
    let tst = le__test_fn(a, 2)
    let from_end = le__kwarg_or(a, 2, ":from-end", Nil).truthy()
    let st2 = to_int(le__kwarg_or(a, 2, ":start2", Fix(0L)))
    let en2 = match le__kwarg_or(a, 2, ":end2", Nil) {
      Nil => s.length()
      v => to_int(v)
    }
    let mut found = -1
    let mut i = st2
    while i + p.length() <= en2 {
      let mut ok = true
      for j in 0..<p.length() {
        if !tst(p[j], s[i + j]) {
          ok = false
          break
        }
      }
      if ok {
        found = i
        if !from_end {
          break
        }
      }
      i += 1
    }
    if found < 0 {
      Nil
    } else {
      int(found)
    }
  })
  le__def("mismatch", a => {
    let s1 = le__seq_elems(le__arg(a, 0))
    let s2 = le__seq_elems(le__arg(a, 1))
    let tst = le__test_fn(a, 2)
    let n = s1.length().min(s2.length())
    for i in 0..<n {
      if !tst(s1[i], s2[i]) {
        return int(i)
      }
    }
    if s1.length() == s2.length() {
      Nil
    } else {
      int(n)
    }
  })
  le__def("coerce", a => le__coerce(le__arg(a, 0), le__arg(a, 1)))
}

///|
fn le__find(a : Array[Value], want_pos : Bool, mode : Int) -> Value raise {
  let item = le__arg(a, 0)
  let elems = le__seq_elems(le__arg(a, 1))
  let tst = le__test_fn(a, 2)
  let key = le__key_fn(a, 2)
  let from_end = le__kwarg_or(a, 2, ":from-end", Nil).truthy()
  let (st, en) = le__start_end(a, 2, elems.length())
  let mut found = -1
  for i in st..<en {
    let kx = le__apply_key(key, elems[i])
    let ok = match mode {
      0 => tst(item, kx)
      1 => le__call1(item, kx).truthy()
      _ => !le__call1(item, kx).truthy()
    }
    if ok {
      found = i
      if !from_end {
        break
      }
    }
  }
  if found < 0 {
    Nil
  } else if want_pos {
    int(found)
  } else {
    elems[found]
  }
}

///|
fn le__count(a : Array[Value], mode : Int) -> Value raise {
  let item = le__arg(a, 0)
  let elems = le__seq_elems(le__arg(a, 1))
  let tst = le__test_fn(a, 2)
  let key = le__key_fn(a, 2)
  let (st, en) = le__start_end(a, 2, elems.length())
  let mut n = 0
  for i in st..<en {
    let kx = le__apply_key(key, elems[i])
    let ok = match mode {
      0 => tst(item, kx)
      1 => le__call1(item, kx).truthy()
      _ => !le__call1(item, kx).truthy()
    }
    if ok {
      n += 1
    }
  }
  int(n)
}

///|
fn le__remove(a : Array[Value], mode : Int) -> Value raise {
  let item = le__arg(a, 0)
  let s = le__arg(a, 1)
  let elems = le__seq_elems(s)
  let tst = le__test_fn(a, 2)
  let key = le__key_fn(a, 2)
  let (st, en) = le__start_end(a, 2, elems.length())
  let count = match le__kwarg(a, 2, ":count") {
    Some(Nil) | None => -1
    Some(v) => to_int(v)
  }
  let mut removed = 0
  let keep = []
  for i, x in elems {
    if i >= st && i < en && (count < 0 || removed < count) {
      let kx = le__apply_key(key, x)
      let ok = match mode {
        0 => tst(item, kx)
        1 => le__call1(item, kx).truthy()
        _ => !le__call1(item, kx).truthy()
      }
      if ok {
        removed += 1
        continue
      }
    }
    keep.push(x)
  }
  if removed == 0 {
    return s
  }
  le__seq_like(s, keep)
}

///|
fn le__substitute(a : Array[Value], mode : Int) -> Value raise {
  let new_ = le__arg(a, 0)
  let item = le__arg(a, 1)
  let s = le__arg(a, 2)
  let tst = le__test_fn(a, 3)
  let key = le__key_fn(a, 3)
  let out = le__seq_elems(s).map(x => {
    let kx = le__apply_key(key, x)
    let ok = match mode {
      0 => tst(item, kx)
      _ => le__call1(item, kx).truthy()
    }
    if ok {
      new_
    } else {
      x
    }
  })
  le__seq_like(s, out)
}

///|
fn le__sort(a : Array[Value]) -> Value raise {
  let s = le__arg(a, 0)
  let pred = le__arg(a, 1)
  let key = le__key_fn(a, 2)
  let lt = (x : Value, y : Value) => le__call2(
      pred,
      le__apply_key(key, x),
      le__apply_key(key, y),
    ).truthy()
  match s {
    Vec(v) => {
      let n = match v.fill {
        Some(f) => f
        None => v.data.length()
      }
      let sorted = sort_array(v.data[0:n].to_array(), lt)
      for i in 0..<n {
        v.data[i] = sorted[i]
      }
      s
    }
    Str(_) => le__seq_like(s, sort_array(le__seq_elems(s), lt))
    _ => sort_list(s, lt)
  }
}

///|
fn le__coerce(x : Value, ty : Value) -> Value raise {
  let tname = match ty {
    Sym(s) => s.name
    Cons({ car: Sym(s), .. }) => s.name
    _ => ""
  }
  match tname {
    "list" => list(le__seq_elems(x))
    "string" | "simple-string" | "base-string" =>
      match x {
        Str(_) => x
        _ => le__seq_like(Str(""), le__seq_elems(x))
      }
    "vector" | "simple-vector" | "array" | "simple-array" => vector(le__seq_elems(x))
    "float" | "double-float" | "single-float" | "flonum" | "long-float" | "short-float" | "real" =>
      if complexp(x) {
        x
      } else {
        lfloat(x)
      }
    "character" => Char(le__char(x))
    "complex" => if complexp(x) { x } else { complex(x) }
    "function" =>
      match x {
        Cons(_) => le__closure_of_lambda(x, Top, None)
        Sym(_) => symbol_function(x)
        _ => x
      }
    "t" | "number" | "integer" | "rational" => x
    _ => x
  }
}

///|
fn le__fdiv(
  a : Array[Value],
  op : (Value, Value?) -> (Value, Value) raise,
  float_q : Bool,
) -> Value raise {
  let x = le__arg(a, 0)
  let (q, r) = op(x, if a.length() > 1 { Some(a[1]) } else { None })
  let q2 = if float_q { lfloat(q) } else { q }
  le__values([q2, r])
}

///|
fn le__register_cl_numbers() -> Unit {
  le__def("floor", a => le__fdiv(a, (x, b) => num_floor(x, b?), false))
  le__def("ceiling", a => le__fdiv(a, (x, b) => num_ceiling(x, b?), false))
  le__def("truncate", a => le__fdiv(a, (x, b) => num_truncate(x, b?), false))
  le__def("round", a => le__fdiv(a, (x, b) => num_round(x, b?), false))
  le__def("ffloor", a => le__fdiv(a, (x, b) => num_floor(x, b?), true))
  le__def("fceiling", a => le__fdiv(a, (x, b) => num_ceiling(x, b?), true))
  le__def("ftruncate", a => le__fdiv(a, (x, b) => num_truncate(x, b?), true))
  le__def("fround", a => le__fdiv(a, (x, b) => num_round(x, b?), true))
  le__def("/=", a => {
    for i in 0..<a.length() {
      for j in (i + 1)..<a.length() {
        if num_eq(a[i], a[j]) {
          return Nil
        }
      }
    }
    t
  })
  le__def("lcm", a => {
    let mut acc : Value = Fix(1L)
    for x in a {
      acc = num_lcm(acc, x)
    }
    acc
  })
  le__def("lognot", a => lognot(le__arg(a, 0)))
  le__def("logcount", a => int(logcount(le__arg(a, 0))))
  le__def("logtest", a => le__bool(!zerop(logand(le__arg(a, 0), le__arg(a, 1)))))
  le__def("logandc1", a => logand(lognot(le__arg(a, 0)), le__arg(a, 1)))
  le__def("logandc2", a => logand(le__arg(a, 0), lognot(le__arg(a, 1))))
  le__def("logeqv", a => lognot(logxor(le__arg(a, 0), le__arg(a, 1))))
  le__def("conjugate", a => conjugate(le__arg(a, 0)))
  le__def("phase", a => phase(le__arg(a, 0)))
  le__def("cis", a => cis(le__arg(a, 0)))
  le__def("asin", a => lasin(le__arg(a, 0)))
  le__def("acos", a => lacos(le__arg(a, 0)))
  le__def("sinh", a => lsinh(le__arg(a, 0)))
  le__def("cosh", a => lcosh(le__arg(a, 0)))
  le__def("tanh", a => ltanh(le__arg(a, 0)))
  le__def("asinh", a => lasinh(le__arg(a, 0)))
  le__def("acosh", a => lacosh(le__arg(a, 0)))
  le__def("atanh", a => latanh(le__arg(a, 0)))
  le__def("signum", a => signum(le__arg(a, 0)))
  le__def("exp", a => lexp(le__arg(a, 0)))
  le__def("tan", a => ltan(le__arg(a, 0)))
  le__def("float", a => {
    let x = le__arg(a, 0)
    if floatp(x) {
      x
    } else {
      lfloat(x)
    }
  })
  le__def("decode-float", a => {
    let (m, e, s) = decode_float(to_double(le__arg(a, 0)))
    le__values([Flo(m), int(e), Flo(s)])
  })
  le__def("integer-decode-float", a => {
    let (m, e, s) = integer_decode_float(to_double(le__arg(a, 0)))
    le__values([from_big(m), int(e), int(s)])
  })
  le__def("scale-float", a => Flo(
    scale_float(to_double(le__arg(a, 0)), le__int(le__arg(a, 1))),
  ))
  le__def("float-sign", a => {
    let x = to_double(le__arg(a, 0))
    let m = if a.length() > 1 { to_double(a[1]).abs() } else { 1.0 }
    Flo(if dsignbit(x) { -m } else { m })
  })
  le__def("float-digits", _ => Fix(53L))
  le__def("float-precision", a => if to_double(le__arg(a, 0)) == 0.0 {
    Fix(0L)
  } else {
    Fix(53L)
  })
  le__def("float-radix", _ => Fix(2L))
  le__def("numberp", a => le__bool(numberp(le__arg(a, 0))))
  le__def("integerp", a => le__bool(integerp(le__arg(a, 0))))
  le__def("fixnump", a => le__bool(fixnump(le__arg(a, 0))))
  le__def("bignump", a => le__bool(bignump(le__arg(a, 0))))
  le__def("parse-integer", a => {
    let s = le__str(le__arg(a, 0))
    let chars = string_chars(s)
    let (st, en) = le__start_end(a, 1, chars.length())
    let radix = le__int(le__kwarg_or(a, 1, ":radix", Fix(10L)))
    let junk = le__kwarg_or(a, 1, ":junk-allowed", Nil).truthy()
    let sub = chars_to_string(chars[st:en].to_array())
    match parse_integer(sub, radix~) {
      Some(n) => le__values([n, int(en)])
      None =>
        if junk {
          // the longest valid prefix (after whitespace)
          let mut i = st
          while i < en && is_space_char(chars[i]) {
            i += 1
          }
          let start = i
          if i < en && (chars[i] == '+' || chars[i] == '-') {
            i += 1
          }
          while i < en && digit_char_p(chars[i], radix~) is Some(_) {
            i += 1
          }
          match parse_integer(chars_to_string(chars[start:i].to_array()), radix~) {
            Some(n) => le__values([n, int(i)])
            None => le__values([Nil, int(i)])
          }
        } else {
          raise LispError::Condition(
            intern("parse-error"),
            "junk in string \"" + s + "\"",
            Str(s),
          )
        }
    }
  })
  le__def("random", a => {
    let lim = le__arg(a, 0)
    le__random(lim)
  })
  le__def("byte", a => cons(le__arg(a, 0), le__arg(a, 1)))
  le__def("ldb", a => {
    let size = le__int(car(le__arg(a, 0)))
    let pos = le__int(cdr(le__arg(a, 0)))
    logand(ash(le__arg(a, 1), -pos), num_sub(ash(Fix(1L), size), Fix(1L)))
  })
  le__def("boole", a => {
    let op = le__int(le__arg(a, 0))
    let x = le__arg(a, 1)
    let y = le__arg(a, 2)
    match op {
      1 => logand(x, y)
      6 => logxor(x, y)
      7 => logior(x, y)
      _ => logand(x, y)
    }
  })
}

///|
fn is_space_char(c : Char) -> Bool {
  c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

///|
let le__rand_state : Ref[UInt64] = Ref(0x2545F4914F6CDD1DUL)

///|
fn le__rand_next() -> UInt64 {
  let mut x = le__rand_state.val
  x = x ^ (x << 13)
  x = x ^ (x >> 7)
  x = x ^ (x << 17)
  le__rand_state.val = x
  x
}

///|
fn le__random(lim : Value) -> Value raise {
  match lim {
    Flo(d) => Flo((le__rand_next() >> 11).to_double() / 9007199254740992.0 * d)
    Fix(n) if n > 0L => Fix((le__rand_next() % n.reinterpret_as_uint64()).reinterpret_as_int64())
    Big(_) => {
      // combine 62-bit chunks
      let mut acc : Value = Fix(0L)
      for _ in 0..<(integer_length(lim) / 60 + 2) {
        acc = num_add(ash(acc, 60), Fix((le__rand_next() >> 4).reinterpret_as_int64()))
      }
      num_mod(acc, lim)
    }
    _ => le__error("random: invalid limit " + prin1_to_string(lim))
  }
}

///|
fn le__char_cmp(a : Array[Value], f : (Int, Int) -> Bool, fold : Bool) -> Value raise {
  for i in 0..<(a.length() - 1) {
    let mut x = le__char(a[i])
    let mut y = le__char(a[i + 1])
    if fold {
      x = char_upcase(x)
      y = char_upcase(y)
    }
    if !f(x.to_int(), y.to_int()) {
      return Nil
    }
  }
  t
}

///|
fn le__str_cmp(
  a : Array[Value],
  fold : Bool,
  ok : (Int) -> Bool,
  want_index : Bool,
) -> Value raise {
  let s1 = string_chars(le__str(le__arg(a, 0)))
  let s2 = string_chars(le__str(le__arg(a, 1)))
  let st1 = to_int(le__kwarg_or(a, 2, ":start1", Fix(0L)))
  let en1 = match le__kwarg_or(a, 2, ":end1", Nil) {
    Nil => s1.length()
    v => to_int(v)
  }
  let st2 = to_int(le__kwarg_or(a, 2, ":start2", Fix(0L)))
  let en2 = match le__kwarg_or(a, 2, ":end2", Nil) {
    Nil => s2.length()
    v => to_int(v)
  }
  let mut i = st1
  let mut j = st2
  let mut cmp = 0
  while true {
    if i >= en1 || j >= en2 {
      cmp = if i >= en1 && j >= en2 {
        0
      } else if i >= en1 {
        -1
      } else {
        1
      }
      break
    }
    let mut c1 = s1[i]
    let mut c2 = s2[j]
    if fold {
      c1 = char_upcase(c1)
      c2 = char_upcase(c2)
    }
    if c1 != c2 {
      cmp = if c1 < c2 { -1 } else { 1 }
      break
    }
    i += 1
    j += 1
  }
  if ok(cmp) {
    if want_index {
      int(i)
    } else {
      t
    }
  } else {
    Nil
  }
}

///|
fn le__string_trim_bag(bag : Value) -> String raise {
  match bag {
    Str(s) => s
    _ => chars_to_string(le__seq_elems(bag).map(c => le__char(c) catch { _ => ' ' }))
  }
}

///|
fn le__register_cl_strings() -> Unit {
  le__def("char-code", a => int(char_code(le__char(le__arg(a, 0)))))
  le__def("char-int", a => int(char_code(le__char(le__arg(a, 0)))))
  le__def("code-char", a => Char(code_char(le__int(le__arg(a, 0)))))
  le__def("char-upcase", a => Char(char_upcase(le__char(le__arg(a, 0)))))
  le__def("char-downcase", a => Char(char_downcase(le__char(le__arg(a, 0)))))
  le__def("upper-case-p", a => le__bool(upper_case_p(le__char(le__arg(a, 0)))))
  le__def("lower-case-p", a => le__bool(lower_case_p(le__char(le__arg(a, 0)))))
  le__def("both-case-p", a => le__bool(both_case_p(le__char(le__arg(a, 0)))))
  le__def("alpha-char-p", a => le__bool(alpha_char_p(le__char(le__arg(a, 0)))))
  le__def("alphanumericp", a => le__bool(alphanumericp(le__char(le__arg(a, 0)))))
  le__def("graphic-char-p", a => {
    let c = le__char(le__arg(a, 0))
    le__bool(c.to_int() >= 32 && c.to_int() != 127)
  })
  le__def("standard-char-p", a => {
    let c = le__char(le__arg(a, 0))
    le__bool((c.to_int() >= 32 && c.to_int() < 127) || c == '\n')
  })
  le__def("digit-char-p", a => {
    let radix = if a.length() > 1 { le__int(a[1]) } else { 10 }
    match digit_char_p(le__char(le__arg(a, 0)), radix~) {
      Some(d) => int(d)
      None => Nil
    }
  })
  le__def("digit-char", a => {
    let d = le__int(le__arg(a, 0))
    let radix = if a.length() > 1 { le__int(a[1]) } else { 10 }
    if d < 0 || d >= radix {
      Nil
    } else if d < 10 {
      Char(code_char('0'.to_int() + d))
    } else {
      Char(code_char('A'.to_int() + d - 10))
    }
  })
  le__def("char=", a => le__char_cmp(a, (x, y) => x == y, false))
  le__def("char/=", a => le__char_cmp(a, (x, y) => x != y, false))
  le__def("char<", a => le__char_cmp(a, (x, y) => x < y, false))
  le__def("char>", a => le__char_cmp(a, (x, y) => x > y, false))
  le__def("char<=", a => le__char_cmp(a, (x, y) => x <= y, false))
  le__def("char>=", a => le__char_cmp(a, (x, y) => x >= y, false))
  le__def("char-equal", a => le__char_cmp(a, (x, y) => x == y, true))
  le__def("char-not-equal", a => le__char_cmp(a, (x, y) => x != y, true))
  le__def("char-lessp", a => le__char_cmp(a, (x, y) => x < y, true))
  le__def("char-greaterp", a => le__char_cmp(a, (x, y) => x > y, true))
  le__def("char-name", a => {
    let c = le__char(le__arg(a, 0))
    match c {
      ' ' => Str("Space")
      '\n' => Str("Newline")
      '\t' => Str("Tab")
      '\r' => Str("Return")
      '\u{0C}' => Str("Page")
      '\u{08}' => Str("Backspace")
      '\u{7F}' => Str("Rubout")
      '\u{00}' => Str("Nul")
      _ => Nil
    }
  })
  le__def("name-char", a => {
    let n = string_downcase(le__str(le__arg(a, 0)))
    match n {
      "space" => Char(' ')
      "newline" | "linefeed" => Char('\n')
      "tab" => Char('\t')
      "return" => Char('\r')
      "page" => Char('\u{0C}')
      "backspace" => Char('\u{08}')
      "rubout" => Char('\u{7F}')
      "nul" | "null" => Char('\u{00}')
      _ => Nil
    }
  })
  le__def("character", a => Char(le__char(le__arg(a, 0))))
  le__def("characterp", a => le__bool(characterp(le__arg(a, 0))))
  le__def("stringp", a => le__bool(stringp(le__arg(a, 0))))
  le__def("simple-string-p", a => le__bool(stringp(le__arg(a, 0))))
  le__def("string", a => {
    match le__arg(a, 0) {
      Str(_) as s => s
      Char(c) => Str(c.to_string())
      x => Str(le__str(x))
    }
  })
  le__def("string=", a => le__str_cmp(a, false, c => c == 0, false))
  le__def("string/=", a => le__str_cmp(a, false, c => c != 0, true))
  le__def("string<", a => le__str_cmp(a, false, c => c < 0, true))
  le__def("string>", a => le__str_cmp(a, false, c => c > 0, true))
  le__def("string<=", a => le__str_cmp(a, false, c => c <= 0, true))
  le__def("string>=", a => le__str_cmp(a, false, c => c >= 0, true))
  le__def("string-equal", a => le__str_cmp(a, true, c => c == 0, false))
  le__def("string-not-equal", a => le__str_cmp(a, true, c => c != 0, true))
  le__def("string-lessp", a => le__str_cmp(a, true, c => c < 0, true))
  le__def("string-greaterp", a => le__str_cmp(a, true, c => c > 0, true))
  le__def("string-not-greaterp", a => le__str_cmp(a, true, c => c <= 0, true))
  le__def("string-not-lessp", a => le__str_cmp(a, true, c => c >= 0, true))
  le__def("string-upcase", a => {
    let cs = string_chars(le__str(le__arg(a, 0)))
    let (st, en) = le__start_end(a, 1, cs.length())
    for i in st..<en {
      cs[i] = char_upcase(cs[i])
    }
    Str(chars_to_string(cs))
  })
  le__def("string-downcase", a => {
    let cs = string_chars(le__str(le__arg(a, 0)))
    let (st, en) = le__start_end(a, 1, cs.length())
    for i in st..<en {
      cs[i] = char_downcase(cs[i])
    }
    Str(chars_to_string(cs))
  })
  le__def("string-capitalize", a => {
    let cs = string_chars(le__str(le__arg(a, 0)))
    let mut in_word = false
    for i in 0..<cs.length() {
      let c = cs[i]
      if alphanumericp(c) {
        cs[i] = if in_word { char_downcase(c) } else { char_upcase(c) }
        in_word = true
      } else {
        in_word = false
      }
    }
    Str(chars_to_string(cs))
  })
  le__def("nstring-upcase", a => funcall(sym("string-upcase"), a))
  le__def("nstring-downcase", a => funcall(sym("string-downcase"), a))
  le__def("string-trim", a => Str(
    string_trim(le__string_trim_bag(le__arg(a, 0)), le__str(le__arg(a, 1))),
  ))
  le__def("string-left-trim", a => Str(
    string_left_trim(le__string_trim_bag(le__arg(a, 0)), le__str(le__arg(a, 1))),
  ))
  le__def("string-right-trim", a => Str(
    string_right_trim(le__string_trim_bag(le__arg(a, 0)), le__str(le__arg(a, 1))),
  ))
  le__def("make-string", a => {
    let n = le__int(le__arg(a, 0))
    let c = match le__kwarg(a, 1, ":initial-element") {
      Some(Char(c)) => c
      _ => ' '
    }
    Str(chars_to_string(Array::make(n, c)))
  })
  le__def("char", a => {
    match le__arg(a, 0) {
      Str(s) => Char(char_at(s, le__int(le__arg(a, 1))))
      x => aref1(x, le__int(le__arg(a, 1)))
    }
  })
  le__def("schar", a => funcall(sym("char"), a))
  le__def("string-to-list", a => string_to_char_list(le__str(le__arg(a, 0))))
}

///|
fn le__hash_test(v : Value) -> HashTest {
  match v {
    Sym({ name: "eq", .. }) => HashTest::Eq
    Sym({ name: "equal", .. }) => HashTest::Equal
    Sym({ name: "equalp", .. }) => HashTest::Equalp
    Func({ name: "eq", .. }) => HashTest::Eq
    Func({ name: "equal", .. }) => HashTest::Equal
    Func({ name: "equalp", .. }) => HashTest::Equalp
    _ => HashTest::Eql
  }
}

///|
fn le__register_cl_hash() -> Unit {
  le__def("make-hash-table", a => make_hash_table(
    kind=le__hash_test(le__kwarg_or(a, 0, ":test", Nil)),
  ))
  le__def("gethash", a => {
    let (v, found) = gethash2(le__arg(a, 0), le__arg(a, 1))
    if found {
      le__values([v, t])
    } else {
      le__values([le__arg(a, 2), Nil])
    }
  })
  le__def("si::puthash", a => {
    // (si::puthash key table [default] value)
    let v = a[a.length() - 1]
    sethash(le__arg(a, 0), le__arg(a, 1), v) |> ignore
    v
  })
  le__def("remhash", a => le__bool(remhash(le__arg(a, 0), le__arg(a, 1))))
  le__def("clrhash", a => clrhash(le__arg(a, 0)))
  le__def("maphash", a => {
    let f = le__arg(a, 0)
    maphash((k, v) => le__call2(f, k, v) |> ignore, le__arg(a, 1))
    Nil
  })
  le__def("hash-table-count", a => int(hash_table_count(le__arg(a, 0))))
  le__def("hash-table-p", a => le__bool(hash_table_p(le__arg(a, 0))))
  le__def("hash-table-test", a => match le__arg(a, 0) {
    Hash(h) =>
      sym(
        match h.kind {
          Eq => "eq"
          Eql => "eql"
          Equal => "equal"
          Equalp => "equalp"
        },
      )
    _ => Nil
  })
  le__def("hash-table-size", a => int(hash_table_count(le__arg(a, 0))))
  le__def("si::hash-table-pairs", a => match le__arg(a, 0) {
    Hash(h) => list(h.entries().map(e => cons(e.0, e.1)))
    _ => Nil
  })
  le__def("sxhash", a => int(hash_equal(le__arg(a, 0))))
}
