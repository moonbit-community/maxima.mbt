// Port of src/utils.lisp: general purpose Lisp utilities.

///|
fn maxima_getenv(envvar : Value) -> Value raise {
  match getenv(lstring(envvar)) {
    Some(s) => Str(s)
    None => Nil
  }
}

///|
fn bye(exit_code? : Value = Fix(0L)) -> Value raise {
  exit_process(to_int(exit_code))
  Nil
}

///|
/// F is assumed to be a function of two arguments.  It is mapped down L and
/// applied to consecutive pairs of elements of the list. Useful for
/// iterating over property lists.
fn map2c(f : Value, l : Value) -> Value raise {
  let mut lans : Value = Nil
  let mut llt = l
  while llt.truthy() {
    lans = cons(funcall(f, [car(llt), cadr(llt)]), lans)
    llt = cddr(llt)
  }
  lans
}

///|
/// Like MAPCAR, except if an application of F to any of the elements of L
/// returns NIL, then the function returns NIL immediately.
fn andmapcar(f : Value, l : Value) -> Value raise {
  let mut answer : Value = Nil
  for x in l.iter() {
    let d = funcall(f, [x])
    if d.truthy() {
      answer = cons(d, answer)
    } else {
      return Nil
    }
  }
  nreverse(answer)
}

///|
/// Returns T if either A or B is NIL, but not both.
fn xor(a : Value, b : Value) -> Value raise {
  if a is Nil && b.truthy() {
    b
  } else if b is Nil && a.truthy() {
    a
  } else {
    Nil
  }
}

///|
/// Similar to AMONG, but takes a list of objects to look for.  If any are
/// found in L, returns T.
fn amongl(x : Value, l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else if atom(l) {
    memq(l, x)
  } else {
    let r = amongl(x, car(l))
    if r.truthy() {
      r
    } else {
      amongl(x, cdr(l))
    }
  }
}

///|
/// Tests to see whether one tree is a subtree of another. If supplied, TEST
/// is used as an equality predicate (default EQL).
fn subtree_p(branch : Value, tree : Value, test_? : Value) -> Value raise {
  let tst = fn(a : Value, b : Value) -> Bool raise {
    match test_ {
      Some(f) => funcall(f, [a, b]).truthy()
      None => eql(a, b)
    }
  }
  if tst(branch, tree) {
    return t
  }
  if atom(tree) {
    return Nil
  }
  member_if_test(branch, tree, fn(x, y) raise {
    subtree_p(x, y, test_?=test_).truthy()
  })
}

///|
/// Takes a list in "alist" form and converts it to one in "property list"
/// form, i.e. ((A . B) (C . D)) --> (A B C D).
fn dot2l(l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else {
    list_star([caar(l), cdar(l), dot2l(cdr(l))])
  }
}

///|
/// (C-PUT sym value selector): make a symbol's property list look like a
/// structure. If the value to be stored is NIL, then flush the property,
/// else store the value under the appropriate property.
fn cput(base : Value, val : Value, sel : Value) -> Value raise {
  if val is Nil {
    zl_remprop(base, sel) |> ignore
    Nil
  } else {
    putprop_(base, val, sel)
  }
}

///|
/// Returns T if PREFIX is a prefix of SEQUENCE (lists or strings), using
/// TEST (default EQL). Any sequence is a prefix of itself.
fn prefixp(prefix : Value, sequence : Value, test_? : Value) -> Value raise {
  let elems = fn(s : Value) -> Array[Value] {
    match s {
      Str(str) => str.iter().map(c => Value::Char(c)).collect()
      Vec(a) =>
        match a.fill {
          Some(f) => a.data[0:f].to_array()
          None => a.data
        }
      _ => list_to_array(s)
    }
  }
  let p = elems(prefix)
  let q = elems(sequence)
  // (mismatch sequence prefix :test test)
  let n = if p.length() < q.length() { p.length() } else { q.length() }
  let mut m : Int? = None
  for i in 0..<n {
    let same = match test_ {
      Some(f) => funcall(f, [q[i], p[i]]).truthy()
      None => eql(q[i], p[i])
    }
    if !same {
      m = Some(i)
      break
    }
  }
  if m is None && p.length() != q.length() {
    m = Some(n)
  }
  match m {
    None => t
    Some(i) => lbool(i >= p.length())
  }
}
