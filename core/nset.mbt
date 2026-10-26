// Port of src/nset.lisp: a Maxima set package (Stavros Macrakis and
// Barton Willis).

///|
fn nset__set_header() -> Value {
  list2(q_d_set, q_simp)
}

///|
fn nset__mk_set(elems : Value) -> Value {
  cons(nset__set_header(), elems)
}

///|
fn require_set(x : Value, context_string : Value) -> Value raise {
  if d_setp(x).truthy() {
    cdr(x)
  } else {
    merr("~:M: argument must be a set; found: ~:M", [context_string, x])
  }
}

///|
/// If x is a Maxima list, return a Lisp list of its members; otherwise,
/// signal an error.
fn require_list(x : Value, context_string : Value) -> Value raise {
  if d_listp(x).truthy() {
    cdr(x)
  } else {
    merr("~:M: argument must be a list; found: ~:M", [context_string, x])
  }
}

///|
/// If x is a Maxima list or set, return a Lisp list of its members;
/// otherwise, signal an error.
fn require_list_or_set(x : Value, context_string : Value) -> Value raise {
  if d_listp(x).truthy() || d_setp(x).truthy() {
    cdr(x)
  } else {
    merr("~:M: argument must be a list or a set; found: ~:M", [
      context_string, x,
    ])
  }
}

///|
fn nset__sort(l : Value) -> Value raise {
  sort_list(l, (a, b) => d_orderlessp(a, b).truthy())
}

///|
/// When a is a list, return a list of the unique elements of a.
fn d_unique(x : Value) -> Value raise {
  if d_listp(x).truthy() {
    cons(list1(q_mlist), sorted_remove_duplicates(nset__sort(copy_list(cdr(x)))))
  } else {
    x
  }
}

///|
fn d_setify(a : Value) -> Value raise {
  simplifya(cons(list1(q_d_set), copy_list(require_list(a, q_d_setify))), t)
}

///|
fn d_fullsetify(a : Value) -> Value raise {
  if d_listp(a).truthy() {
    cons(list1(q_d_set), mapcar(x => d_fullsetify(x), cdr(a)))
  } else {
    a
  }
}

///|
fn d_listify(a : Value) -> Value raise {
  if d_setp(a).truthy() {
    simplifya(cons(list1(q_mlist), cdr(a)), t)
  } else {
    a
  }
}

///|
fn d_full_listify(a : Value) -> Value raise {
  let a = d_ratdisrep(a)
  if d_mapatom(a).truthy() {
    a
  } else if d_setp(a).truthy() {
    simplify(cons(list1(q_mlist), mapcar(x => d_full_listify(x), cdr(a))))
  } else {
    simplify(cons(car(a), mapcar(x => d_full_listify(x), cdr(a))))
  }
}

///|
/// Simplify a set.
fn simp_set(a : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let mut a = if z.truthy() {
    copy_list(cdr(a))
  } else {
    mapcar(x => simplifya(x, Nil), cdr(a))
  }
  a = sorted_remove_duplicates(nset__sort(a))
  nset__mk_set(a)
}

///|
/// Return true iff a is an empty set or list.
fn d_emptyp(a : Value) -> Value raise {
  let v = like(a, list1(list1(q_d_set)))
  if v.truthy() {
    return v
  }
  let v = like(a, list1(list1(q_mlist)))
  if v.truthy() {
    return v
  }
  lbool(
    d_matrixp(a).truthy() && every(x => d_emptyp(x).truthy(), margs(a)),
  )
}

///|
/// Return true iff the operator of a is set.
fn d_setp(a : Value) -> Value raise {
  lbool(consp(a) && consp(car(a)) && eq(caar(a), q_d_set))
}

///|
/// Return the cardinality of a set. This function works even when $simp is
/// false.
fn d_cardinality(a : Value) -> Value raise {
  if symval(q_d_simp).truthy() {
    int(length(require_set(a, q_d_cardinality)))
  } else {
    with_special(q_d_simp, t, () => d_cardinality(simplify(a)))
  }
}

///|
fn d_subsetp(a : Value, b : Value) -> Value raise {
  let a = require_set(a, q_d_subsetp)
  let b = require_set(b, q_d_subsetp)
  if length(a) <= length(b) {
    set_subsetp(a, b)
  } else {
    Nil
  }
}

///|
fn d_setequalp(a : Value, b : Value) -> Value raise {
  let a = require_set(a, q_d_setequalp)
  let b = require_set(b, q_d_setequalp)
  if length(a) != length(b) {
    return Nil
  }
  let mut p = a
  let mut q = b
  while !(p is Nil) && !(q is Nil) {
    if !like(car(p), car(q)).truthy() {
      return Nil
    }
    p = cdr(p)
    q = cdr(q)
  }
  t
}

///|
/// Adjoin x to the list or set a and return a set.
fn d_adjoin(x : Value, a : Value) -> Value raise {
  let mut a = require_set(a, q_d_adjoin)
  let (f, i, b) = b_search_expr(x, a, int(0), int(length(a)))
  if !f.truthy() {
    a = prefixconc(a, i, cons(x, b))
  }
  nset__mk_set(a)
}

///|
fn d_disjoin(x : Value, a : Value) -> Value raise {
  let a = require_set(a, q_d_disjoin)
  let (f, i, b) = b_search_expr(x, a, int(0), int(length(a)))
  nset__mk_set(if f.truthy() { prefixconc(a, i, b) } else { a })
}

///|
/// (prefixconc l len rest) is equivalent to (nconc (subseq l 0 len) rest)
fn prefixconc(l : Value, len : Value, rest_ : Value) -> Value raise {
  let mut res : Value = Nil
  let mut i = to_int(len)
  let mut l = l
  while i != 0 {
    res = cons(car(l), res)
    i -= 1
    l = cdr(l)
  }
  nreconc(res, rest_)
}

///|
fn d_union(a : Value) -> Value raise {
  let mut acc : Value = Nil
  for ai in a.iter() {
    acc = set_union(acc, require_set(ai, q_d_union))
  }
  nset__mk_set(acc)
}

///|
fn d_setdifference(a : Value, b : Value) -> Value raise {
  nset__mk_set(
    sset_difference(
      require_set(a, q_d_setdifference),
      require_set(b, q_d_setdifference),
    ),
  )
}

///|
fn d_intersection(a : Value, b : Value) -> Value raise {
  let mut acc = require_set(a, q_d_intersection)
  if consp(b) {
    for bi in b.iter() {
      acc = set_intersect(acc, require_set(bi, q_d_intersection))
    }
  }
  nset__mk_set(acc)
}

///|
fn d_intersect(a : Value, b : Value) -> Value raise {
  d_intersection(a, b)
}

///|
fn d_elementp(x : Value, a : Value) -> Value raise {
  let a = require_set(a, q_d_elementp)
  b_search_expr(x, a, int(0), int(length(a))).0
}

///|
fn d_disjointp(a : Value, b : Value) -> Value raise {
  let a = require_set(a, q_d_disjointp)
  let b = require_set(b, q_d_disjointp)
  set_disjointp(a, b)
}

///|
fn d_subset(a : Value, f : Value) -> Value raise {
  let a = require_set(a, q_d_subset)
  let mut acc : Value = Nil
  for x in a.iter() {
    let b = mfuncall(f, list1(x))
    if eq(t, b) {
      acc = cons(x, acc)
    } else if !(b is Nil || eq(b, q_d_unknown)) {
      merr("subset: ~:M(~:M) evaluates to a non-boolean.", [f, x]) |> ignore
    }
  }
  nset__mk_set(nreverse(acc))
}

///|
fn d_partition_set(a : Value, f : Value) -> Value raise {
  let a = require_set(a, q_d_partition_set)
  let mut t_acc : Value = Nil
  let mut f_acc : Value = Nil
  for x in a.iter() {
    let b = mfuncall(f, list1(x))
    if eq(t, b) {
      t_acc = cons(x, t_acc)
    } else if b is Nil || eq(b, q_d_unknown) {
      f_acc = cons(x, f_acc)
    } else {
      merr("partition_set: ~:M(~:M) evaluates to a non-boolean.", [f, x])
      |> ignore
    }
  }
  list3(
    list2(q_mlist, q_simp),
    nset__mk_set(nreverse(f_acc)),
    nset__mk_set(nreverse(t_acc)),
  )
}

///|
fn d_symmdifference(l : Value) -> Value raise {
  let mut acc : Value = Nil
  for lk in l.iter() {
    acc = set_symmetric_difference(acc, require_set(lk, q_d_symmdifference))
  }
  nset__mk_set(acc)
}

///|
/// Return {x | x in exactly one set l1, l2, ...}
fn d_in_exactly_one(l : Value) -> Value raise {
  let mut u : Value = Nil
  let mut r : Value = Nil
  for lk0 in l.iter() {
    let lk = require_set(lk0, q_d_in_exactly_one)
    r = set_union(r, set_intersect(u, lk))
    u = set_union(u, lk)
  }
  nset__mk_set(sset_difference(u, r))
}

///|
fn d_powerset(a : Value, k? : Value = Nil) -> Value raise {
  let a = require_set(a, Str("powerset"))
  if k is Nil {
    cons(nset__set_header(), mapcar(s => nset__mk_set(s), power_set(a)))
  } else if integerp(k) {
    powerset_subset(a, k, int(length(a)))
  } else {
    merr("The second argument to powerset must be an integer; found ~:M", [k])
  }
}

///|
fn power_set(a : Value) -> Value raise {
  if a is Nil {
    list1(Nil)
  } else {
    let x = car(a)
    let b = power_set(cdr(a))
    append_n([list1(Nil), mapcar(u => cons(x, u), b), cdr(b)])
  }
}

///|
fn powerset_subset(a : Value, k : Value, n : Value) -> Value raise {
  let mut s : Value = Nil
  let mut acc : Value = Nil
  let ki = to_int(k)
  if ki == 0 {
    acc = cons(list1(nset__set_header()), acc)
  } else if num_le(k, n) {
    for i in 0..<ki {
      s = cons(int(i), s)
    }
    s = nreverse(s)
    while !(s is Nil) {
      let mut b : Value = Nil
      for i in 0..<ki {
        b = cons(nth(to_int(nth(i, s)), a), b)
      }
      acc = cons(nset__mk_set(nreverse(b)), acc)
      s = ksubset_lex_successor(s, k, n)
    }
  }
  nset__mk_set(nreverse(acc))
}

///|
/// Based on Algorithm 2.6 "Combinatorial Algorithms Generation,
/// Enumeration, and Search," CRC Press, 1999 by Donald Kreher and Douglas
/// Stinson.
fn ksubset_lex_successor(s : Value, k : Value, n : Value) -> Value raise {
  let u = copy_list(s)
  let k = to_int(k)
  let n = to_int(n)
  let mut i = k - 1
  let mut si = n - k
  while i >= 0 && to_int(nth(i, s)) == si + i {
    i -= 1
  }
  if i < 0 {
    Nil
  } else {
    let mut j = i
    si = 1 + (to_int(nth(i, s)) - i)
    while j < k {
      rplaca(nthcdr(j, u), int(si + j)) |> ignore
      j += 1
    }
    u
  }
}

///|
fn d_permutations(a : Value) -> Value raise {
  let a = if d_listp(a).truthy() {
    nset__sort(copy_list(cdr(a)))
  } else {
    require_set(a, q_d_permutations)
  }
  let n = length(a)
  let mut p = make_array([n + 1], initial=int(0))
  let r = make_array([n + 1], initial=int(0))
  let b = make_array([n + 1], initial=int(0))
  let mut acc : Value = Nil
  let need_to_simp = length(a) != length(sorted_remove_duplicates(copy_list(a)))
  for i in 0..<(n + 1) {
    aset1(p, i, int(i)) |> ignore
  }
  for i in 0..<n {
    aset1(b, i + 1, nth(i, a)) |> ignore
  }
  if !(a is Nil) {
    while !(p is Nil) {
      let mut i = 1
      let mut q : Value = Nil
      while i <= n {
        q = cons(aref1(b, to_int(aref1(p, i))), q)
        i += 1
      }
      acc = cons(cons(list2(q_mlist, q_simp), nreverse(q)), acc)
      p = permutation_lex_successor(int(n), p, r)
    }
  } else {
    acc = list1(list1(list2(q_mlist, q_simp)))
  }
  acc = nreverse(acc)
  if need_to_simp {
    cons(list1(q_d_set), acc)
  } else {
    nset__mk_set(acc)
  }
}

///|
/// Based on Algorithm 2.14 of Kreher and Stinson. The array elements p(1)
/// thru p(n) specify the permutation; the array r gets used for swapping
/// elements of p.
fn permutation_lex_successor(n : Value, p : Value, r : Value) -> Value raise {
  let n = to_int(n)
  let ar = fn(x : Value, i : Int) -> Int raise { to_int(aref1(x, i)) }
  let mut i = n - 1
  let mut j = n
  aset1(p, 0, int(0)) |> ignore
  while ar(p, i + 1) < ar(p, i) {
    i -= 1
  }
  if i == 0 {
    Nil
  } else {
    while ar(p, j) < ar(p, i) {
      j -= 1
    }
    let tm = aref1(p, j)
    aset1(p, j, aref1(p, i)) |> ignore
    aset1(p, i, tm) |> ignore
    j = i + 1
    while j <= n {
      aset1(r, j, aref1(p, j)) |> ignore
      j += 1
    }
    j = i + 1
    let m = n + i + 1
    while j <= n {
      aset1(p, j, aref1(r, m - j)) |> ignore
      j += 1
    }
    p
  }
}

///|
fn d_random_permutation(a : Value) -> Value raise {
  let a = if d_listp(a).truthy() {
    copy_list(cdr(a))
  } else {
    copy_list(require_set(a, q_d_random_permutation))
  }
  let n = length(a)
  for i in 0..<n {
    let j = i + to_int(d_random(int(n - i)))
    let tmp = nth(i, a)
    rplaca(nthcdr(i, a), nth(j, a)) |> ignore
    rplaca(nthcdr(j, a), tmp) |> ignore
  }
  cons(list1(q_mlist), a)
}

///|
/// Returns 3 values
/// FOUND -- is X in L
/// POSITION -- where is X in L; if not in L, position it is before
/// REST -- everything after X in L
fn b_search_expr(
  x : Value,
  l : Value,
  lo : Value,
  len : Value,
) -> (Value, Value, Value) raise {
  let mut len = to_int(len)
  let mut lo = to_int(lo)
  let mut l = l
  if len == 0 {
    return (Nil, int(lo), l)
  }
  // uses great directly instead of $orderlessp; only specrepcheck x once
  let x = specrepcheck(x)
  while len > 1 {
    let mid = len / 2
    let midl = nthcdr(mid, l)
    let midel = specrepcheck(car(midl))
    if alike1(x, midel).truthy() {
      l = midl
      lo = lo + mid
      len = -1
    } else if great(midel, x).truthy() {
      len = mid
    } else {
      l = midl
      lo = lo + mid
      len = len - mid
    }
  }
  if len == -1 {
    (t, int(lo), cdr(l))
  } else if alike1(x, specrepcheck(nth(0, l))).truthy() {
    (t, int(lo), cdr(l))
  } else if great(specrepcheck(nth(0, l)), x).truthy() {
    (Nil, int(lo), l)
  } else {
    (Nil, int(lo + 1), cdr(l))
  }
}

///|
/// Flatten evaluates an expression as if its main operator had been
/// declared nary, but doesn't recurse into other function arguments.
fn d_flatten(e : Value) -> Value raise {
  if specrepp(e).truthy() || mapatom(e).truthy() {
    e
  } else {
    mcons_op_args(mop(e), flattenl_op(margs(e), mop(e)))
  }
}

///|
fn flattenl_op(e : Value, op : Value) -> Value raise {
  mapcan(
    e => if mapatom(e).truthy() || !alike1(mop(e), op).truthy() {
      list1(e)
    } else {
      flattenl_op(margs(e), op)
    },
    e,
  )
}

///|
fn sorted_remove_duplicates(l : Value) -> Value raise {
  let result = l
  let mut l = l
  while !(cdr(l) is Nil) {
    while !(cdr(l) is Nil) && like(car(l), cadr(l)).truthy() {
      rplacd(l, cddr(l)) |> ignore
    }
    l = cdr(l)
  }
  result
}

///|
/// The `do-merge-asym` macro (clmacs.lisp) with eqfun `like` and lessfun
/// `$orderlessp`. Each callback returns false to stop the merge early (a
/// `throw` out of it); the function then returns false.
fn nset__do_merge_asym(
  l1 : Value,
  l2 : Value,
  bothfun : ((Value) -> Bool raise)?,
  only1fun : ((Value) -> Bool raise)?,
  only2fun : ((Value) -> Bool raise)?,
) -> Bool raise {
  let mut l1 = l1
  let mut l2 = l2
  while true {
    if l1 is Nil {
      if only2fun is Some(f) {
        while !(l2 is Nil) {
          if !f(car(l2)) {
            return false
          }
          l2 = cdr(l2)
        }
      }
      return true
    } else if l2 is Nil {
      if only1fun is Some(f) {
        while !(l1 is Nil) {
          if !f(car(l1)) {
            return false
          }
          l1 = cdr(l1)
        }
      }
      return true
    } else if like(car(l1), car(l2)).truthy() {
      if bothfun is Some(f) {
        if !f(car(l1)) {
          return false
        }
      }
      l1 = cdr(l1)
      l2 = cdr(l2)
    } else if d_orderlessp(car(l1), car(l2)).truthy() {
      if only1fun is Some(f) {
        if !f(car(l1)) {
          return false
        }
      }
      l1 = cdr(l1)
    } else {
      if only2fun is Some(f) {
        if !f(car(l2)) {
          return false
        }
      }
      l2 = cdr(l2)
    }
  }
  true
}

///|
fn set_intersect(l1 : Value, l2 : Value) -> Value raise {
  // Only works for lists of sorted by $orderlessp.
  let c = Collector::new()
  let collect = fn(x : Value) -> Bool raise {
    c.add(x)
    true
  }
  nset__do_merge_asym(l1, l2, Some(collect), None, None) |> ignore
  c.result()
}

///|
fn set_union(l1 : Value, l2 : Value) -> Value raise {
  // Only works for lists of sorted by $orderlessp.
  let c = Collector::new()
  let collect = fn(x : Value) -> Bool raise {
    c.add(x)
    true
  }
  nset__do_merge_asym(l1, l2, Some(collect), Some(collect), Some(collect))
  |> ignore
  c.result()
}

///|
fn sset_difference(l1 : Value, l2 : Value) -> Value raise {
  // Only works for lists of sorted by $orderlessp.
  let c = Collector::new()
  let collect = fn(x : Value) -> Bool raise {
    c.add(x)
    true
  }
  nset__do_merge_asym(l1, l2, None, Some(collect), None) |> ignore
  c.result()
}

///|
fn set_subsetp(l1 : Value, l2 : Value) -> Value raise {
  // Is l1 a subset of l2
  lbool(nset__do_merge_asym(l1, l2, None, Some(_ => false), None))
}

///|
fn set_symmetric_difference(l1 : Value, l2 : Value) -> Value raise {
  let c = Collector::new()
  let collect = fn(x : Value) -> Bool raise {
    c.add(x)
    true
  }
  nset__do_merge_asym(l1, l2, None, Some(collect), Some(collect)) |> ignore
  c.result()
}

///|
fn set_disjointp(l1 : Value, l2 : Value) -> Value raise {
  lbool(nset__do_merge_asym(l1, l2, Some(_ => false), None, None))
}

///|
/// When s = $max, return { x in a | f(x) = maximum of f on a} and when
/// s = $min, return { x in a | f(x) = minimum of f on a}.
fn d_extremal_subset(a : Value, f : Value, s : Value) -> Value raise {
  let mut a = require_set(a, q_d_extremal_subset)
  if a is Nil {
    return list1(nset__set_header())
  }
  let s = if eq(s, q_d_min) {
    int(-1)
  } else if eq(s, q_d_max) {
    int(1)
  } else {
    merr(
      "extremal_subset: third argument must be 'max or 'min; found: ~:M",
      [s],
    )
  }
  let max_subset0 = nth(0, a)
  let mut mx = mul2(s, mfuncall(f, list1(max_subset0)))
  let mut max_subset = list1(max_subset0)
  a = cdr(a)
  for ai in a.iter() {
    let x = mul2(s, mfuncall(f, list1(ai)))
    if mevalp_tr(mgrp(x, mx), t).truthy() {
      mx = x
      max_subset = list1(ai)
    } else if like(x, mx).truthy() {
      max_subset = cons(ai, max_subset)
    }
  }
  nset__mk_set(nreverse(max_subset))
}

///|
fn bool_checked_mfuncall(f : Value, x : Value, y : Value) -> Value raise {
  with_special(q_d_prederror, Nil, () => {
    let b = mevalp(mfuncall(f, list2(x, y)))
    if eq(b, t) || b is Nil {
      b
    } else {
      merr("equiv_classes: ~:M(~:M, ~:M) evaluates to a non-boolean.", [
        f, x, y,
      ])
    }
  })
}

///|
/// Return the set of equivalence classes of f on the set l.
fn d_equiv_classes(l : Value, f : Value) -> Value raise {
  let mut l = require_set(l, q_d_equiv_classes)
  let mut acc : Value = Nil
  while !(l is Nil) {
    let x = car(l)
    let tail = member_if(z => bool_checked_mfuncall(f, x, car(z)).truthy(), acc)
    if tail is Nil {
      acc = cons(list1(x), acc)
    } else {
      rplaca(tail, cons(x, car(tail))) |> ignore
    }
    l = cdr(l)
  }
  simplify(cons(list1(q_d_set), mapcar(x => cons(list1(q_d_set), x), acc)))
}

///|
fn d_cartesian_product(b : Value) -> Value raise {
  if b is Nil {
    list2(list1(q_d_set), list1(list1(q_mlist)))
  } else if every(x => d_setp(x).truthy(), b) {
    let l = cartesian_product(mapcar(x => cdr(x), b))
    cons(list1(q_d_set), mapcar(e => cons(list1(q_mlist), e), l))
  } else {
    merr("cartesian_product: all arguments must be sets; found: ~M", [
      cons(list1(q_mlist), b),
    ])
  }
}

///|
fn d_cartesian_product_list(b : Value) -> Value raise {
  if b is Nil {
    list2(list1(q_mlist), list1(list1(q_mlist)))
  } else if every(x => d_listp(x).truthy(), b) {
    let l = cartesian_product(mapcar(x => cdr(x), b))
    cons(list1(q_mlist), mapcar(e => cons(list1(q_mlist), e), l))
  } else {
    merr("cartesian_product_list: all arguments must be lists; found: ~M", [
      cons(list1(q_mlist), b),
    ])
  }
}

///|
/// Assume here that B is nonempty; caller has already handled case B = NIL.
fn cartesian_product(b : Value) -> Value raise {
  let mut b = reverse(b)
  let mut acc = mapcar(x => list1(x), car(b))
  b = cdr(b)
  for bi in b.iter() {
    let mut a : Value = Nil
    for bij in bi.iter() {
      let cur = acc
      a = append(a, mapcar(x => cons(bij, x), cur))
    }
    acc = a
  }
  acc
}

///|
fn d_set_partitions(a : Value, n__sub? : Value = Nil) -> Value raise {
  let a = require_set(a, q_d_set_partitions)
  if integerp(n__sub) && num_gt(n__sub, int(-1)) {
    cons(list1(q_d_set), set_partitions(a, n__sub))
  } else if n__sub is Nil {
    let n_sub = length(a)
    let mut acc = set_partitions(a, int(0))
    let mut k = 1
    while k <= n_sub {
      acc = append(acc, set_partitions(a, int(k)))
      k += 1
    }
    cons(list1(q_d_set), acc)
  } else {
    merr(
      "set_partitions: second argument must be a positive integer; found: ~:M",
      [n__sub],
    )
  }
}

///|
fn set_partitions(a : Value, n : Value) -> Value raise {
  if num_eq(n, int(0)) {
    if a is Nil {
      list1(list1(nset__set_header()))
    } else {
      Nil
    }
  } else if a is Nil {
    Nil
  } else {
    let mut acc : Value = Nil
    let x = car(a)
    let p = set_partitions(cdr(a), n)
    for pj in p.iter() {
      let mut w : Value = Nil
      let mut s = cdr(pj)
      while !(s is Nil) {
        let z = car(s)
        s = cdr(s)
        acc = cons(
          simplifya(
            cons(list1(q_d_set), append_n([w, list1(d_adjoin(x, z)), s])),
            t,
          ),
          acc,
        )
        w = cons(z, w)
      }
    }
    let x = nset__mk_set(list1(x))
    let p = set_partitions(cdr(a), num_sub(n, int(1)))
    for pj in p.iter() {
      acc = cons(d_adjoin(x, pj), acc)
    }
    acc
  }
}

///|
/// Generate the integer partitions in dictionary order.
fn d_integer_partitions(n : Value, len? : Value = Nil) -> Value raise {
  if integerp(n) && num_ge(n, int(0)) {
    let mut acc : Value = if num_eq(n, int(0)) {
      Nil
    } else if integerp(len) {
      fixed_length_partitions(n, n, len)
    } else {
      integer_partitions(n)
    }
    if acc is Nil && num_eq(n, int(0)) {
      acc = list1(list1(list2(q_mlist, q_simp)))
    } else {
      acc = mapcar(x => simplify(cons(list1(q_mlist), x)), acc)
    }
    nset__mk_set(acc)
  } else if len.truthy() {
    list3(list2(q_d_integer_partitions, q_simp), n, len)
  } else {
    list2(list2(q_d_integer_partitions, q_simp), n)
  }
}

///|
fn integer_partitions(n : Value) -> Value raise {
  let mut p = list1(n)
  let mut acc : Value = Nil
  while num_gt(car(last(p)), int(1)) {
    acc = cons(copy_list(reverse(p)), acc)
    p = member_if(x => num_gt(x, int(1)), p)
    let mut k = num_sub(nth(0, p), int(1))
    rplaca(p, k) |> ignore
    let mut d = num_sub(n, num_sum(list_to_array(p)))
    while num_gt(k, int(0)) && num_gt(d, int(0)) {
      let (q, r) = num_floor(d, b=k)
      let pre = []
      let mut c = int(0)
      while num_lt(c, q) {
        pre.push(k)
        c = num_add(c, int(1))
      }
      p = append(list(pre), p)
      d = r
      k = num_sub(k, int(1))
    }
  }
  acc = cons(copy_list(reverse(p)), acc)
  acc
}

///|
fn fixed_length_partitions(n : Value, b : Value, len : Value) -> Value raise {
  let mut p = t
  let mut acc : Value = Nil
  let mut n = n
  let mut len = len
  if num_gt(n, num_mul(b, len)) {
    ()
  } else if num_eq(len, int(1)) {
    if num_le(n, b) {
      acc = list1(list1(n))
    }
  } else {
    len = num_sub(len, int(1))
    let mut i = num_sub(n, num_min(n, b))
    n = num_min(n, b)
    while !(p is Nil) {
      let nn = n
      p = mapcar(
        x => cons(nn, x),
        fixed_length_partitions(i, num_min(i, n), len),
      )
      acc = append(p, acc)
      n = num_sub(n, int(1))
      i = num_add(i, int(1))
    }
  }
  acc
}

///|
/// The list `((mlist simp) p[1] ... p[n])` built as in the Lisp code by
/// `(push '(mlist simp) (cdr acc))`.
fn nset__p_list(p : Array[Value], n : Int) -> Value {
  let acc = []
  for i in 0..<(n + 1) {
    acc.push(p[i])
  }
  let l = list(acc)
  setf_cdr(l, cons(list2(q_mlist, q_simp), cdr(l))) |> ignore
  cdr(l)
}

///|
/// When n is a nonnegative integer, return the number of partitions of n.
fn d_num_partitions(n : Value, lst? : Value = Nil) -> Value raise {
  if equal(n, int(0)) {
    int(1)
  } else if integerp(n) && num_gt(n, int(-1)) {
    let ni = to_int(n)
    let p = Array::make(ni + 1, int(0))
    p[0] = int(1)
    for i in 1..=ni {
      let mut k = 1
      while true {
        let k64 = k.to_int64()
        if k % 2 == 1 {
          let mut j = (k64 * (3L * k64 - 1L) / 2L).to_int()
          if j > i {
            break
          }
          p[i] = num_add(p[i], p[i - j])
          j = (k64 * (3L * k64 + 1L) / 2L).to_int()
          if j > i {
            break
          }
          p[i] = num_add(p[i], p[i - j])
        } else {
          let mut j = (k64 * (3L * k64 - 1L) / 2L).to_int()
          if j > i {
            break
          }
          p[i] = num_sub(p[i], p[i - j])
          j = (k64 * (3L * k64 + 1L) / 2L).to_int()
          if j > i {
            break
          }
          p[i] = num_sub(p[i], p[i - j])
        }
        k += 1
      }
    }
    if eq(lst, q_d_list) {
      nset__p_list(p, ni)
    } else {
      p[ni]
    }
  } else if lst.truthy() {
    list3(list2(q_d_num_partitions, q_simp), n, lst)
  } else {
    list2(list2(q_d_num_partitions, q_simp), n)
  }
}

///|
fn d_num_distinct_partitions(n : Value, lst? : Value = Nil) -> Value raise {
  if eql(n, int(0)) {
    int(1)
  } else if integerp(n) && num_gt(n, int(-1)) {
    let ni = to_int(n)
    let p = Array::make(ni + 1, nil)
    let s = Array::make(ni + 1, nil)
    let u = Array::make(ni + 1, nil)
    p[0] = int(1)
    p[1] = int(1)
    let mut i = 0
    while i <= ni {
      s[i] = mfuncall(q_d_divsum, list2(int(i), int(1)))
      i += 1
    }
    i = 0
    while i <= ni {
      if i % 2 == 1 {
        u[i] = s[i]
      } else {
        u[i] = num_sub(s[i], num_mul(int(2), s[i / 2]))
      }
      i += 1
    }
    i = 2
    while i <= ni {
      let mut sum = int(0)
      let mut j = 1
      while j <= i {
        sum = num_add(sum, num_mul(u[j], p[i - j]))
        j += 1
      }
      p[i] = num_div(sum, int(i))
      i += 1
    }
    if eq(lst, q_d_list) {
      nset__p_list(p, ni)
    } else {
      p[ni]
    }
  } else if lst.truthy() {
    list3(list2(q_d_num_distinct_partitions, q_simp), n, lst)
  } else {
    list2(list2(q_d_num_distinct_partitions, q_simp), n)
  }
}

///|
fn d_kron_delta(x : Value) -> Value raise {
  simplifya(cons(list1(q_p_kron_delta), x), t)
}

///|
/// A n-ary Kronecker delta function.
fn simp_kron_delta(l : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let l = cdr(l)
  if l.truthy() && cdr(l) is Nil {
    // wrong number of arguments error for exactly one argument
    wna_err(q_d_kron_delta) |> ignore
  }
  let mut acc : Value = Nil
  let mut return_zero = false
  for lk0 in l.iter() {
    let lk = simpcheck(lk0, z)
    if some(s => eq(t, mnqp(s, lk)), acc) {
      return_zero = true
      break
    } else if some(s => eq(t, meqp(s, lk)), acc) {
      ()
    } else {
      acc = cons(lk, acc)
    }
  }
  if return_zero {
    int(0)
  } else if acc is Nil || cdr(acc) is Nil {
    int(1)
  } else {
    // reflection: kron_delta(-a,-b,...) == kron_delta(a,b,...).
    let neg_acc = nset__sort(mapcar(x => neg(x), acc))
    let acc = nset__sort(acc)
    cons(
      list2(q_p_kron_delta, q_simp),
      if great(cons(list1(q_mlist), neg_acc), cons(list1(q_mlist), acc)).truthy() {
        neg_acc
      } else {
        acc
      },
    )
  }
}

///|
fn tex_kron_delta(x : Value, l : Value, r : Value) -> Value raise {
  append(
    l,
    append(
      cons(Str("\\delta_{"), tex_list(cdr(x), Nil, list1(Str("} ")), Str(", "))),
      r,
    ),
  )
}

///|
/// Stirling1 simplifications; for n,k in Z.
fn simp_stirling1(l : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let fn_ = car(car(l))
  let mut l = cdr(l)
  let n = if l.truthy() {
    let v = car(l)
    l = cdr(l)
    maybe_simplifya(v, z)
  } else {
    wna_err(fn_)
  }
  let k = if l.truthy() {
    let v = car(l)
    l = cdr(l)
    maybe_simplifya(v, z)
  } else {
    wna_err(fn_)
  }
  let n_is_nonnegative_int = nonnegative_integerp(n).truthy()
  if l.truthy() {
    wna_err(fn_) |> ignore
  }
  if integerp(n) && integerp(k) && num_gt(n, int(-1)) && num_gt(k, int(-1)) {
    integer_stirling1(n, k)
  } else if eql(n, int(1)) &&
    d_featurep(k, q_d_integer).truthy() &&
    eq(t, mgrp(k, int(-1))) {
    take(list1(q_p_kron_delta), [int(1), k])
  } else if n_is_nonnegative_int && like(n, k).truthy() {
    int(1)
  } else if nonnegative_integerp(sub(n, int(1))).truthy() &&
    like(n, add2(k, int(1))).truthy() {
    mul2(int(-1), take(list1(q_p_binomial), [n, int(2)]))
  } else if n_is_nonnegative_int && eql(k, int(0)) {
    take(list1(q_p_kron_delta), [n, int(0)])
  } else if n_is_nonnegative_int && eql(k, int(1)) && eq(t, mgqp(n, int(1))) {
    mul2(
      power(int(-1), sub(n, int(1))),
      take(list1(q_mfactorial), [sub(n, int(1))]),
    )
  } else if n_is_nonnegative_int &&
    d_featurep(k, q_d_integer).truthy() &&
    eq(t, mgrp(k, n)) {
    int(0)
  } else {
    list3(list2(fn_, q_simp), n, k)
  }
}

///|
/// Based on Algorithm 3.17 of Kreher and Stinson (with the typographical
/// error i - j replaced by i - 1).
fn integer_stirling1(m : Value, n : Value) -> Value raise {
  if num_ge(m, n) {
    let mi = to_int(m)
    let ni = to_int(n)
    let s = Array::makei(mi + 1, _ => Array::make(mi + 1, int(0)))
    s[0][0] = int(1)
    let mut i = 1
    while i <= mi {
      let k = if i < ni { i } else { ni }
      let mut j = 1
      let im1 = i - 1
      while j <= k {
        s[i][j] = num_sub(s[im1][j - 1], num_mul(int(im1), s[im1][j]))
        j += 1
      }
      i += 1
    }
    s[mi][ni]
  } else {
    int(0)
  }
}

///|
fn nonnegative_integerp(e : Value) -> Value raise {
  if d_featurep(e, q_d_integer).truthy() {
    memq(d_sign(specrepcheck(e)), list([q_d_pos, q_d_zero, q_d_pz]))
  } else {
    Nil
  }
}

///|
fn simp_stirling2(l : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let fn_ = car(car(l))
  let mut l = cdr(l)
  let n = if l.truthy() {
    let v = car(l)
    l = cdr(l)
    maybe_simplifya(v, z)
  } else {
    wna_err(fn_)
  }
  let k = if l.truthy() {
    let v = car(l)
    l = cdr(l)
    maybe_simplifya(v, z)
  } else {
    wna_err(fn_)
  }
  let n_is_nonnegative_int = nonnegative_integerp(n).truthy()
  let n_is_positive_int = nonnegative_integerp(sub(n, int(1))).truthy()
  if l.truthy() {
    wna_err(fn_) |> ignore
  }
  if integerp(n) && integerp(k) && num_gt(n, int(-1)) && num_gt(k, int(-1)) {
    integer_stirling2(n, k)
  } else if n_is_positive_int && eql(k, int(0)) {
    int(0)
  } else if n_is_positive_int && eql(k, int(1)) {
    int(1)
  } else if n_is_positive_int && eql(k, int(2)) {
    add2(power(int(2), sub(n, int(1))), int(-1))
  } else if n_is_nonnegative_int && like(n, k).truthy() {
    int(1)
  } else if n_is_positive_int && like(n, add2(k, int(1))).truthy() {
    take(list1(q_p_binomial), [n, int(2)])
  } else if n_is_nonnegative_int &&
    d_featurep(k, q_d_integer).truthy() &&
    eq(t, mgrp(k, n)) {
    int(0)
  } else {
    list3(list2(fn_, q_simp), n, k)
  }
}

///|
/// Stirling2(n,m) = sum((-1)^(m - k) binomial(m k) k^n,i,1,m) / m!.
/// See A & S 24.1.4, page 824.
fn integer_stirling2(n : Value, m : Value) -> Value raise {
  let mut s = if num_eq(n, int(0)) { int(1) } else { int(0) }
  let mut i = int(1)
  let mut f = int(1)
  let mut b = m
  while num_le(i, m) {
    let mut z = num_mul(b, expt(i, n))
    f = num_mul(f, i)
    b = num_div(num_mul(num_sub(m, i), b), num_add(i, int(1)))
    if oddp(i) {
      z = num_neg(z)
    }
    s = num_add(s, z)
    i = num_add(i, int(1))
  }
  s = num_div(s, f)
  if oddp(m) {
    num_neg(s)
  } else {
    s
  }
}

///|
/// Simplify the Bell function.
fn simp_belln(n : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  oneargcheck(n) |> ignore
  let y = caar(n)
  let n = simpcheck(cadr(n), z)
  if integerp(n) && num_gt(n, int(-1)) {
    integer_belln(n)
  } else if d_listp(n).truthy() ||
    d_setp(n).truthy() ||
    d_matrixp(n).truthy() ||
    mequalp(n).truthy() {
    thread(y, cdr(n), caar(n))
  } else {
    list2(list2(q_d_belln, q_simp), n)
  }
}

///|
fn integer_belln(n : Value) -> Value raise {
  let mut s = if num_eq(n, int(0)) { int(1) } else { int(0) }
  let mut i = int(1)
  while num_le(i, n) {
    s = num_add(s, integer_stirling2(n, i))
    i = num_add(i, int(1))
  }
  s
}

///|
/// The multinomial coefficient.
fn d_multinomial_coeff(a : Value) -> Value raise {
  let mut n = int(0)
  let mut d = int(1)
  for ai in a.iter() {
    n = add2(n, ai)
    d = mult(d, simplify(mk(q_mfactorial, [ai])))
  }
  div(simplify(mk(q_mfactorial, [n])), d)
}

///|
fn d_rreduce(f : Value, s : Value, init_? : Value = q_no_init) -> Value raise {
  rl_reduce(f, s, t, init_, q_d_rreduce)
}

///|
fn d_lreduce(f : Value, s : Value, init_? : Value = q_no_init) -> Value raise {
  rl_reduce(f, s, Nil, init_, q_d_lreduce)
}

///|
/// CL `reduce` of `mfuncall f` over `s`, honoring `:from-end left` and an
/// optional initial value.
fn nset__reduce(
  f : Value,
  s : Value,
  from_end : Bool,
  init_ : Value?,
) -> Value raise {
  let arr = list_to_array(s)
  if from_end {
    let mut i = arr.length() - 1
    let mut acc = match init_ {
      Some(v) => v
      None => {
        if i < 0 {
          return mfuncall(f, nil)
        }
        let v = arr[i]
        i -= 1
        v
      }
    }
    while i >= 0 {
      acc = mfuncall(f, list2(arr[i], acc))
      i -= 1
    }
    acc
  } else {
    let mut i = 0
    let mut acc = match init_ {
      Some(v) => v
      None => {
        if arr.length() == 0 {
          return mfuncall(f, nil)
        }
        i = 1
        arr[0]
      }
    }
    while i < arr.length() {
      acc = mfuncall(f, list2(acc, arr[i]))
      i += 1
    }
    acc
  }
}

///|
fn rl_reduce(
  f : Value,
  s : Value,
  left : Value,
  init_ : Value,
  fn_ : Value,
) -> Value raise {
  let s = require_list(s, fn_)
  if !equal(init_, q_no_init) {
    nset__reduce(f, s, left.truthy(), Some(init_))
  } else if s is Nil {
    merr("~M: either a nonempty set or initial value must be given.", [fn_])
  } else {
    nset__reduce(f, s, left.truthy(), None)
  }
}

///|
/// `def-nary` macro: `(setf (get fn '$nary) (list #'(lambda arg f-body) id))`.
/// In the port, `f_body` is the already-built function value and `arg` is
/// ignored.
fn def_nary(fn_ : Value, arg : Value, f_body : Value, id : Value) -> Value raise {
  ignore(arg)
  setf_get(fn_, q_d_nary, list2(f_body, id))
}

///|
fn xappend(s : Value) -> Value raise {
  let mut acc : Value = Nil
  for si in reverse(s).iter() {
    acc = append(require_list(si, q_d_append), acc)
  }
  cons(list1(q_mlist), acc)
}

///|
/// Extend a function f : S x S -> S to n arguments.
fn d_xreduce(f : Value, s : Value, init_? : Value = q_no_init) -> Value raise {
  let op_props = get(if atom(f) { d_verbify(f) } else { Nil }, q_d_nary)
  let opfn = if consp(op_props) { car(op_props) } else { Nil }
  if opfn.truthy() {
    let mut s = require_list_or_set(s, q_d_xreduce)
    if !equal(init_, q_no_init) {
      s = cons(init_, s)
    }
    if s is Nil {
      cadr(op_props)
    } else {
      funcall(opfn, [s])
    }
  } else if op_props.truthy() {
    let mut s = require_list_or_set(s, q_d_xreduce)
    if !eq(init_, q_no_init) {
      s = cons(init_, s)
    }
    d_apply(f, cons(list1(q_mlist), s))
  } else {
    rl_reduce(f, d_listify(s), Nil, init_, q_d_xreduce)
  }
}

///|
/// Extend a function f : S x S -> S to n arguments using a minimum depth
/// tree.
fn d_tree_reduce(f : Value, a : Value, init_? : Value = q_no_init) -> Value raise {
  let mut a = require_list_or_set(a, q_d_tree_reduce)
  if !equal(init_, q_no_init) {
    a = cons(init_, a)
  }
  if a is Nil {
    merr(
      "tree_reduce: either a nonempty set or initial value must be given.",
      [],
    )
    |> ignore
  }
  let mut acc : Value = Nil
  let mut x : Value = Nil
  let mut doit = false
  while consp(a) {
    x = car(a)
    a = cdr(a)
    while consp(a) {
      let y = car(a)
      a = cdr(a)
      acc = cons(mfuncall(f, list2(x, y)), acc)
      doit = consp(a)
      if doit {
        x = car(a)
        a = cdr(a)
      }
    }
    if doit {
      acc = cons(x, acc)
    }
    a = nreverse(acc)
    acc = Nil
  }
  x
}

///|
fn d_identity(x : Value) -> Value raise {
  x
}

///|
fn checked_and(x : Value) -> Value raise {
  let x = mfuncall(q_d_maybe, list1(cons(list1(q_mand), x)))
  if eq(x, t) || x is Nil || !symval(q_d_prederror).truthy() {
    x
  } else if eq(x, q_d_unknown) {
    Nil
  } else {
    merr(
      "Predicate isn't true/false valued; maybe you want to set 'prederror' to false",
      [],
    )
  }
}

///|
fn checked_or(x : Value) -> Value raise {
  let x = mfuncall(q_d_maybe, list1(cons(list1(q_mor), x)))
  if eq(x, t) || x is Nil || !symval(q_d_prederror).truthy() {
    x
  } else if eq(x, q_d_unknown) {
    Nil
  } else {
    merr(
      "Predicate isn't true/false valued; maybe you want to set 'prederror' to false",
      [],
    )
  }
}

///|
/// Apply the Maxima function f to x. If an error is signaled, return nil;
/// otherwise return (list (mfuncall f x)).
fn ignore_errors_mfuncall(f : Value, x : Value) -> Value raise {
  with_special(q_errcatch, t, () => match errset(() => mfuncall(f, list1(x))) {
    Some(v) => list1(v)
    None => Nil
  })
}

///|
fn d_every(f : Value, x : Value) -> Value raise {
  if x is Nil || (cdr(x) is Nil && d_emptyp(first(x)).truthy()) {
    t
  } else if d_listp(first(x)).truthy() ||
    (d_setp(first(x)).truthy() && cdr(x) is Nil) {
    let x = margs(simplify(map1(cons(f, x))))
    checked_and(
      mapcar(
        y => car(y),
        mapcar(s => ignore_errors_mfuncall(q_d_maybe, s), x),
      ),
    )
  } else if every(m => d_matrixp(m).truthy(), x) {
    with_special(q_fmaplvl, int(2), () => {
      let x = margs(simplify(fmapl1(f, x)))
      checked_and(mapcar(s => d_every(q_d_identity, list1(s)), x))
    })
  } else {
    merr("every: invalid arguments.", [])
  }
}

///|
fn d_some(f : Value, x : Value) -> Value raise {
  if x is Nil || (cdr(x) is Nil && d_emptyp(first(x)).truthy()) {
    Nil
  } else if d_listp(first(x)).truthy() ||
    (d_setp(first(x)).truthy() && cdr(x) is Nil) {
    let x = margs(simplify(map1(cons(f, x))))
    checked_or(
      mapcar(
        y => car(y),
        mapcar(s => ignore_errors_mfuncall(q_d_maybe, s), x),
      ),
    )
  } else if every(m => d_matrixp(m).truthy(), x) {
    with_special(q_fmaplvl, int(2), () => {
      let x = margs(simplify(fmapl1(f, x)))
      checked_or(mapcar(s => d_some(q_d_identity, list1(s)), x))
    })
  } else {
    merr("some: invalid arguments.", [])
  }
}

///|
/// `(subst new old tree :test #'alike1)`
fn nset__subst_alike1(new : Value, old : Value, tree : Value) -> Value raise {
  if alike1(old, tree).truthy() {
    new
  } else {
    match tree {
      Cons(c) => {
        let a = nset__subst_alike1(new, old, c.car)
        let d = nset__subst_alike1(new, old, c.cdr)
        if eq(a, c.car) && eq(d, c.cdr) {
          tree
        } else {
          cons(a, d)
        }
      }
      _ => tree
    }
  }
}

///|
fn d_makeset(l : Value) -> Value raise {
  let fn_ = car(car(l))
  let mut l = cdr(l)
  let pop_arg = fn() -> Value raise {
    if l.truthy() {
      let v = car(l)
      l = cdr(l)
      v
    } else {
      wna_err(fn_)
    }
  }
  let mut f = pop_arg()
  let mut v = pop_arg()
  let s = pop_arg()
  if l.truthy() {
    wna_err(fn_) |> ignore
  }
  if !d_listp(v).truthy() ||
    !every(x => d_symbolp(x).truthy() || d_subvarp(x).truthy(), cdr(v)) {
    merr("makeset: second argument must be a list of symbols; found: ~:M", [
      v,
    ])
    |> ignore
  }
  let s = require_list_or_set(meval(s), q_d_makeset)
  f = list3(list1(q_lambda), v, f)
  v = margs(v)
  for sk in v.iter() {
    f = nset__subst_alike1(gensym(), sk, f)
  }
  let ff = f
  simplifya(
    cons(list1(q_d_set), mapcar(x => mfuncall(q_d_apply, list2(ff, x)), s)),
    t,
  )
}

///|
/// Thread fn over l and apply op to the resulting list.
fn thread(fn_ : Value, l : Value, op : Value) -> Value raise {
  simplify(cons(list1(op), mapcar(x => simplify(mk(fn_, [x])), l)))
}

///|
/// Return a set of the divisors of n.
fn simp_divisors(n : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  oneargcheck(n) |> ignore
  let y = caar(n)
  let n = simpcheck(cadr(n), z)
  if d_listp(n).truthy() ||
    d_setp(n).truthy() ||
    d_matrixp(n).truthy() ||
    mequalp(n).truthy() {
    thread(y, cdr(n), caar(n))
  } else if integerp(n) && !zerop(n) {
    let n = num_abs(n)
    with_special(q_d_intfaclim, Nil, () => nset__mk_set(
      sort_list(mapcar(x => car(x), divisors(cfactorw(n))), (a, b) => num_lt(
        a, b,
      )),
    ))
  } else {
    list2(list2(q_d_divisors, q_simp), n)
  }
}

///|
/// The Moebius function; it threads over lists, sets, matrices, and
/// equalities.
fn simp_moebius(n : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  oneargcheck(n) |> ignore
  let y = caar(n)
  let n = simpcheck(cadr(n), z)
  if posint(n).truthy() {
    if num_eq(n, int(1)) {
      int(1)
    } else {
      // pfl is a list of (prime exponent) pairs; it is computed before
      // $intfaclim is rebound (parallel LET).
      let pfl = get_factor_list(n)
      with_special(q_d_intfaclim, Nil, () => if every(
          x => num_eq(int(1), second(x)),
          pfl,
        ) {
        if length(pfl) % 2 == 0 {
          int(1)
        } else {
          int(-1)
        }
      } else {
        int(0)
      })
    }
  } else if d_listp(n).truthy() ||
    d_setp(n).truthy() ||
    d_matrixp(n).truthy() ||
    mequalp(n).truthy() {
    thread(y, cdr(n), caar(n))
  } else {
    list2(list2(q_d_moebius, q_simp), n)
  }
}

///|
/// Find indices of elements which satisfy a predicate.
fn d_sublist_indices(items : Value, pred : Value) -> Value raise {
  let items = require_list(items, q_d_sublist_indices)
  let mut i = 0
  let mut xs = items
  let mut acc : Value = Nil
  while !(xs is Nil) {
    if definitely_so(mfuncall(pred, list1(car(xs)))).truthy() {
      acc = cons(int(i + 1), acc)
    }
    i += 1
    xs = cdr(xs)
  }
  cons(list1(q_mlist), nreverse(acc))
}

///|
fn init_nset() -> Unit raise {
  d_put(q_d_nset, Flo(1.21), q_d_version) |> ignore
  set(q_d_props, remove(q_d_nset, symval(q_d_props))) |> ignore
  // Display sets as { .. }.
  putprop(q_d_set, q_msize_matchfix, q_grind) |> ignore
  setf_get(q_d_set, q_dissym, list2(list1(Char('{')), Char('}'))) |> ignore
  setf_get(q_d_set, q_dimension, q_dimension_match) |> ignore
  // Parse {a, b, c} into set(a, b, c).
  setf_get(q_d_set, q_op, Str("{")) |> ignore
  setf_get(q_d_op_rc, q_nud, q_delim_err) |> ignore
  setf_get(q_d_op_rc, q_led, q_erb_err) |> ignore
  putprop(q_d_op_rc, int(5), q_lbp) |> ignore
  setf_get(q_d_op_lc, q_nud, q_parse_matchfix) |> ignore
  putprop(q_d_op_lc, q_d_op_rc, q_match) |> ignore
  putprop(q_d_op_lc, int(200), q_lbp) |> ignore
  putprop(q_d_op_lc, list1(q_d_set), q_mheader) |> ignore
  putprop(q_d_op_lc, q_d_any, q_pos) |> ignore
  def_operator(
    Str("{"),
    q_d_any,
    Nil,
    q_d_any,
    Nil,
    Nil,
    Nil,
    Nil,
    cons(q_nud, q_parse_matchfix),
    q_msize_matchfix,
    q_dimension_match,
    Str("}"),
  )
  |> ignore
  set(q_d_props, remove_equal(Str("{"), symval(q_d_props))) |> ignore
  set(q_d_props, remove_equal(Str("}"), symval(q_d_props))) |> ignore
  // DEF-OPERATOR makes "{" map to ${, but it needs to map to $SET.
  putopr(Str("{"), q_d_set) |> ignore
  // Support for TeXing sets.
  putprop(q_d_set, q_tex_matchfix, q_tex) |> ignore
  putprop(
    q_d_set,
    list2(list1(Str("\\left \\{")), Str(" \\right \\}")),
    q_texsym,
  )
  |> ignore
  putprop(q_d_set, q_simp_set, q_operators) |> ignore
  // kron_delta
  putprop(q_p_kron_delta, q_simp_kron_delta, q_operators) |> ignore
  setf_get(q_d_kron_delta, q_verb, q_p_kron_delta) |> ignore
  setf_get(q_p_kron_delta, q_noun, q_d_kron_delta) |> ignore
  setf_get(q_d_kron_delta, q_alias, q_p_kron_delta) |> ignore
  setf_get(q_p_kron_delta, q_reversealias, q_d_kron_delta) |> ignore
  setf_get(q_p_kron_delta, q_real_valued, t) |> ignore
  setf_get(q_p_kron_delta, q_integer_valued, t) |> ignore
  mputprop(q_p_kron_delta, t, q_d_scalar) |> ignore
  putprop(
    q_p_kron_delta,
    lfunc("kron-delta-sign", _ => set(q_sign, q_d_pz)),
    q_sign_function,
  )
  |> ignore
  putprop(q_p_kron_delta, q_tex_kron_delta, q_tex) |> ignore
  putprop(q_d_stirling1, q_simp_stirling1, q_operators) |> ignore
  putprop(q_d_stirling2, q_simp_stirling2, q_operators) |> ignore
  putprop(q_d_belln, q_simp_belln, q_operators) |> ignore
  // n-ary reductions
  def_nary(
    q_mand,
    Nil,
    lfunc("nary-mand", args => mevalp(cons(list1(q_mand), arg(args, 0)))),
    t,
  )
  |> ignore
  def_nary(
    q_mor,
    Nil,
    lfunc("nary-mor", args => mevalp(cons(list1(q_mor), arg(args, 0)))),
    Nil,
  )
  |> ignore
  def_nary(
    q_mplus,
    Nil,
    lfunc("nary-mplus", args => simplify(cons(list1(q_mplus), arg(args, 0)))),
    int(0),
  )
  |> ignore
  def_nary(
    q_mtimes,
    Nil,
    lfunc("nary-mtimes", args => simplify(cons(list1(q_mtimes), arg(args, 0)))),
    int(1),
  )
  |> ignore
  def_nary(
    q_d_max,
    Nil,
    lfunc("nary-max", args => {
      let s = arg(args, 0)
      if s is Nil {
        q_d_minf
      } else {
        maximin(s, q_d_max)
      }
    }),
    q_d_minf,
  )
  |> ignore
  def_nary(
    q_d_min,
    Nil,
    lfunc("nary-min", args => {
      let s = arg(args, 0)
      if s is Nil {
        q_d_inf
      } else {
        maximin(s, q_d_min)
      }
    }),
    q_d_inf,
  )
  |> ignore
  def_nary(
    q_d_append,
    Nil,
    lfunc("nary-append", args => xappend(arg(args, 0))),
    list1(list1(q_mlist)),
  )
  |> ignore
  def_nary(
    q_d_union,
    Nil,
    lfunc("nary-union", args => d_apply(q_d_union, cons(list1(q_mlist), arg(args, 0)))),
    list1(list1(q_d_set)),
  )
  |> ignore
  putprop(q_d_divisors, q_simp_divisors, q_operators) |> ignore
  putprop(q_d_moebius, q_simp_moebius, q_operators) |> ignore
}
