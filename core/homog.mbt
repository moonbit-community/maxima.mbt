// Port of src/homog.lisp: homogeneous polynomial reduction.

///|
fn addvardeg(n : Value, l : Value, lt : Value) -> Value raise {
  let mut lt = lt
  for x in l.iter() {
    lt = cons(cons(n, x), lt)
  }
  lt
}

///|
fn ptermvec(p : Value) -> Value raise {
  ltermvec(p, sort_list(listovars(p), (a, b) => pointergp(a, b).truthy()), Nil)
}

///|
fn nzeros(n : Value, l : Value) -> Value raise {
  let mut l = l
  for _i in 0..<to_int(n) {
    l = cons(int(0), l)
  }
  l
}

///|
fn ltermvec(p : Value, vl : Value, coef_q : Value) -> Value raise {
  if vl is Nil {
    list1(if coef_q.truthy() { p } else { Nil })
  } else if pcoefp(p).truthy() {
    list1(nzeros(int(length(vl)), if coef_q.truthy() { p } else { Nil }))
  } else if pointergp(car(vl), car(p)).truthy() {
    addvardeg(int(0), ltermvec(p, cdr(vl), coef_q), Nil)
  } else {
    let mut q = cdr(p)
    let mut lt : Value = Nil
    while !(q is Nil) {
      lt = addvardeg(car(q), ltermvec(cadr(q), cdr(vl), coef_q), lt)
      q = cddr(q)
    }
    lt
  }
}

///|
fn homog__ar(arr : Value, i : Value, j : Value) -> Value raise {
  aref(arr, [to_int(i), to_int(j)])
}

///|
fn homog__as(arr : Value, i : Value, j : Value, v : Value) -> Unit raise {
  aset(arr, [to_int(i), to_int(j)], v) |> ignore
}

///|
/// car(lv) = list of dependent equations
/// caddr (lv) = correspondence between new columns and old ones.
fn hlinsolve(mat : Value) -> Value raise {
  let n = length(mat) - 1
  let m = length(car(mat))
  let car_mat = car(mat)
  let mut mat = mapcar(x => mapcar2((a, b) => num_sub(a, b), car_mat, x), cdr(mat))
  let arr = make_array([1 + (if m > n { m } else { n }), 2 + m], initial=int(0))
  // solving for m vars
  let mut ml = mat
  let mut i = 1
  while !(ml is Nil) {
    let mut l = car(ml)
    let mut j = 1
    while true {
      if l is Nil {
        aset(arr, [i, j], int(0)) |> ignore
        break
      }
      aset(arr, [i, j], car(l)) |> ignore
      l = cdr(l)
      j += 1
    }
    ml = cdr(ml)
    i += 1
  }
  mat = tfgeli1(arr, int(n), int(1 + m))
  if cadr(mat).truthy() {
    merr("HLINSOLVE: inconsistent equations.", []) |> ignore // shouldn't happen
  }
  // # indep equations = n - (car mat)
  // # dependent vars = # indep equations
  // # indep vars = m - # dependent vars
  let ndepvar = n - length(car(mat))
  for i in (n + 1)..=m {
    for j in (ndepvar + 1)..=m {
      aset(arr, [i, j], int(0)) |> ignore
    }
  }
  let det = num_abs(aref(arr, [1, 1]))
  for i in (ndepvar + 1)..=m {
    aset(arr, [i, i], det) |> ignore
  }
  let a11 = aref(arr, [1, 1])
  if numberp(a11) && plusp(a11) {
    for i in 1..=ndepvar {
      for j in (ndepvar + 1)..=m {
        aset(arr, [i, j], num_neg(aref(arr, [i, j]))) |> ignore
      }
    }
  }
  // invert var permutation
  let mut l = caddr(mat)
  let mut i = 1
  while !(l is Nil) {
    homog__as(arr, int(0), car(l), int(i))
    l = cdr(l)
    i += 1
  }
  let mut varord = caddr(mat)
  let mut i = 1
  while i <= ndepvar {
    let mut gcd = int(0)
    let mut j = i
    while !(num_eq(gcd, int(1)) || j > m) {
      gcd = num_gcd(gcd, aref(arr, [i, j]))
      j += 1
    }
    homog__as(
      arr,
      car(varord),
      int(0),
      num_abs(num_truncate(aref(arr, [i, i]), b=gcd).0),
    )
    varord = cdr(varord)
    i += 1
  }
  while i <= m {
    let mut vecl : Value = Nil
    let mut j = m
    while j >= 1 {
      vecl = cons(homog__ar(arr, aref(arr, [0, j]), int(i)), vecl)
      j -= 1
    }
    homog__as(arr, car(varord), int(0), vecl)
    varord = cdr(varord)
    i += 1
  }
  let mut ans : Value = Nil
  let mut i = m
  while i >= 1 {
    ans = cons(aref(arr, [i, 0]), ans)
    i -= 1
  }
  ans
}

///|
/// returns (mixed list of <reduced exp> and <basis vector for null space>)
/// <reduced expon> corresponds to dependent var
/// <basis vector> corresponds to independent var
fn hreduce(p : Value, vl? : Value, hl? : Value) -> Value raise {
  let vl = match vl {
    Some(v) => v
    None =>
      set(
        q_n_starhvar,
        sort_list(listovars(p), (a, b) => pointergp(a, b).truthy()),
      )
  }
  let hl = match hl {
    Some(v) => v
    None =>
      set(q_n_starhmat, hlinsolve(ltermvec(p, symval(q_n_starhvar), Nil)))
  }
  if pcoefp(p).truthy() {
    p
  } else if pointergp(car(vl), car(p)).truthy() {
    hreduce(p, vl=cdr(vl), hl=cdr(hl))
  } else if numberp(car(hl)) {
    let mut q = cdr(p)
    let red = car(hl)
    let mut ans : Value = Nil
    while !(q is Nil) {
      ans = cons(num_truncate(car(q), b=red).0, ans)
      ans = cons(hreduce(cadr(q), vl=cdr(vl), hl=cdr(hl)), ans)
      q = cddr(q)
    }
    cons(car(p), nreverse(ans))
  } else {
    let mut sum = hreduce(caddr(p), vl=cdr(vl), hl=cdr(hl))
    let mut q = cdddr(p)
    while !(q is Nil) {
      sum = pplus(sum, hreduce(cadr(q), vl=cdr(vl), hl=cdr(hl)))
      q = cddr(q)
    }
    sum
  }
}

///|
fn hexpand(p : Value, hl? : Value, vl? : Value) -> Value raise {
  let hl = match hl {
    Some(v) => v
    None => symval(q_n_starhmat)
  }
  let vl = match vl {
    Some(v) => v
    None => symval(q_n_starhvar)
  }
  if every(x => onep(x).truthy(), hl) {
    return p
  }
  let mut p = p
  let pl = ltermvec(p, vl, t)
  let mut h = hl
  let mut i = 1
  while !(h is Nil) {
    if numberp(car(h)) && !onep(car(h)).truthy() {
      let mut q = pl
      while !(q is Nil) {
        let term = nthcdr(i - 1, car(q))
        rplaca(term, num_mul(car(term), car(h))) |> ignore
        q = cdr(q)
      }
    }
    h = cdr(h)
    i += 1
  }
  p = pl
  let mut h = hl
  let mut i = 1
  while !(h is Nil) {
    if !numberp(car(h)) {
      let ch = car(h)
      let wtlist = mapcar(x => hdot(ch, x), p)
      let newwt = nth(i - 1, car(h))
      let maxwt = reduce((a, b) => num_max(a, b), wtlist)
      let mut q = p
      let mut w = wtlist
      while !(q is Nil) {
        let term = nthcdr(i - 1, car(q))
        rplaca(term, num_truncate(num_sub(maxwt, car(w)), b=newwt).0) |> ignore
        q = cdr(q)
        w = cdr(w)
      }
    }
    h = cdr(h)
    i += 1
  }
  hsimp(p, vl)
}

///|
fn hdot(ht : Value, pt : Value) -> Value raise {
  let mut sum = num_mul(car(ht), car(pt))
  let mut ht = cdr(ht)
  let mut pt = cdr(pt)
  while !(ht is Nil) {
    sum = num_add(sum, num_mul(car(ht), car(pt)))
    ht = cdr(ht)
    pt = cdr(pt)
  }
  sum
}

///|
fn hsimp(pl : Value, vl : Value) -> Value raise {
  let mut p = hsimp1(car(pl), vl)
  let mut pl = cdr(pl)
  while !(pl is Nil) {
    p = pplus(p, hsimp1(car(pl), vl))
    pl = cdr(pl)
  }
  p
}

///|
fn hsimp1(tl : Value, vl : Value) -> Value raise {
  if vl is Nil {
    tl
  } else if num_gt(car(tl), int(0)) {
    list3(car(vl), car(tl), hsimp1(cdr(tl), cdr(vl)))
  } else {
    hsimp1(cdr(tl), cdr(vl))
  }
}
