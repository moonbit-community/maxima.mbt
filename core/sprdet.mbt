// Port of src/sprdet.lisp: the sparse determinant package.

///|
fn sprdet__ref(s : Value, i : Int) -> Int raise {
  to_int(aref1(symval(s), i))
}

///|
/// `(car (aref ax (aref *ptr* i) (aref *ptc* j)))`
fn sprdet__elt(ax : Value, i : Int, j : Int) -> Value raise {
  car(aref(ax, [sprdet__ref(q_ear_ptr, i), sprdet__ref(q_ear_ptc, j)]))
}

///|
fn sprdet(ax : Value, n : Value) -> Value raise {
  let ax = get_array_pointer(ax)
  let nn = to_int(n)
  let mut r = 0
  set(q_ear_ptr, make_array([1 + nn], initial=Fix(0L))) |> ignore
  set(q_ear_ptc, make_array([1 + nn], initial=Fix(0L))) |> ignore
  let mut bl = tmlattice(ax, q_ear_ptr, q_ear_ptc, n)
  if bl is Nil {
    return Fix(0L)
  }
  let mut rodr : Value = Nil
  for b in reverse(bl).iter() {
    rodr = append(b, rodr)
  }
  let codr = mapcar(x => cadr(x), rodr)
  rodr = mapcar(x => car(x), rodr)
  let mut det = num_mul(prmusign(rodr), prmusign(codr))
  bl = mapcar(x => int(length(x)), bl)
  while bl.truthy() {
    let dm = to_int(car(bl))
    set(q_ear_blk, make_array([1 + dm, 1 + dm], initial=Fix(0L))) |> ignore
    if dm == 1 {
      det = gptimes(det, sprdet__elt(ax, 1 + r, 1 + r))
    } else if dm == 2 {
      det = gptimes(
        det,
        gpdifference(
          gptimes(sprdet__elt(ax, 1 + r, 1 + r), sprdet__elt(ax, 2 + r, 2 + r)),
          gptimes(sprdet__elt(ax, 1 + r, 2 + r), sprdet__elt(ax, 2 + r, 1 + r)),
        ),
      )
    } else {
      let mut i = dm
      while i != 0 {
        let mut j = dm
        while j != 0 {
          aset(symval(q_ear_blk), [i, j], sprdet__elt(ax, r + i, r + j))
          |> ignore
          j = j - 1
        }
        i = i - 1
      }
      det = gptimes(det, tdbu(q_ear_blk, int(dm)))
    }
    r = r + dm
    bl = cdr(bl)
  }
  det
}

///|
fn minorl(x : Value, n : Value, l : Value, nz : Value) -> Value raise {
  with_special(q_rzl_star, Nil, () => {
    let mut ans : Value = Nil
    let mut s : Value = Nil
    let mut col = 1
    let n2 = num_truncate(n, b=Fix(2L)).0
    let n2 = to_int(n2) - 1
    let mut d : Value = Nil
    let mut dl = l
    let mut l : Value = Nil
    let mut nz = cons(Nil, nz)
    let mut z : Value = Nil
    let mut a : Value = Nil
    let mut elm : Value = Nil
    let mut rule : Value = Nil
    // States: 1 = L1, 3 = L3, 2 = L2, 4 = ON
    let mut state = 1
    while true {
      match state {
        1 => {
          if nz is Nil {
            return ans
          }
          state = 3
        }
        3 => {
          z = car(nz)
          if l is Nil {
            if dl.truthy() {
              ans = cons(dl, ans)
            } else {
              return Nil
            }
            nz = cdr(nz)
            col = col + 1
            l = dl
            dl = Nil
            state = 1
          } else {
            a = caar(l)
            state = 2
          }
        }
        2 => {
          if z is Nil {
            if rule.truthy() {
              rplaca(car(l), list2(a, rule)) |> ignore
              rule = Nil
              l = cdr(l)
            } else if cdr(l) is Nil {
              rplaca(car(l), list2(a, Fix(0L))) |> ignore
              l = cdr(l)
            } else {
              rplaca(l, cadr(l)) |> ignore
              rplacd(l, cddr(l)) |> ignore
            }
            state = 3
            continue
          }
          elm = car(z)
          z = cdr(z)
          s = signnp(elm, a)
          if s.truthy() {
            d = remove_equal(elm, copy_list(a))
            if membercar(d, dl).truthy() {
              state = 4
            } else if col < n2 || !singp(x, d, int(col), n).truthy() {
              dl = cons(cons(d, Fix(1L)), dl)
              state = 4
            }
          }
        }
        _ => {
          rule = cons(list([d, s, elm, int(col - 1)]), rule)
          state = 2
        }
      }
    }
    Nil
  })
}

///|
fn singp(x : Value, ml : Value, col : Value, n : Value) -> Value raise {
  let mut j = to_int(col)
  let n = to_int(n)
  let l = ml
  if ml.truthy() {
    let i = car(ml)
    if member_equal(i, symval(q_rzl_star)).truthy() {
      return t
    } else if zrow(x, i, col, int(n)).truthy() {
      return set(q_rzl_star, cons(i, symval(q_rzl_star)))
    }
  }
  while true {
    if j > n {
      return Nil
    }
    let jj = j
    if every(i => equal(aref(x, [to_int(i), jj]), Fix(0L)), l) {
      return t
    }
    j = j + 1
  }
  Nil
}

///|
fn tdbu(x : Value, n : Value) -> Value raise {
  with_special(q_ml_star, Nil, () => {
    set(q_ear_detsign, Fix(1L)) |> ignore
    let x = get_array_pointer(x)
    detpivot(x, n) |> ignore
    let x = get_array_pointer(q_x_star)
    let nl = nzl(x, n)
    if memq(Nil, nl).truthy() {
      return Fix(0L)
    }
    let mut a = minorl(
      x,
      n,
      list1(cons(nreverse(index_star(n)), Fix(1L))),
      nl,
    )
    if a is Nil {
      return Fix(0L)
    }
    tb2(x, car(a), n) |> ignore
    while true {
      set(q_ml_star, cons(cons(Nil, Nil), car(a))) |> ignore
      a = cdr(a)
      if a is Nil {
        return if num_eq(symval(q_ear_detsign), Fix(1L)) {
          cadadr(symval(q_ml_star))
        } else {
          gpctimes(Fix(-1L), cadadr(symval(q_ml_star)))
        }
      }
      let mut nml = car(a)
      while nml.truthy() {
        let dd = car(nml)
        nml = cdr(nml)
        nbn(dd, x) |> ignore
      }
    }
    Nil
  })
}

///|
fn nbn(rule : Value, x : Value) -> Value raise {
  let mut ans : Value = Fix(0L)
  let mut r = cadar(rule)
  if equal(r, Fix(0L)) {
    return Fix(0L)
  }
  rplaca(rule, caar(rule)) |> ignore
  while r.truthy() {
    let a = car(r)
    r = cdr(r)
    let e = aref(x, [to_int(caddr(a)), to_int(cadddr(a))])
    ans = gpplus(
      ans,
      gptimes(
        if num_eq(cadr(a), Fix(1L)) {
          e
        } else {
          gpctimes(cadr(a), e)
        },
        getminor(car(a)),
      ),
    )
  }
  rplacd(rule, cons(ans, cdr(rule)))
}

///|
/// Destructive `(delete item l :test #'equal)`.
fn sprdet__ndelete_equal(item : Value, l : Value) -> Value {
  let mut head = l
  while head is Cons(_) && equal(car(head), item) {
    head = cdr(head)
  }
  let mut p = head
  while cdr(p) is Cons(_) {
    if equal(cadr(p), item) {
      rplacd(p, cddr(p)) |> ignore
    } else {
      p = cdr(p)
    }
  }
  head
}

///|
fn getminor(index : Value) -> Value raise {
  let mut index = assoc_equal(index, symval(q_ml_star))
  if index is Nil {
    Fix(0L)
  } else {
    rplacd(cdr(index), one_minus(cddr(index))) |> ignore
    if num_eq(cddr(index), Fix(0L)) {
      index = sprdet__ndelete_equal(index, symval(q_ml_star))
    }
    cadr(index)
  }
}

///|
fn tb2(x : Value, l : Value, n : Value) -> Value raise {
  let n = to_int(n)
  let n_1 = n - 1
  let mut l = l
  while l.truthy() {
    let a = car(l)
    l = cdr(l)
    let b = car(a)
    let r0 = to_int(car(b))
    let r1 = to_int(cadr(b))
    rplacd(
      a,
      cons(
        gpdifference(
          gptimes(aref(x, [r0, n_1]), aref(x, [r1, n])),
          gptimes(aref(x, [r0, n]), aref(x, [r1, n_1])),
        ),
        cdr(a),
      ),
    )
    |> ignore
  }
  Nil
}

///|
fn zrow(x : Value, i : Value, col : Value, n : Value) -> Value raise {
  let i = to_int(i)
  let n = to_int(n)
  let mut j = to_int(col)
  while true {
    if j > n {
      return t
    } else if equal(aref(x, [i, j]), Fix(0L)) {
      j = j + 1
    } else {
      return Nil
    }
  }
  Nil
}

///|
fn nzl(a : Value, n : Value) -> Value raise {
  let n = to_int(n)
  let mut j = n - 2
  let mut d : Value = Nil
  let mut l : Value = Nil
  while j != 0 {
    let mut i = n
    while i != 0 {
      if !equal(aref(a, [i, j]), Fix(0L)) {
        d = cons(int(i), d)
      }
      i = i - 1
    }
    l = cons(d, l)
    d = Nil
    j = j - 1
  }
  l
}

///|
fn signnp(e : Value, l : Value) -> Value raise {
  let mut i = 1
  let mut l = l
  while l.truthy() {
    if equal(e, car(l)) {
      return int(i)
    }
    l = cdr(l)
    i = -i
  }
  Nil
}

///|
fn membercar(e : Value, l : Value) -> Value raise {
  let mut l = l
  while l.truthy() {
    if equal(e, caar(l)) {
      return rplacd(car(l), one_plus(cdar(l)))
    }
    l = cdr(l)
  }
  Nil
}

///|
fn atranspose(a : Value, n : Value) -> Value raise {
  let n = to_int(n)
  for i in 1..=n {
    for j in (i + 1)..=n {
      let d = aref(a, [i, j])
      aset(a, [i, j], aref(a, [j, i])) |> ignore
      aset(a, [j, i], d) |> ignore
    }
  }
  Nil
}

///|
fn mxcomp(l1 : Value, l2 : Value) -> Value raise {
  let mut l1 = l1
  let mut l2 = l2
  while true {
    if l1 is Nil {
      return t
    } else if car_gt(car(l1), car(l2)).truthy() {
      return t
    } else if car_gt(car(l2), car(l1)).truthy() {
      return Nil
    }
    l1 = cdr(l1)
    l2 = cdr(l2)
  }
  Nil
}

///|
fn prmusign(l : Value) -> Value raise {
  let mut b = 0
  let mut l = l
  while l.truthy() {
    let a = car(l)
    l = cdr(l)
    let mut d = l
    while d.truthy() {
      if num_gt(a, car(d)) {
        b = b + 1
      }
      d = cdr(d)
    }
  }
  if b % 2 == 0 {
    Fix(1L)
  } else {
    Fix(-1L)
  }
}

///|
fn detpivot(x : Value, n : Value) -> Value raise {
  let car_gt_fn = lfunc("car>", args => car_gt(arg(args, 0), arg(args, 1)))
  let mut c0 = colrow0(x, n, Nil)
  let mut r0 = colrow0(x, n, t)
  c0 = nreverse(bbsort(c0, car_gt_fn))
  r0 = nreverse(bbsort(r0, car_gt_fn))
  if !mxcomp(c0, r0).truthy() {
    atranspose(x, n) |> ignore
    c0 = r0
  }
  set(q_ear_detsign, prmusign(mapcar(e => car(e), c0))) |> ignore
  newmat(q_x_star, x, n, c0)
}

///|
fn newmat(x : Value, y : Value, n : Value, l : Value) -> Value raise {
  let n = to_int(n)
  set(x, make_array([1 + n, 1 + n], initial=Fix(0L))) |> ignore
  let x = get_array_pointer(x)
  let mut j = 0
  let mut l = l
  while true {
    j = j + 1
    if l is Nil {
      return Nil
    }
    let jl = to_int(cdar(l))
    l = cdr(l)
    for i in 1..=n {
      aset(x, [i, j], aref(y, [i, jl])) |> ignore
    }
  }
  Nil
}

///|
fn car_gt(a : Value, b : Value) -> Value raise {
  lbool(num_gt(car(a), car(b)))
}

///|
/// ind=t for row otherwise col
fn colrow0(a : Value, n : Value, ind : Value) -> Value raise {
  let n = to_int(n)
  let mut j = n
  let mut l : Value = Nil
  let mut c = 0
  while j != 0 {
    let mut i = n
    while i != 0 {
      let e = if ind.truthy() { aref(a, [j, i]) } else { aref(a, [i, j]) }
      if equal(e, Fix(0L)) {
        c = c + 1
      }
      i = i - 1
    }
    l = cons(cons(int(c), int(j)), l)
    c = 0
    j = j - 1
  }
  l
}

///|
fn gpdifference(a : Value, b : Value) -> Value raise {
  if symval(q_d_ratmx).truthy() {
    pdifference(a, b)
  } else {
    simplus(
      list3(list1(q_mplus), a, list3(list1(q_mtimes), Fix(-1L), b)),
      Fix(1L),
      Nil,
    )
  }
}

///|
fn gpctimes(a : Value, b : Value) -> Value raise {
  if symval(q_d_ratmx).truthy() {
    pctimes(a, b)
  } else {
    simptimes(list3(list1(q_mtimes), a, b), Fix(1L), Nil)
  }
}

///|
fn gptimes(a : Value, b : Value) -> Value raise {
  if symval(q_d_ratmx).truthy() {
    ptimes(a, b)
  } else {
    simptimes(list3(list1(q_mtimes), a, b), Fix(1L), Nil)
  }
}

///|
fn gpplus(a : Value, b : Value) -> Value raise {
  if symval(q_d_ratmx).truthy() {
    pplus(a, b)
  } else {
    simplus(list3(list1(q_mplus), a, b), Fix(1L), Nil)
  }
}
