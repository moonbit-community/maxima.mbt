// Port of src/newinv.lisp: inversion of sparse matrices by blocks, using
// the lattice (block) structure found by TMLATTICE.

///|
fn multbk(l : Value, ax : Value, m : Value) -> Value raise {
  let m = to_int(m)
  let mut l = l
  for j in (m + 1)..=(2 * m) {
    let e = car(l)
    l = cdr(l)
    for i in 1..=m {
      aset(ax, [i, j], rattimes(e, aref(ax, [i, j]), t)) |> ignore
    }
  }
  Nil
}

///|
fn ctimemt(x : Value, y : Value) -> Value raise {
  let mut c : Value = Nil
  let mut y = y
  while y.truthy() {
    c = nconc(c, list1(timesrow(x, car(y))))
    y = cdr(y)
  }
  c
}

///|
fn newinv__ptr(i : Int) -> Int raise {
  to_int(aref1(symval(q_ear_ptr), i))
}

///|
fn newinv__ptc(j : Int) -> Int raise {
  to_int(aref1(symval(q_ear_ptc), j))
}

///|
fn stora(ax : Value, m : Value, ei : Value, r : Value) -> Value raise {
  let m = to_int(m)
  let r = to_int(r)
  let mut i = 0
  let mut ei = ei
  while ei.truthy() {
    let mut mat = car(ei)
    ei = cdr(ei)
    let det = caar(mat)
    mat = cdr(mat)
    while mat.truthy() {
      let mut j = r
      i = i + 1
      let mut ro = car(mat)
      mat = cdr(mat)
      while ro.truthy() {
        j = j + 1
        aset(ax, [i, m + j], ratreduce(caar(ro), det)) |> ignore
        aset(ax, [newinv__ptr(i), newinv__ptc(j)], Nil) |> ignore
        ro = cdr(ro)
      }
    }
  }
  Nil
}

///|
fn prodhk(ax : Value, ri : Value, d : Value, r : Value, m : Value) -> Value raise {
  with_special(q_ear_rr, Nil, () => {
    let n_starr0 = r
    let mut ei = ri
    let mut co : Value = Nil
    while ei.truthy() {
      let e = car(ei)
      ei = cdr(ei)
      co = cons(bmhk(ax, e, d, co, r, symval(q_detl_star), n_starr0), co)
    }
    stora(ax, m, append(co, list1(d)), r) |> ignore
    set(q_detl_star, cons(car(d), symval(q_detl_star))) |> ignore
    cons(
      list1(d),
      mapcar2((x, y) => nconc(x, list1(y)), ri, nreverse(symval(q_ear_rr))),
    )
  })
}

///|
fn obmtrx(ax : Value, r : Value, s : Value, i : Value, j : Value) -> Value raise {
  let mut ans : Value = Nil
  let mut dr : Value = Nil
  let mut r = to_int(r)
  let mut s = to_int(s)
  let mut i = to_int(i)
  let mut j = to_int(j)
  let ds = s
  let dj = j
  while i != 0 {
    if j == 0 {
      j = dj
      s = ds
      ans = cons(nreverse(dr), ans)
      dr = Nil
      r = r - 1
      i = i - 1
      continue
    }
    s = s + 1
    j = j - 1
    let d = aref(ax, [newinv__ptr(r), newinv__ptc(s)])
    if !(symval(q_ear_nonz).truthy() || equal(d, Fix(0L))) {
      set(q_ear_nonz, t) |> ignore
    }
    dr = cons(d, dr)
  }
  ans
}

///|
fn bmhk(
  ax : Value,
  da : Value,
  b : Value,
  nc : Value,
  c0 : Value,
  detl : Value,
  n_starr0 : Value,
) -> Value raise {
  with_special(q_ear_nonz, Nil, () => {
    let mut det = car(b)
    let b = cdr(b)
    let a = car(da)
    let mut da = cdr(da)
    let mut nc = reverse(nc)
    let mut detl = detl
    da = reverse(da)
    let c = obmtrx(ax, n_starr0, c0, int(length(cdr(a))), int(length(b)))
    set(q_ear_rr, cons(c, symval(q_ear_rr))) |> ignore
    if symval(q_ear_nonz) is Nil {
      return cons(cons(Fix(1L), Fix(1L)), c)
    }
    let mut sum = multmat(c, b)
    while da.truthy() {
      let x = car(da)
      let mut y = car(nc)
      let dy = car(y)
      y = cdr(y)
      let x = multmat(x, y)
      sum = addmatrix1(ctimemt(cons(pminus(caar(detl)), Fix(1L)), sum), x)
      det = dy
      detl = cdr(detl)
      da = cdr(da)
      nc = cdr(nc)
    }
    det = cons(ptimes(pminus(caar(a)), car(det)), Fix(1L))
    cons(det, multmat(cdr(a), sum))
  })
}

///|
/// tmlattice returns the block structure in the form of a list of blocks
/// each in the form of ((i1 j1) (i2 j2) etc))
fn newinv(ax : Value, m : Value, n : Value) -> Value raise {
  with_special(q_detl_star, Nil, () => {
    let mm = to_int(m)
    let mut mmat : Value = Nil
    let mut i = mm
    while i != 0 {
      mmat = cons(aref(ax, [i, i + mm]), mmat)
      i = i - 1
    }
    set(q_ear_ptr, make_array([1 + mm], initial=Fix(0L))) |> ignore
    set(q_ear_ptc, make_array([1 + mm], initial=Fix(0L))) |> ignore
    let mut bl = tmlattice(ax, q_ear_ptr, q_ear_ptc, m)
    if bl is Nil {
      merr("newinv: matrix is singular.", []) |> ignore
    }
    bl = mapcar(x => int(length(x)), bl)
    // (apply #'max bl)
    let mut bm = car(bl)
    for x in cdr(bl).iter() {
      bm = num_max(bm, x)
    }
    let bm = to_int(bm)
    set(q_ear_iar, make_array([1 + bm, 1 + 2 * bm], initial=Fix(0L))) |> ignore
    let mut r = 0
    let mut ei : Value = Nil
    let one = cons(Fix(1L), Fix(1L))
    let zero = cons(Fix(0L), Fix(1L))
    while bl.truthy() {
      let mut i = to_int(car(bl))
      let dm = i
      let dm2 = 2 * dm
      while i != 0 {
        let mut j = dm2
        let ipdm = i + dm
        while j != 0 {
          let v = if j > dm {
            if j == ipdm {
              one
            } else {
              zero
            }
          } else {
            aref(ax, [newinv__ptr(r + i), newinv__ptc(r + j)])
          }
          aset(symval(q_ear_iar), [i, j], v) |> ignore
          j = j - 1
        }
        i = i - 1
      }
      if r == 0 {
        ei = tmlin(q_ear_iar, int(dm), int(dm), int(dm))
        ei = list1(cons(caar(ei), cdr(ei)))
        stora(ax, m, ei, int(r)) |> ignore
        ei = list1(ei)
      } else {
        let mut d = tmlin(q_ear_iar, int(dm), int(dm), int(dm))
        d = cons(caar(d), cdr(d))
        ei = prodhk(ax, ei, d, int(r), m)
      }
      r = r + to_int(car(bl))
      bl = cdr(bl)
    }
    tmunpivot(ax, q_ear_ptr, q_ear_ptc, m, n) |> ignore
    multbk(mmat, ax, m)
  })
}
