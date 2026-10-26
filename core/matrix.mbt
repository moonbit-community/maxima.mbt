// Port of src/matrix.lisp: matrix arithmetic, determinants, inversion by
// Gaussian elimination, echelon and triangular forms, and matrix utilities.

///|
/// Matrix to MACSYMA conversion
fn mxc(x : Value) -> Value raise {
  mapcar(y => cons(list1(q_mlist), y), x)
}

///|
/// MACSYMA to Matrix conversion
fn mcx(x : Value) -> Value raise {
  mapcar(y => cdr(y), x)
}

///|
/// Transpose a list of lists ll. Example: ((1 2) (3 4)) --> ((1 3) (2 4)).
fn transpose(ll : Value) -> Value raise {
  let mut acc : Value = Nil
  let mut ll = ll
  while car(ll).truthy() {
    acc = cons(mapcar(x => car(x), ll), acc)
    ll = mapcar(x => cdr(x), ll)
  }
  nreverse(acc)
}

///|
fn nthcol(x : Value, nn : Value) -> Value raise {
  if x is Nil || num_gt(nn, int(length(car(x)))) {
    Nil
  } else {
    nthcol1(x, nn)
  }
}

///|
fn nthcol1(x : Value, nn : Value) -> Value raise {
  if x is Nil || num_eq(nn, Fix(0L)) {
    Nil
  } else {
    cons(ith(car(x), nn), nthcol1(cdr(x), nn))
  }
}

///|
fn check(x : Value) -> Value raise {
  if atom(x) {
    merr("not a matrix: ~M", [x])
  } else if eq(caar(x), q_d_matrix) {
    x
  } else if eq(caar(x), q_mlist) {
    list2(list1(q_d_matrix), x)
  } else {
    merr("not a matrix: ~M", [x])
  }
}

///|
fn check1(x : Value) -> Value raise {
  if atom(x) {
    Nil
  } else if eq(caar(x), q_d_matrix) {
    x
  } else if eq(caar(x), q_mlist) {
    list2(list1(q_d_matrix), x)
  } else {
    Nil
  }
}

///|
fn d_matrixp(x : Value) -> Value raise {
  lbool(!atom(x) && eq(caar(x), q_d_matrix))
}

///|
fn d_charpoly(mat : Value, var_ : Value) -> Value raise {
  let mut mat = check(mat)
  if length(mat) != length(cadr(mat)) {
    merr(
      "charpoly: matrix must be square; found ~M rows, ~M columns.",
      [int(length(mat)), int(length(cadr(mat)))],
    )
    |> ignore
  }
  if !symval(q_d_ratmx).truthy() {
    mat = mcx(cdr(mat))
    det1(
      addmatrix1(
        mat,
        diagmatrix(
          int(length(mat)),
          list3(list1(q_mtimes), Fix(-1L), var_),
          q_d_charpoly,
        ),
      ),
    )
  } else {
    newvar(var_) |> ignore
    newvarmat1(mat) |> ignore
    mat = mcx(cdr(mat))
    determinant1(
      addmatrix(
        mat,
        diagmatrix(
          int(length(mat)),
          list3(list1(q_mtimes), Fix(-1L), var_),
          q_d_charpoly,
        ),
      ),
    )
  }
}

///|
fn disreplist1(a : Value) -> Value raise {
  set(q_header, list([q_mrat, q_simp, symval(q_varlist), symval(q_genvar)]))
  |> ignore
  mapcar(x => disreplist(x), a)
}

///|
fn disreplist(a : Value) -> Value raise {
  mapcar(e => cons(symval(q_header), e), a)
}

///|
fn replist1(a : Value) -> Value raise {
  mapcar(x => replist(x), a)
}

///|
fn replist(a : Value) -> Value raise {
  mapcar(e => cdr(ratrep_star(e)), a)
}

///|
fn timex(mat1 : Value, mat2 : Value) -> Value raise {
  if equal(mat1, Fix(1L)) {
    mat2
  } else if d_matrixp(mat1).truthy() &&
    d_matrixp(mat2).truthy() &&
    cdr(mat1) is Nil {
    list1(list2(q_d_matrix, q_simp))
  } else {
    newvarmat(mat1, mat2) |> ignore
    let smp = if d_listp(mat1).truthy() && d_listp(mat2).truthy() {
      t
    } else {
      symval(q_d_scalarmatrixp)
    }
    with_special(q_d_scalarmatrixp, smp, () => simplifya(timex0(mat1, mat2), Nil))
  }
}

///|
fn lnewvar(a : Value) -> Value raise {
  with_special(q_vlist, Nil, () => {
    lnewvar1(a) |> ignore
    set(q_varlist, nconc(sortgreat(symval(q_vlist)), symval(q_varlist)))
  })
}

///|
fn lnewvar1(a : Value) -> Value raise {
  if atom(a) {
    newvar1(a)
  } else if mbagp(a).truthy() {
    mapc(x => lnewvar1(x) |> ignore, cdr(a))
  } else {
    newvar1(a)
  }
}

///|
fn newvarmat(mat1 : Value, mat2 : Value) -> Value raise {
  if symval(q_d_ratmx).truthy() {
    with_special(q_vlist, Nil, () => {
      lnewvar1(mat1) |> ignore
      lnewvar1(mat2) |> ignore
      set(q_varlist, nconc(sortgreat(symval(q_vlist)), symval(q_varlist)))
    })
  } else {
    Nil
  }
}

///|
fn newvarmat1(a : Value) -> Value raise {
  if symval(q_d_ratmx).truthy() {
    lnewvar(a)
  } else {
    Nil
  }
}

///|
fn addmatrix(x : Value, y : Value) -> Value raise {
  let x = replist1(x)
  let y = replist1(y)
  disreplist1(addmatrix1(x, y))
}

///|
fn addmatrix1(b : Value, c : Value) -> Value raise {
  if !(length(b) == length(c) && length(car(b)) == length(car(c))) {
    merr("ADDMATRIX1: attempt to add nonconformable matrices.", []) |> ignore
  }
  mapcar2((x, y) => addrows(x, y), b, c)
}

///|
fn addrows(a : Value, b : Value) -> Value raise {
  if !symval(q_d_ratmx).truthy() {
    mapcar2(
      (i, j) => simplus(list3(list1(q_mplus), i, j), Fix(1L), Nil),
      a,
      b,
    )
  } else {
    mapcar2((x, y) => ratplus(x, y), a, b)
  }
}

///|
fn d_determinant(mat : Value) -> Value raise {
  if !(mbagp(mat).truthy() || d_matrixp(mat).truthy()) {
    if d_scalarp(mat).truthy() {
      mat
    } else {
      list2(list1(q_p_determinant), mat)
    }
  } else {
    let mat = check(mat)
    if length(mat) != length(cadr(mat)) {
      merr(
        "determinant: matrix must be square; found ~M rows, ~M columns.",
        [int(length(cdr(mat))), int(length(cdadr(mat)))],
      )
      |> ignore
    }
    if !symval(q_d_ratmx).truthy() {
      det1(mcx(cdr(mat)))
    } else {
      newvarmat1(mat) |> ignore
      determinant1(mcx(cdr(mat)))
    }
  }
}

///|
fn det(m : Value) -> Value raise {
  if length(m) == 1 {
    caar(m)
  } else {
    with_specials([(q_ear_det, Nil), (q_mul_star, Nil)], () => {
      let n = set(q_ear_det, int(length(m)))
      mtoa(q_ear_mat, n, symval(q_ear_det), m) |> ignore
      let d = symval(q_ear_det)
      set(q_ear_det, tfgeli0(q_ear_mat, d, d)) |> ignore
      ratreduce(symval(q_ear_det), symval(q_mul_star))
    })
  }
}

///|
fn determinant1(x : Value) -> Value raise {
  catch_tag(q_dz, () => rdis(det(replist1(x))))
}

///|
fn treedet(mat : Value) -> Value raise {
  with_special(q_mdl, Nil, () => {
    let mut mat = reverse(mat)
    let n = length(mat)
    let mut md = car(mat)
    mat = cdr(mat)
    let lindex = nreverse(index_star(int(n)))
    let mut tuplel = mapcar(x => list1(x), lindex)
    while true {
      if mat is Nil {
        return car(md)
      }
      set(q_mdl, Nil) |> ignore
      mapcar2(
        (a, b) => {
          set(q_mdl, nconc(symval(q_mdl), list2(a, b))) |> ignore
          Nil
        },
        tuplel,
        md,
      )
      |> ignore
      md = Nil
      let row = car(mat)
      mat = cdr(mat)
      tuplel = nextlevel(tuplel, lindex)
      let mut lt = tuplel
      while lt.truthy() {
        let id = car(lt)
        lt = cdr(lt)
        md = cons(compumd(id, row), md)
      }
      md = nreverse(md)
    }
    Nil
  })
}

///|
fn assoo(e : Value, l : Value) -> Value raise {
  let mut l = l
  while true {
    if l is Nil {
      return Nil
    } else if equal(e, car(l)) {
      return cadr(l)
    }
    l = cddr(l)
  }
  Nil
}

///|
fn compumd(id : Value, row : Value) -> Value raise {
  let mut ans : Value = Fix(0L)
  let mut sign : Value = Fix(-1L)
  let mut i = id
  while i.truthy() {
    let d = car(i)
    i = cdr(i)
    sign = num_mul(Fix(-1L), sign)
    let e = ith(row, d)
    if equal(e, Fix(0L)) {
      continue
    }
    let minor = assoo(delete(d, copy_tree(id)), symval(q_mdl))
    if equal(minor, Fix(0L)) {
      continue
    }
    ans = if equal(symval(q_d_matrix_element_mult), Str("*")) &&
      equal(symval(q_d_matrix_element_add), Str("+")) {
      add2(ans, muln_([sign, e, minor])) // fast common case
    } else {
      mapply(
        symval(q_d_matrix_element_add),
        list2(
          ans,
          mapply(
            symval(q_d_matrix_element_mult),
            list3(sign, e, minor),
            symval(q_d_matrix_element_mult),
          ),
        ),
        symval(q_d_matrix_element_add),
      )
    }
  }
  ans
}

///|
fn apdl(l1 : Value, l2 : Value) -> Value raise {
  mapcar(j => append(l1, list1(j)), l2)
}

///|
fn nextlevel(tuplel : Value, lindex : Value) -> Value raise {
  let mut ans : Value = Nil
  let mut tuplel = tuplel
  while tuplel.truthy() {
    let l = car(tuplel)
    tuplel = cdr(tuplel)
    let li = cdr(nthcdr(to_int(car(last(l))) - 1, lindex))
    if li is Nil {
      continue
    }
    ans = nconc(ans, apdl(l, li))
  }
  ans
}

///|
fn det1(x : Value) -> Value raise {
  if symval(q_d_sparse).truthy() {
    mtoa(
      q_ear_mat,
      int(length(x)),
      int(length(x)),
      mapcar(x => mapcar(y => list1(y), x), x),
    )
    |> ignore
    sprdet(q_ear_mat, int(length(x)))
  } else {
    treedet(x)
  }
}

///|
fn d_ident(n : Value) -> Value raise {
  cons(list1(q_d_matrix), mxc(diagmatrix(n, Fix(1L), q_d_ident)))
}

///|
fn d_diagmatrix(n : Value, var_ : Value) -> Value raise {
  cons(list1(q_d_matrix), mxc(diagmatrix(n, var_, q_d_diagmatrix)))
}

///|
fn diagmatrix(n : Value, var_ : Value, fn_ : Value) -> Value raise {
  if !fixnump(n) || minusp(n) {
    improper_arg_err(n, fn_) |> ignore
  }
  let mut i = n
  let mut ans : Value = Nil
  while !zerop(i) {
    ans = cons(onen(i, n, var_, Fix(0L)), ans)
    i = one_minus(i)
  }
  ans
}

///|
/// ATOMAT GENERATES A MATRIX FROM A MXN ARRAY BY TAKING COLUMNS S TO N
fn atomat(name : Value, m : Value, n : Value, s : Value) -> Value raise {
  let name = get_array_pointer(name)
  let mut row : Value = Nil
  let mut mat : Value = Nil
  let mut m = to_int(m) + 1
  let n = to_int(n) + 1
  let s = to_int(s)
  while m != 1 {
    m = m - 1
    let mut j = n
    while j != s {
      j = j - 1
      let d = if symval(q_top_star).truthy() {
        meval(list3(list2(name, q_array), int(m), int(j)))
      } else {
        aref(name, [m, j])
      }
      row = cons(if d.truthy() { d } else { cons(Fix(0L), Fix(1L)) }, row)
    }
    mat = cons(row, mat)
    row = Nil
  }
  mat
}

///|
fn d_invert_by_gausselim(k : Value) -> Value raise {
  let ratmx = symval(q_d_ratmx)
  with_specials(
    [
      (q_ear_inv, t),
      (q_ear_det, Nil),
      (q_top_star, Nil),
      (q_mul_star, Nil),
      (q_d_ratmx, t),
      (q_d_ratfac, Nil),
      (q_d_sparse, Nil),
    ],
    () => if atom(k) {
      d_nounify(q_d_inverx) |> ignore
      list2(list1(q_p_inverx), k)
    } else {
      let mut k = check(k)
      newvarmat1(k) |> ignore
      k = invert1(replist1(mcx(cdr(k))))
      k = if symval(q_d_detout).truthy() {
        let d = symval(q_ear_det)
        list3(
          list1(q_mtimes),
          list3(
            list1(q_mexpt),
            rdis(if d.truthy() { d } else { cons(Fix(1L), Fix(1L)) }),
            Fix(-1L),
          ),
          cons(list1(q_d_matrix), mxc(disreplist1(k))),
        )
      } else {
        cons(list1(q_d_matrix), mxc(disreplist1(k)))
      }
      if ratmx.truthy() && !symval(q_d_detout).truthy() {
        fmapl1(lfunc("identity", args => arg(args, 0)), list1(k))
      } else if !ratmx.truthy() {
        d_totaldisrep(k)
      } else {
        k
      }
    },
  )
}

///|
fn diaginv(ax : Value, m : Value) -> Value raise {
  let ax = get_array_pointer(ax)
  let m = to_int(m)
  if symval(q_d_detout).truthy() {
    set(q_ear_det, Fix(1L)) |> ignore
    for i in 1..=m {
      set(q_ear_det, plcm(symval(q_ear_det), car(aref(ax, [i, i])))) |> ignore
    }
    set(q_ear_det, cons(symval(q_ear_det), Fix(1L))) |> ignore
  }
  for i in 1..=m {
    let elm = aref(ax, [i, i])
    aset(
      ax,
      [i, m + i],
      if symval(q_d_detout).truthy() {
        cons(
          ptimes(cdr(elm), pquotient(car(symval(q_ear_det)), car(elm))),
          Fix(1L),
        )
      } else {
        ratinvert(elm)
      },
    )
    |> ignore
  }
  Nil
}

///|
fn invert1(k : Value) -> Value raise {
  let l = length(k)
  let mut i = 1
  if l != length(car(k)) {
    merr("invert: matrix must be square; found ~M rows, ~M columns.", [
      int(l),
      int(length(car(k))),
    ])
    |> ignore
  }
  let one = cons(Fix(1L), Fix(1L))
  let zero = cons(Fix(0L), Fix(1L))
  let mut k = k
  let mut g : Value = Nil
  while k.truthy() {
    let r = car(k)
    g = nconc(g, list1(nconc(r, onen(int(i), int(l), one, zero))))
    k = cdr(k)
    i = i + 1
  }
  k = g
  let m = int(length(k))
  let n = int(length(car(k)))
  mtoa(q_ear_mat, m, n, k) |> ignore
  if diagp(q_ear_mat, m).truthy() {
    diaginv(q_ear_mat, m) |> ignore
  } else {
    tfgeli0(q_ear_mat, m, n) |> ignore
  }
  atomat(q_ear_mat, m, n, one_plus(m))
}

///|
fn diagp(ax : Value, m : Value) -> Value raise {
  let m = to_int(m)
  let ax = get_array_pointer(ax)
  let zero = cons(Fix(0L), Fix(1L))
  for i in 1..=m {
    for j in 1..=m {
      if i != j && equal(aref(ax, [i, j]), zero) {
        ()
      } else if i == j && !equal(aref(ax, [i, j]), zero) {
        ()
      } else {
        return Nil
      }
    }
  }
  t
}

///|
fn tfgeli0(x : Value, m : Value, n : Value) -> Value raise {
  if symval(q_d_sparse).truthy() || symval(q_ear_det).truthy() {
    tfgeli(x, m, n)
  } else {
    tfgeli(x, m, n) |> ignore
    diaglize1(x, m, n)
  }
}

// TWO-STEP FRACTION-FREE GAUSSIAN ELIMINATION ROUTINE

///|
fn ritediv(x : Value, m : Value, n : Value, a : Value) -> Value raise {
  let x = get_array_pointer(x)
  let m = to_int(m)
  let n = to_int(n)
  let mut i = m
  while i != 0 {
    aset(x, [i, i], Nil) |> ignore
    let mut j = m
    while j != n {
      j = j + 1
      if equal(a, Fix(1L)) {
        aset(x, [i, j], cons(aref(x, [i, j]), Fix(1L))) |> ignore
        continue
      }
      // (ignore-rat-err (pquotient (aref x i j) a))
      let mut error_p = true
      let mut result : Value = Nil
      catch_tag(q_rat_err, () => {
        result = pquotient(aref(x, [i, j]), a)
        error_p = false
        Nil
      })
      |> ignore
      let d : Value = if error_p { Nil } else { result }
      let d = if d.truthy() {
        cons(d, Fix(1L))
      } else {
        ratreduce(aref(x, [i, j]), a)
      }
      aset(x, [i, j], d) |> ignore
    }
    i = i - 1
  }
  Nil
}

///|
fn diaglize1(x : Value, m : Value, n : Value) -> Value raise {
  let x = get_array_pointer(x)
  if symval(q_ear_det).truthy() {
    return ptimes(symval(q_ear_det), mat__aref2(x, m, m))
  }
  set(q_ear_det, cons(mat__aref2(x, m, m), Fix(1L))) |> ignore
  if !symval(q_d_detout).truthy() {
    ritediv(x, m, n, mat__aref2(x, m, m))
  } else {
    ritediv(x, m, n, Fix(1L))
  }
}

///|
/// Takes an M by N matrix and creates an array containing the elements of
/// the matrix. The array is put in the value cell of the symbol NAME.
fn mtoa(name : Value, m : Value, n : Value, mat : Value) -> Value raise {
  let m = to_int(m)
  let n = to_int(n)
  set(name, make_array([m + 1, n + 1], initial=Fix(0L))) |> ignore
  let name = get_array_pointer(name)
  let mut mat = mat
  for i in 1..=m {
    let mut row = car(mat)
    for j in 1..=n {
      aset(name, [i, j], car(row)) |> ignore
      row = cdr(row)
    }
    mat = cdr(mat)
  }
  Nil
}

///|
fn d_echelon(x : Value) -> Value raise {
  let mut x = x
  with_special(q_d_ratmx, t, () => {
    x = check(x)
    newvarmat1(x)
  })
  |> ignore
  with_specials(
    [(q_ear_ech, t), (q_d_algebraic, symval(q_d_algebraic))],
    () => {
      if !symval(q_d_algebraic).truthy() &&
        some(v => algp(v).truthy(), symval(q_varlist)) {
        set(q_d_algebraic, t) |> ignore
      }
      x = cons(
        list1(q_d_matrix),
        mxc(disreplist1(echelon1(replist1(mcx(cdr(x)))))),
      )
      x
    },
  )
  |> ignore
  if symval(q_d_ratmx).truthy() {
    x
  } else {
    d_totaldisrep(x)
  }
}

///|
fn echelon1(x : Value) -> Value raise {
  let m = int(length(x))
  let n = int(length(car(x)))
  mtoa(q_ear_mat, m, n, x) |> ignore
  let x = catch_tag(q_rank, () => tfgeli(q_ear_mat, m, n))
  if symval(q_ear_rank).truthy() && x.truthy() {
    throw_tag(q_rnk, x)
  } else {
    echelon2(q_ear_mat, m, n)
  }
}

///|
fn echelon2(name : Value, m : Value, n : Value) -> Value raise {
  let name = symbol_value(name)
  let n = to_int(n)
  let mut row : Value = Nil
  let mut mat : Value = Nil
  let mut m = to_int(m) + 1
  while m != 1 {
    m = m - 1
    let mut j = 0
    let mut a : Value = Nil
    while j != n {
      j = j + 1
      let e = if m > j || equal(aref(name, [m, j]), Fix(0L)) {
        cons(Fix(0L), Fix(1L))
      } else if a.truthy() {
        ratreduce(aref(name, [m, j]), a)
      } else {
        a = aref(name, [m, j])
        cons(Fix(1L), Fix(1L))
      }
      row = nconc(row, list1(e))
    }
    mat = cons(row, mat)
    row = Nil
  }
  mat
}

///|
fn triang(x : Value) -> Value raise {
  let m = int(length(x))
  let n = int(length(car(x)))
  with_special(q_ear_tri, t, () => {
    mtoa(q_ear_mat, m, n, x) |> ignore
    tfgeli(q_ear_mat, m, n) |> ignore
    triang2(q_ear_mat, m, n)
  })
}

///|
fn triang2(nam : Value, m : Value, n : Value) -> Value raise {
  let nam = get_array_pointer(nam)
  let n = to_int(n)
  let mut row : Value = Nil
  let mut mat : Value = Nil
  aset(nam, [0, 0], Fix(1L)) |> ignore
  let mut m = to_int(m) + 1
  while m != 1 {
    m = m - 1
    let mut j = 0
    while j != n {
      j = j + 1
      row = nconc(
        row,
        list1(
          if m > j {
            cons(Fix(0L), Fix(1L))
          } else {
            cons(aref(nam, [m, j]), Fix(1L))
          },
        ),
      )
    }
    mat = cons(row, mat)
    row = Nil
  }
  mat
}

///|
fn onen(n : Value, i : Value, var_ : Value, fill : Value) -> Value raise {
  let mut g : Value = Nil
  let mut i = i
  while true {
    if num_eq(i, n) {
      g = cons(var_, g)
    } else if zerop(i) {
      return g
    } else {
      g = cons(fill, g)
    }
    i = one_minus(i)
  }
  g
}

///|
fn timex0(x : Value, y : Value) -> Value raise {
  let u = check1(x)
  let v = check1(y)
  if u is Nil && v is Nil {
    list3(list1(q_mtimes), x, y)
  } else if u is Nil {
    timex1(x, cons(list1(q_d_matrix), mcx(cdr(v))))
  } else if v is Nil {
    timex1(y, cons(list1(q_d_matrix), mcx(cdr(u))))
  } else {
    cons(
      list2(q_d_matrix, q_mult),
      mxc(multiplymatrices(mcx(cdr(u)), mcx(cdr(v)))),
    )
  }
}

///|
fn timex1(x : Value, y : Value) -> Value raise {
  let mut x = x
  let mut y = check(y)
  if !symval(q_d_ratmx).truthy() {
    y = cdr(y)
  } else {
    x = cdr(ratf(x))
    y = replist1(cdr(y))
  }
  ctimesx(x, y)
}

///|
fn ctimesx(x : Value, y : Value) -> Value raise {
  let mut c : Value = Nil
  let mut y = y
  while y.truthy() {
    c = nconc(c, list1(timesrow(x, car(y))))
    y = cdr(y)
  }
  cons(
    list2(q_d_matrix, q_mult),
    mxc(if !symval(q_d_ratmx).truthy() { c } else { disreplist1(c) }),
  )
}

///|
fn multiplymatrices(x : Value, y : Value) -> Value raise {
  let mut x = x
  let mut y = y
  if cdr(y) is Nil && cdr(x) is Nil {
    if cdar(x).truthy() {
      y = transpose(y)
    }
  } else if cdar(x) is Nil && cdar(y) is Nil {
    if cdr(y).truthy() {
      x = transpose(x)
    }
  }
  if length(car(x)) != length(y) {
    if cdr(y) is Nil && length(car(x)) == length(car(y)) {
      y = transpose(y)
    } else {
      merr("MULTIPLYMATRICES: attempt to multiply nonconformable matrices.", [])
      |> ignore
    }
  }
  if !symval(q_d_ratmx).truthy() {
    multmat(x, y)
  } else {
    x = replist1(x)
    y = replist1(y)
    disreplist1(multmat(x, y))
  }
}

///|
fn multmat(x : Value, y : Value) -> Value raise {
  let mut mat : Value = Nil
  let mut row : Value = Nil
  let yt = transpose(y)
  let mut x = x
  while x.truthy() {
    let rowx = car(x)
    let mut y = yt
    while y.truthy() {
      row = nconc(row, list1(multl(rowx, car(y))))
      y = cdr(y)
    }
    mat = nconc(mat, list1(row))
    x = cdr(x)
    row = Nil
  }
  mat
}

///|
/// `((mquote simp) x)`
fn matrix__quote(x : Value) -> Value {
  list2(list2(q_mquote, q_simp), x)
}

///|
/// This actually takes the inner product of the two vectors. The most
/// common cases are checked for speed.
fn multl(a : Value, b : Value) -> Value raise {
  if equal(symval(q_d_matrix_element_add), Str("+")) {
    let mut ans : Value = if !symval(q_d_ratmx).truthy() {
      Fix(0L)
    } else {
      cons(Fix(0L), Fix(1L))
    }
    let mut a = a
    let mut b = b
    while a.truthy() {
      ans = if !symval(q_d_ratmx).truthy() {
        if equal(symval(q_d_matrix_element_mult), Str("*")) {
          add2(ans, mul2(car(a), car(b)))
        } else if equal(symval(q_d_matrix_element_mult), Str(".")) {
          add2(ans, ncmul_([car(a), car(b)]))
        } else {
          add2(
            ans,
            meval(
              list3(
                list1(getopr(symval(q_d_matrix_element_mult))),
                matrix__quote(car(a)),
                matrix__quote(car(b)),
              ),
            ),
          )
        }
      } else {
        ratplus(ans, rattimes(car(a), car(b), t))
      }
      a = cdr(a)
      b = cdr(b)
    }
    ans
  } else {
    mapply(
      getopr(symval(q_d_matrix_element_add)),
      mapcar2(
        (u, v) => meval(
          list3(
            list1(getopr(symval(q_d_matrix_element_mult))),
            matrix__quote(u),
            matrix__quote(v),
          ),
        ),
        a,
        b,
      ),
      getopr(symval(q_d_matrix_element_add)),
    )
  }
}

///|
fn bbsort(l : Value, fn_ : Value) -> Value raise {
  nreverse(sort_list(copy_list(l), (a, b) => funcall(fn_, [a, b]).truthy()))
}

///|
fn powerx(mat : Value, x : Value) -> Value raise {
  let mut mat = mat
  let mut x = x
  if !fixnump(x) {
    return list3(list2(q_mncexpt, q_simp), mat, x)
  } else if num_eq(x, Fix(1L)) {
    return mat
  } else if minusp(x) {
    x = num_neg(x)
    mat = with_special(q_d_scalarmatrixp, Nil, () => d_invert(list1(mat)))
    if symval(q_d_detout).truthy() {
      let m = mat
      let xx = x
      return with_special(q_ear_inv, q_d_detout, () => mul2_star(
        power_star(cadr(m), xx),
        fmapl1(
          lfunc("identity", args => arg(args, 0)),
          list1(powerx(caddr(m), xx)),
        ),
      ))
    }
  }
  mat = check(mat)
  newvarmat1(mat) |> ignore
  let mut n : Value = Fix(1L)
  mat = mcx(cdr(mat))
  let mut y = mat
  while true {
    if num_eq(n, x) {
      let smp = if eq(symval(q_d_scalarmatrixp), q_d_all) {
        q_d_all
      } else {
        Nil
      }
      let yy = y
      return with_special(q_d_scalarmatrixp, smp, () => simplify(
        cons(list2(q_d_matrix, q_mult), mxc(yy)),
      ))
    }
    y = multiplymatrices(y, mat)
    n = one_plus(n)
  }
  Nil
}

///|
/// The following $ALGEBRAIC code is so that
/// RANK(MATRIX([1-SQRT(5),2],[-2,1+SQRT(5)])); will give 1.
fn d_rank(x : Value) -> Value raise {
  with_specials(
    [(q_ear_rank, t), (q_d_ratmx, t), (q_d_algebraic, symval(q_d_algebraic))],
    () => {
      let mut x = check(x)
      newvarmat1(x) |> ignore
      if !symval(q_d_algebraic).truthy() &&
        some(v => algp(v).truthy(), symval(q_varlist)) {
        set(q_d_algebraic, t) |> ignore
      }
      x = replist1(mcx(cdr(x)))
      mtoa(q_ear_mat, int(length(x)), int(length(car(x))), x) |> ignore
      tfgeli(q_ear_mat, int(length(x)), int(length(car(x))))
    },
  )
}

///|
fn replacerow(i : Value, y : Value, x : Value) -> Value raise {
  if num_eq(i, Fix(1L)) {
    cons(y, cdr(x))
  } else {
    cons(car(x), replacerow(one_minus(i), y, cdr(x)))
  }
}

///|
fn timesrow(y : Value, row : Value) -> Value raise {
  let mut y = y
  let mut row = row
  let mut ans : Value = Nil
  if symval(q_d_ratmx).truthy() && atom(y) && y.truthy() {
    y = cdr(ratf(y))
  }
  while row.truthy() {
    ans = nconc(
      ans,
      list1(
        if !symval(q_d_ratmx).truthy() {
          simptimes(list3(list1(q_mtimes), y, car(row)), Fix(1L), Nil)
        } else {
          rattimes(y, car(row), t)
        },
      ),
    )
    row = cdr(row)
  }
  ans
}

///|
fn d_triangularize(x : Value) -> Value raise {
  let mut x = x
  with_special(q_d_ratmx, t, () => {
    x = check(x)
    newvarmat1(x)
  })
  |> ignore
  with_special(q_d_algebraic, symval(q_d_algebraic), () => {
    if !symval(q_d_algebraic).truthy() &&
      some(v => algp(v).truthy(), symval(q_varlist)) {
      set(q_d_algebraic, t) |> ignore
    }
    x = cons(
      list1(q_d_matrix),
      mxc(disreplist1(triang(replist1(mcx(cdr(x)))))),
    )
    x
  })
  |> ignore
  if symval(q_d_ratmx).truthy() {
    x
  } else {
    d_totaldisrep(x)
  }
}

///|
fn d_col(mat : Value, n : Value) -> Value raise {
  cons(
    list1(q_d_matrix),
    mxc(transpose(list1(nthcol(mcx(cdr(check(mat))), n)))),
  )
}

///|
fn deletecol(n : Value, x : Value) -> Value raise {
  let mut m = x
  let mut g : Value = Nil
  while m.truthy() {
    g = nconc(g, list1(deleterow(n, car(m))))
    m = cdr(m)
  }
  g
}

///|
fn deleterow(i : Value, m : Value) -> Value raise {
  if m is Nil || num_lt(i, Fix(0L)) {
    merr("DELETEROW: matrix is null, or index is negative.", [])
  } else if num_eq(i, Fix(1L)) {
    cdr(m)
  } else {
    cons(car(m), deleterow(one_minus(i), cdr(m)))
  }
}

///|
fn d_minor(mat : Value, m : Value, n : Value) -> Value raise {
  cons(list1(q_d_matrix), mxc(minor(m, n, mcx(cdr(check(mat))))))
}

///|
fn minor(i : Value, j : Value, m : Value) -> Value raise {
  deletecol(j, deleterow(i, m))
}

///|
fn d_row(mat : Value, m : Value) -> Value raise {
  cons(list1(q_d_matrix), mxc(list1(ith(mcx(cdr(check(mat))), m))))
}

///|
fn d_setelmx(elm : Value, m : Value, n : Value, mat : Value) -> Value raise {
  if !(integerp(m) && integerp(n)) {
    merr("setelmx: indices must be integers; found: ~M, ~M", [m, n]) |> ignore
  } else if !d_matrixp(mat).truthy() {
    merr("setelmx: last argument must be a matrix; found: ~M", [mat]) |> ignore
  } else if !(
      num_gt(m, Fix(0L)) &&
      num_gt(n, Fix(0L)) &&
      num_gt(int(length(mat)), m) &&
      num_gt(int(length(cadr(mat))), n)
    ) {
    merr("setelmx: no such element [~M, ~M]", [m, n]) |> ignore
  }
  rplaca(nthcdr(to_int(n), car(nthcdr(to_int(m), mat))), elm) |> ignore
  mat
}

///|
/// Here the function transpose can actually do simplification of its
/// argument. TRANSPOSE(TRANSPOSE(FOO)) => FOO.
fn d_transpose(mat : Value) -> Value raise {
  if !mxorlistp(mat).truthy() {
    if !atom(mat) &&
      memq(mop(mat), list2(q_d_transpose, q_p_transpose)).truthy() {
      cadr(mat)
    } else if d_scalarp(mat).truthy() {
      mat
    } else if mplusp(mat).truthy() {
      cons(list1(q_mplus), mapcar(x => d_transpose(x), cdr(mat)))
    } else if mtimesp(mat).truthy() {
      cons(list1(q_mtimes), mapcar(x => d_transpose(x), cdr(mat)))
    } else if mnctimesp(mat).truthy() {
      cons(list1(q_mnctimes), nreverse(mapcar(x => d_transpose(x), cdr(mat))))
    } else if mncexptp(mat).truthy() {
      let m = cadr(mat)
      let pow = caddr(mat)
      list3(list1(q_mncexpt), d_transpose(m), pow)
    } else {
      d_nounify(q_d_transpose) |> ignore
      list2(list1(q_p_transpose), mat)
    }
  } else {
    let mut ans = transpose(mcx(cdr(check(mat))))
    if symval(q_d_matrix_element_transpose).truthy() {
      ans = mapcar(u => mapcar(e => transpose_els(e), u), ans)
    }
    cons(list1(q_d_matrix), mxc(ans))
  }
}

///|
/// THIS IS FOR TRANSPOSING THE ELEMENTS OF A MATRIX
/// A hack for Block matrices and tensors.
fn transpose_els(elem : Value) -> Value raise {
  let met = symval(q_d_matrix_element_transpose)
  if eq(met, q_d_transpose) {
    d_transpose(elem)
  } else if eq(met, q_d_nonscalars) {
    if d_nonscalarp(elem).truthy() {
      d_transpose(elem)
    } else {
      elem
    }
  } else {
    meval(list2(list1(getopr(met)), matrix__quote(elem)))
  }
}

///|
fn d_submatrix(x : Value) -> Value raise {
  let mut x = x
  let mut r : Value = Nil
  while numberp(car(x)) {
    r = cons(car(x), r)
    x = cdr(x)
  }
  let gt = lfunc(">", args => lbool(num_gt(arg(args, 0), arg(args, 1))))
  let mut c = nreverse(bbsort(cdr(x), gt))
  r = nreverse(bbsort(r, gt))
  x = mcx(cdar(x))
  while r.truthy() {
    x = deleterow(car(r), x)
    r = cdr(r)
  }
  while c.truthy() {
    x = deletecol(car(c), x)
    c = cdr(c)
  }
  cons(list1(q_d_matrix), mxc(x))
}

///|
fn d_list_matrix_entries(m : Value) -> Value raise {
  if !d_matrixp(m).truthy() {
    merr("list_matrix_entries: argument must be a matrix; found: ~M", [m])
    |> ignore
  }
  let entries = Collector::new()
  for row in cdr(m).iter() {
    entries.append_list(copy_list(cdr(row)))
  }
  cons(
    if cdr(m) is Nil {
      list1(q_mlist)
    } else {
      caadr(m)
    },
    entries.result(),
  )
}
