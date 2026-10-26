// Port of share/linearalgebra/lu.lisp: LU factorization over a ring.

///|
fn share_lu__i(x : Value) -> Int raise {
  to_int(x)
}

///|
/// Return the i,j entry of the Maxima matrix m. The rows of m have been
/// permuted according to the Maxima list p.
fn m_elem(m : Value, p : Value, i : Value, j : Value) -> Value raise {
  if arrayp(m) {
    aref(m, [share_lu__i(aref1(p, share_lu__i(i))), share_lu__i(j)])
  } else {
    nth(share_lu__i(j), nth(share_lu__i(nth(share_lu__i(i), p)), m))
  }
}

///|
/// Set the i j entry of the Maxima matrix or an array to x.
fn setmatelem(m : Value, x : Value, i : Value, j : Value) -> Value raise {
  if arrayp(m) {
    aset(m, [share_lu__i(i), share_lu__i(j)], x)
  } else {
    rplaca(nthcdr(share_lu__i(j), nth(share_lu__i(i), m)), x) |> ignore
    x
  }
}

///|
/// Return m[perm[i], k] - sum(m[perm[i],s] * m[perm[s],k],s,0,n)
fn partial_matrix_prod(
  m : Value,
  p : Value,
  i : Value,
  k : Value,
  n : Value,
  fadd : Value,
  fsub : Value,
  fmult : Value,
  add_id : Value,
  fname : Value,
) -> Value raise {
  if eq(fname, q_d_floatfield) {
    partial_matrix_prod_float(m, p, i, k, n)
  } else if eq(fname, q_d_complexfield) {
    partial_matrix_prod_complex_float(m, p, i, k, n)
  } else {
    let mut add_id = add_id
    let l = share_lu__i(aref1(p, share_lu__i(i)))
    let kk = share_lu__i(k)
    for s in 0..=share_lu__i(n) {
      add_id = funcall(fadd, [
        add_id,
        funcall(fmult, [
          aref(m, [l, s]),
          aref(m, [share_lu__i(aref1(p, s)), kk]),
        ]),
      ])
    }
    aset(m, [l, kk], funcall(fsub, [aref(m, [l, kk]), add_id]))
  }
}

///|
fn partial_matrix_prod_float(
  m : Value,
  p : Value,
  i : Value,
  k : Value,
  n : Value,
) -> Value raise {
  let mut add_id : Value = Flo(0.0)
  let l = share_lu__i(aref1(p, share_lu__i(i)))
  let kk = share_lu__i(k)
  for s in 0..=share_lu__i(n) {
    add_id = num_add(
      add_id,
      num_mul(aref(m, [l, s]), aref(m, [share_lu__i(aref1(p, s)), kk])),
    )
  }
  aset(m, [l, kk], num_sub(aref(m, [l, kk]), add_id))
}

///|
fn partial_matrix_prod_complex_float(
  m : Value,
  p : Value,
  i : Value,
  k : Value,
  n : Value,
) -> Value raise {
  partial_matrix_prod_float(m, p, i, k, n)
}

///|
/// Return the infinity norm (the largest row sum) of the array mat. The
/// function fn coerces matrix elements into flonum floats.
fn array_infinity_norm(mat : Value, fn_ : Value) -> Value raise {
  reduce(
    (a, b) => num_max(a, b),
    mapcar(
      s => reduce((a, b) => num_add(a, b), s, initial=Fix(0L)),
      array_to_row_list(
        mat,
        fn_=lfunc("abs-fn", args => num_abs(funcall(fn_, [args[0]]))),
      ),
    ),
  )
}

///|
fn d_lu_factor(mat : Value, fld? : Value = q_d_generalring) -> Value raise {
  d_require_nonempty_matrix(mat, q_d_first, q_d_lu_factor) |> ignore
  d_require_square_matrix(mat, q_d_first, q_d_lu_factor) |> ignore
  let fld = d_require_ring(fld, q_d_second, q_d_lu_factor)
  let mut c = share_lu__i(d_length(mat))
  let perm = make_array([c])
  let mat = maxima_to_array(mat, fn_=share_mring__slot(fld, "maxima-to-mring"))
  c -= 1
  for i in 0..=c {
    aset1(perm, i, int(i)) |> ignore
  }
  // When the matrix elements can be converted to CL floats, find the
  // infinity norm of m. The norm is used to bound the condition number.
  let cnd = if share_mring__slot(fld, "coerce-to-lisp-float").truthy() {
    let fn_ = share_mring__slot(fld, "coerce-to-lisp-float")
    array_infinity_norm(mat, fn_)
  } else {
    Flo(0.0)
  }
  lu_factor(mat, perm, int(c), fld, cnd~)
}

///|
fn d_get_lu_factors(x : Value) -> Value raise {
  let mat = d_first(x)
  let p = share_lu__second(x)
  let mut perm : Value = Nil
  let mut mp : Value = Nil
  let mut r = d_matrix_size(mat)
  let c = share_lu__second(r)
  r = d_first(r)
  let mut id = d_args(d_identfor(mat))
  for i in 1..=share_lu__i(c) {
    perm = cons(nth(share_lu__i(nth(i, p)), id), perm)
    mp = cons(nth(share_lu__i(nth(i, p)), mat), mp)
  }
  perm = reverse(perm)
  mp = reverse(mp)
  perm = cons(list1(q_d_matrix), perm)
  mp = cons(list1(q_d_matrix), mp)
  let lower = copy_tree(mp)
  let upper = copy_tree(mp)
  id = d_identfor(d_first(d_first(mat)))
  let zero = d_zerofor(d_first(d_first(mat)))
  for i in 1..=share_lu__i(r) {
    for j in 1..=share_lu__i(c) {
      if i == j {
        setmatelem(lower, id, int(i), int(j)) |> ignore
      }
      if i > j {
        setmatelem(upper, zero, int(i), int(j)) |> ignore
      }
      if i < j {
        setmatelem(lower, zero, int(i), int(j)) |> ignore
      }
    }
  }
  list([list1(q_mlist), d_transpose(perm), lower, upper])
}

///|
fn lu_factor(
  m : Value,
  perm : Value,
  c : Value,
  fld : Value,
  cnd? : Value = Flo(1.0),
) -> Value raise {
  let fname = share_mring__name(fld)
  let add_id = share_mring__call(fld, "add-id", [])
  let fzerop = share_mring__slot(fld, "fzerop")
  let fabs = share_mring__slot(fld, "abs")
  let fdiv = share_mring__slot(fld, "div")
  let fgreat = share_mring__slot(fld, "great")
  let fadd = share_mring__slot(fld, "add")
  let fsub = share_mring__slot(fld, "sub")
  let fmult = share_mring__slot(fld, "mult")
  let c_ = share_lu__i(c)
  for k in 0..=c_ {
    for i in k..=c_ {
      partial_matrix_prod(
        m,
        perm,
        int(i),
        int(k),
        int(k - 1),
        fadd,
        fsub,
        fmult,
        add_id,
        fname,
      )
      |> ignore
    }
    let mut mx = funcall(fabs, [m_elem(m, perm, int(k), int(k))])
    let mut pos = k
    for s in k..=c_ {
      if funcall(fgreat, [funcall(fabs, [m_elem(m, perm, int(s), int(k))]), mx]).truthy() {
        pos = s
        mx = funcall(fabs, [m_elem(m, perm, int(s), int(k))])
      }
    }
    let save = aref1(perm, k)
    aset1(perm, k, aref1(perm, pos)) |> ignore
    aset1(perm, pos, save) |> ignore
    let kp1 = k + 1
    for i in kp1..=c_ {
      if !funcall(fzerop, [m_elem(m, perm, int(k), int(k))]).truthy() {
        setmatelem(
          m,
          funcall(fdiv, [
            m_elem(m, perm, int(i), int(k)),
            m_elem(m, perm, int(k), int(k)),
          ]),
          aref1(perm, i),
          int(k),
        )
        |> ignore
        partial_matrix_prod(
          m,
          perm,
          int(k),
          int(i),
          int(k - 1),
          fadd,
          fsub,
          fmult,
          add_id,
          fname,
        )
        |> ignore
      }
    }
  }
  let plus1 = lfunc("1+", args => num_add(args[0], Fix(1L)))
  let coerce = share_mring__slot(fld, "coerce-to-lisp-float")
  if coerce.truthy() {
    let (lb, ub) = mat_cond_by_lu(m, perm, c, coerce)
    let m = array_to_maxima_matrix(m, fn_=share_mring__slot(fld, "mring-to-maxima"))
    let lb = d_limit(list1(mul2(lb, cnd)))
    let ub = d_limit(list1(mul2(ub, cnd)))
    let perm = array_to_maxima_list(perm, fn_=plus1)
    list([list1(q_mlist), m, perm, fname, lb, ub])
  } else {
    let perm = array_to_maxima_list(perm, fn_=plus1)
    let m = array_to_maxima_matrix(m, fn_=share_mring__slot(fld, "mring-to-maxima"))
    list([list1(q_mlist), m, perm, fname])
  }
}

///|
/// The first argument should be a matrix in packed LU form. The Maxima list
/// perm specifies the true row ordering. When r is false, reflect the matrix
/// horizontally and vertically.
fn m_elem_reflect(
  mat : Value,
  perm : Value,
  n : Value,
  r : Value,
  i : Value,
  j : Value,
) -> Value raise {
  if r.truthy() && num_eq(i, j) {
    Fix(1L)
  } else if r.truthy() {
    m_elem(mat, perm, num_sub(n, i), num_sub(n, j))
  } else {
    m_elem(mat, perm, i, j)
  }
}

///|
fn mat_cond_by_lu(mat : Value, perm : Value, n : Value, fn_ : Value) -> (Value, Value) raise {
  let (lb0, ub0) = triangular_mat_cond(mat, perm, n, fn_, t)
  let (lb1, ub1) = triangular_mat_cond(mat, perm, n, fn_, Nil)
  (d_limit(list1(mul2(lb0, lb1))), d_limit(list1(mul2(ub0, ub1))))
}

///|
/// Return lower and upper bounds for the infinity norm condition number of
/// the lower or upper triangular part of the matrix mat. The function fn
/// coerces the matrix elements to flonum floats.  When the matrix is
/// singular, return infinity.  Based on algorithm 2.1 in "Survey of
/// condition number estimation," by Nicholas J. Higham, SIAM Review,
/// Vol. 29, No. 4, December, 1987.
fn triangular_mat_cond(
  mat : Value,
  perm : Value,
  n : Value,
  fn_ : Value,
  r : Value,
) -> (Value, Value) raise {
  let nn = share_lu__i(n)
  let z : Array[Value] = Array::make(nn + 1, Nil)
  let mut d_max : Value = Flo(0.0)
  let mut z_max : Value = Flo(0.0)
  let mut i = nn
  while i >= 0 {
    let mut d = num_abs(
      funcall(fn_, [m_elem_reflect(mat, perm, n, r, int(i), int(i))]),
    )
    if num_eq(Flo(0.0), d) {
      return (q_d_inf, q_d_inf)
    } else {
      d = num_div(Fix(1L), d)
    }
    d_max = num_max(d_max, num_abs(funcall(fn_, [d])))
    let mut s : Value = Flo(1.0)
    for j in (i + 1)..=nn {
      s = num_add(
        s,
        num_mul(
          num_abs(
            funcall(fn_, [m_elem_reflect(mat, perm, n, r, int(i), int(j))]),
          ),
          z[j],
        ),
      )
    }
    z[i] = num_mul(d, s)
    z_max = num_max(z_max, z[i])
    i -= 1
  }
  (d_max, z_max)
}

///|
fn d_lu_backsub(m : Value, b1 : Value) -> Value raise {
  d_require_list(m, q_d_first, q_d_lu_backsub) |> ignore
  if num_lt(d_length(m), Fix(3L)) {
    merr(
      "The first argument to 'lu_backsub' must be a list with at least 3 members",
      [],
    )
    |> ignore
  }
  let fld = get(mfuncall(q_d_ev, list1(fourth(m))), q_ring)
  let fadd = share_mring__slot(fld, "add")
  let fsub = share_mring__slot(fld, "sub")
  let fmult = share_mring__slot(fld, "mult")
  let fdiv = share_mring__slot(fld, "rdiv")
  let add_id = share_mring__call(fld, "add-id", [])
  let mut mat = copy_tree(d_first(m))
  let perm = share_lu__second(m)
  let n = d_matrix_size(mat)
  let r = share_lu__i(d_first(n))
  mat = matrix_map(share_mring__slot(fld, "maxima-to-mring"), mat)
  let mut b = copy_tree(b1)
  let c = share_lu__i(share_lu__second(d_matrix_size(mat)))
  let cc = share_lu__i(share_lu__second(d_matrix_size(b)))
  b = matrix_map(share_mring__slot(fld, "maxima-to-mring"), b)
  let bb = copy_tree(b)
  for i in 1..=r {
    for j in 1..=cc {
      setmatelem(bb, m_elem(b, perm, int(i), int(j)), int(i), int(j)) |> ignore
    }
  }
  let id_perm = mfuncall(q_d_makelist, list([q_i, q_i, Fix(1L), int(r)]))
  for q in 1..=cc {
    for i in 2..=c {
      let mut acc = add_id
      for j in 1..=(i - 1) {
        acc = funcall(fadd, [
          acc,
          funcall(fmult, [
            m_elem(mat, perm, int(i), int(j)),
            m_elem(bb, id_perm, int(j), int(q)),
          ]),
        ])
      }
      setmatelem(
        bb,
        funcall(fsub, [m_elem(bb, id_perm, int(i), int(q)), acc]),
        int(i),
        int(q),
      )
      |> ignore
    }
  }
  for q in 1..=cc {
    let mut i = r
    while i >= 1 {
      let mut acc = m_elem(bb, id_perm, int(i), int(q))
      for j in (i + 1)..=c {
        acc = funcall(fsub, [
          acc,
          funcall(fmult, [
            m_elem(mat, perm, int(i), int(j)),
            m_elem(bb, id_perm, int(j), int(q)),
          ]),
        ])
      }
      if eq(
          t,
          meqp(
            share_mring__call(fld, "mring-to-maxima", [
              m_elem(mat, perm, int(i), int(i)),
            ]),
            Fix(0L),
          ),
        ) {
        merr("lu_backsub: matrix is singular.", []) |> ignore
      }
      setmatelem(
        bb,
        funcall(fdiv, [acc, m_elem(mat, perm, int(i), int(i))]),
        int(i),
        int(q),
      )
      |> ignore
      i -= 1
    }
  }
  matrix_map(share_mring__slot(fld, "mring-to-maxima"), bb)
}

///|
fn d_invert_by_lu(m : Value, fld? : Value = q_d_generalring) -> Value raise {
  d_require_square_matrix(m, q_d_first, q_d_invert_by_lu) |> ignore
  d_lu_backsub(d_lu_factor(m, fld~), d_identfor(m))
}

///|
/// Return a Lisp list of two elements, the determinant, and the inverse of M.
fn invert_by_lu_with_determinant(m : Value, fld_name : Value) -> Value raise {
  let i = d_identfor(m)
  let m1 = d_lu_factor(m, fld=fld_name)
  let fld = get(fld_name, q_ring)
  let d = determinant_by_lu_factors(m1, fld)
  list2(d, d_lu_backsub(m1, i))
}

///|
fn d_determinant_by_lu(m : Value, fld_name? : Value = q_d_generalring) -> Value raise {
  d_require_square_matrix(m, q_d_first, q_d_determinant_by_lu) |> ignore
  let fld = d_require_ring(fld_name, q_d_second, q_d_determinant_by_lu)
  let m = d_lu_factor(m, fld=fld_name)
  determinant_by_lu_factors(m, fld)
}

///|
/// Assume that M has already been factored by $LU_FACTOR and FLD is some
/// field (not a field name).
fn determinant_by_lu_factors(m : Value, fld : Value) -> Value raise {
  let mut acc = share_mring__call(fld, "mult-id", [])
  let fmult = share_mring__slot(fld, "mult")
  let fconvert = share_mring__slot(fld, "maxima-to-mring")
  let n = share_lu__i(d_first(d_matrix_size(d_first(m))))
  let perm = share_lu__second(m)
  let m = d_first(m)
  for i in 1..=n {
    let d = funcall(fconvert, [m_elem(m, perm, int(i), int(i))])
    acc = funcall(fmult, [acc, d])
  }
  let (_, perm_sign) = bbsort1(cdr(perm))
  share_mring__call(fld, "mring-to-maxima", [
    if perm_sign.truthy() {
      share_mring__call(fld, "negate", [acc])
    } else {
      acc
    },
  ])
}

///|
fn d_mat_cond(m : Value, p : Value) -> Value raise {
  d_require_square_matrix(m, q_d_first, q_d_mat_cond) |> ignore
  mul2(
    mfuncall(q_d_mat_norm, list2(m, p)),
    mfuncall(q_d_mat_norm, list2(d_invert_by_lu(m), p)),
  )
}

///|
fn d_linsolve_by_lu(m : Value, b : Value, fld? : Value = q_d_generalring) -> Value raise {
  d_require_square_matrix(m, q_d_first, q_d_linsolve_by_lu) |> ignore
  let b = if d_listp(b).truthy() { d_transpose(b) } else { b }
  d_require_matrix(b, q_d_second, q_d_linsolve_by_lu) |> ignore
  d_require_ring(fld, q_d_third, q_d_linsolve_by_lu) |> ignore
  if !num_eq(share_lu__second(d_matrix_size(m)), d_first(d_matrix_size(b))) {
    merr("Incompatible matrix sizes", []) |> ignore
  }
  let m = d_lu_factor(m, fld~)
  list([
    list1(q_mlist),
    d_lu_backsub(m, b),
    if floatp(d_last(m)) {
      d_last(m)
    } else {
      Nil
    },
  ])
}

///|
fn invertible_matrixp(mat : Value, fld : Value) -> Value raise {
  let mut ok = true
  if d_matrixp(mat).truthy() {
    let n = d_matrix_size(mat)
    if !eql(d_first(n), share_lu__second(n)) {
      // nonsquare matrices aren't invertible
      Nil
    } else {
      let mat = fourth(d_get_lu_factors(d_lu_factor(mat, fld~)))
      let mut n = share_lu__i(d_first(n))
      while ok && n > 0 {
        ok = ok && !d_zeromatrixp(d_inpart(list3(mat, int(n), int(n)))).truthy()
        n -= 1
      }
      lbool(ok)
    }
  } else {
    lbool(!d_zeromatrixp(mat).truthy())
  }
}

///|
fn init_share_lu() -> Unit raise {
  d_put(q_d_lu, Fix(3L), q_d_version) |> ignore
}

///|
/// Maxima's `$second` (defined in comm.lisp by a macro, without a
/// declaration).
fn share_lu__second(x : Value) -> Value raise {
  funcall(q_d_second, [x])
}

///|
/// Maxima's `$third`.
fn share_lu__third(x : Value) -> Value raise {
  funcall(q_d_third, [x])
}
