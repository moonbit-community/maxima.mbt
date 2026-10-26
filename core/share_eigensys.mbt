// Port of share/lapack/eigensys.lisp: the Maxima interface to LAPACK's
// DGEEV, DGESVD, DLANGE, ZLANGE, ZGEEV and ZHEEV (translated by f2cl; the
// MoonBit translation is the package dii/maxima/lapack).
//
// The "Lisp matrices" are Lisp vectors (column-major) of flonums or of
// (complex flonum)s, as in the Lisp; they are copied to and from the
// FixedArrays the LAPACK routines work on around each call.  Passing a
// real matrix where a routine declares a complex array (or the other way
// round) is a TYPE-ERROR in the Lisp, and here.

///|
fn share_lapack__type_error(v : Value, what : String) -> Value raise {
  raise LispError::SimpleError(
    "The value " + prin1_to_string(v) + " is not of type " + what,
  )
}

///|
/// A Lisp vector of flonums as a FixedArray.
fn share_lapack__dvec(v : Value) -> FixedArray[Double] raise {
  let n = length(v)
  let a : FixedArray[Double] = FixedArray::make(n, 0.0)
  for i in 0..<n {
    match aref1(v, i) {
      Flo(d) => a[i] = d
      x => {
        share_lapack__type_error(x, "DOUBLE-FLOAT") |> ignore
        ()
      }
    }
  }
  a
}

///|
/// A Lisp vector of (complex flonum)s as a FixedArray.
fn share_lapack__zvec(v : Value) -> FixedArray[@f2cl.Complex] raise {
  let n = length(v)
  let a : FixedArray[@f2cl.Complex] = FixedArray::make(n, @f2cl.c_zero)
  for i in 0..<n {
    match aref1(v, i) {
      Cplx(Flo(re), Flo(im)) => a[i] = @f2cl.cplx(re, im)
      x => {
        share_lapack__type_error(x, "(COMPLEX DOUBLE-FLOAT)") |> ignore
        ()
      }
    }
  }
  a
}

///|
fn share_lapack__set_dvec(v : Value, a : FixedArray[Double]) -> Unit raise {
  for i in 0..<a.length() {
    aset1(v, i, Flo(a[i])) |> ignore
  }
}

///|
fn share_lapack__set_zvec(v : Value, a : FixedArray[@f2cl.Complex]) -> Unit raise {
  for i in 0..<a.length() {
    aset1(v, i, Cplx(Flo(a[i].re), Flo(a[i].im))) |> ignore
  }
}

///|
fn share_lapack__flonum_array(n : Int) -> Value {
  make_array([n], initial=Flo(0.0))
}

///|
fn share_lapack__complex_array(n : Int) -> Value {
  make_array([n], initial=Cplx(Flo(0.0), Flo(0.0)))
}

///|
fn maxima_matrix_dims(a : Value) -> (Value, Value) raise {
  let row = second(a)
  // Should we check that all rows have the same length?
  (int(length(cdr(a))), int(length(cdr(row))))
}

///|
fn complex_maxima_matrix_p(a : Value) -> Value raise {
  for row in cdr(a).iter() {
    for col in cdr(row).iter() {
      if !eql(d_imagpart(col), Fix(0L)) {
        return t
      }
    }
  }
  Nil
}

///|
/// Convert a Maxima matrix A of dimension NROW and NCOL to a Lisp matrix
/// suitable for use with LAPACK.
fn lapack_lispify_matrix(
  a : Value,
  nrow : Value,
  ncol : Value,
  assume_complex_maxima_matrix_p? : Value = Nil,
) -> Value raise {
  let a = d_float(a)
  let cplx = assume_complex_maxima_matrix_p.truthy() ||
    complex_maxima_matrix_p(a).truthy()
  let nr = to_int(nrow)
  let n = nr * to_int(ncol)
  let mat = if cplx {
    share_lapack__complex_array(n)
  } else {
    share_lapack__flonum_array(n)
  }
  let mut r = 0
  for row in cdr(a).iter() {
    let mut c = 0
    for col in cdr(row).iter() {
      // Fortran matrices are in column-major order!
      let v : Value = if cplx {
        let re = d_realpart(col)
        let im = d_imagpart(col)
        Cplx(Flo(to_double(re)), Flo(to_double(im)))
      } else {
        match col {
          Flo(_) => col
          Fix(_) | Big(_) | Ratio(_, _) => Flo(to_double(col))
          _ => share_lapack__type_error(col, "DOUBLE-FLOAT")
        }
      }
      aset1(mat, c * nr + r, v) |> ignore
      c = c + 1
    }
    r = r + 1
  }
  mat
}

///|
/// Convert an LAPACK matrix of dimensions NROW and NCOL into a Maxima matrix
/// (list of lists).
fn lapack_maxify_matrix(nrow : Value, ncol : Value, a : Value) -> Value raise {
  let nr = to_int(nrow)
  let nc = to_int(ncol)
  let res = Collector::new()
  for r in 0..<nr {
    let row = Collector::new()
    for c in 0..<nc {
      // Fortran arrays are column-major order!
      let v = aref1(a, c * nr + r)
      row.add(add2(realpart(v), mul2(q_d__pcti, imagpart(v))))
    }
    res.add(cons(list1(q_mlist), row.result()))
  }
  cons(list1(q_d_matrix), res.result())
}

///|
/// DGEEV computes for an N-by-N real nonsymmetric matrix A, the eigenvalues
/// and, optionally, the left and/or right eigenvectors.  The result is
/// [eigenvalues, right eigenvectors or false, left eigenvectors or false].
fn d_dgeev(
  a : Value,
  right_vec_p? : Value = Nil,
  left_vec_p? : Value = Nil,
) -> Value raise {
  let make_eigval = (wr : FixedArray[Double], wi : FixedArray[Double]) => {
    let c = Collector::new()
    for k in 0..<wr.length() {
      c.add(add2(Flo(wr[k]), mul2(q_d__pcti, Flo(wi[k]))))
    }
    cons(list1(q_mlist), c.result())
  }
  // dgeev stores the eigen vectors in a special way.  Undo that.
  let make_eigvec = (n : Int, vr : FixedArray[Double], wi : FixedArray[Double]) => {
    let evec : Array[Value] = Array::make(n * n, Nil)
    let mut col = 0
    let mut posn = 0
    while col < n {
      if wi[col] == 0.0 {
        for row in 0..<n {
          evec[row * n + col] = Flo(vr[posn])
          posn = posn + 1
        }
      } else {
        for row in 0..<n {
          let next_posn = posn + n
          let val_plus = add2(Flo(vr[posn]), mul2(q_d__pcti, Flo(vr[next_posn])))
          let val_minus = sub(Flo(vr[posn]), mul2(q_d__pcti, Flo(vr[next_posn])))
          evec[row * n + col] = val_plus
          evec[row * n + col + 1] = val_minus
          posn = posn + 1
        }
        // Skip over the next column, which we've already used
        col = col + 1
        posn = posn + n
      }
      col = col + 1
    }
    // Now convert this 2-D Lisp matrix into a maxima matrix
    let res = Collector::new()
    for r in 0..<n {
      let row = Collector::new()
      for c in 0..<n {
        row.add(evec[r * n + c])
      }
      res.add(cons(list1(q_mlist), row.result()))
    }
    cons(list1(q_d_matrix), res.result())
  }
  let n = to_int(maxima_matrix_dims(a).0)
  let a_mat = lapack_lispify_matrix(a, int(n), int(n))
  let am = share_lapack__dvec(a_mat)
  let wr : FixedArray[Double] = FixedArray::make(n, 0.0)
  let wi : FixedArray[Double] = FixedArray::make(n, 0.0)
  let vl : FixedArray[Double] = FixedArray::make(
    if left_vec_p.truthy() { n * n } else { 0 },
    0.0,
  )
  let vr : FixedArray[Double] = FixedArray::make(
    if right_vec_p.truthy() { n * n } else { 0 },
    0.0,
  )
  let jobvl = if left_vec_p.truthy() { "V" } else { "N" }
  let jobvr = if right_vec_p.truthy() { "V" } else { "N" }
  // Figure out how much space we need in the work array.
  @lapack.dgeev(jobvl, jobvr, n, am, n, wr, wi, vl, n, vr, n, wr, -1, 0)
  |> ignore
  let opt_lwork = wr[0].to_int()
  let work : FixedArray[Double] = FixedArray::make(opt_lwork, 0.0)
  // Now do the work with the optimum size of the work space.
  let info = @lapack.dgeev(
    jobvl, jobvr, n, am, n, wr, wi, vl, n, vr, n, work, opt_lwork, 0,
  )
  share_lapack__set_dvec(a_mat, am)
  if info < 0 {
    merr("DGEEV: invalid arguments: ~D", [int(info)]) |> ignore
  } else if info > 0 {
    merr("DGEEV: failed to converge: ~D", [int(info)]) |> ignore
  }
  let e_val = make_eigval(wr, wi)
  let e_vec_right = if right_vec_p.truthy() {
    make_eigvec(n, vr, wi)
  } else {
    Nil
  }
  let e_vec_left = if left_vec_p.truthy() { make_eigvec(n, vl, wi) } else { Nil }
  list([list1(q_mlist), e_val, e_vec_right, e_vec_left])
}

///|
/// DGESVD computes the singular value decomposition (SVD) of a real M-by-N
/// matrix A = U * SIGMA * transpose(V).  The result is [singular values,
/// U or false, V^T or false] depending on jobu and jobvt.
fn d_dgesvd(a : Value, jobu? : Value = Nil, jobvt? : Value = Nil) -> Value raise {
  let fixup_jobu = (arg : Value) => if arg.truthy() {
    "All columns of U"
  } else {
    "No columns of U"
  }
  let fixup_jobvt = (arg : Value) => if arg.truthy() {
    "All columns of V^T"
  } else {
    "No columns of V^T"
  }
  let (nrow_v, ncol_v) = maxima_matrix_dims(a)
  let nrow = to_int(nrow_v)
  let ncol = to_int(ncol_v)
  let a_mat = lapack_lispify_matrix(a, nrow_v, ncol_v)
  let am = share_lapack__dvec(a_mat)
  let s : FixedArray[Double] = FixedArray::make(
    if nrow < ncol { nrow } else { ncol },
    0.0,
  )
  let u : FixedArray[Double] = FixedArray::make(nrow * nrow, 0.0)
  let vt : FixedArray[Double] = FixedArray::make(ncol * ncol, 0.0)
  let wr : FixedArray[Double] = FixedArray::make(1, 0.0)
  // Figure out the optimum size for the work array
  @lapack.dgesvd(
    fixup_jobu(jobu),
    fixup_jobvt(jobvt),
    nrow,
    ncol,
    am,
    nrow,
    s,
    u,
    nrow,
    vt,
    ncol,
    wr,
    -1,
    0,
  )
  |> ignore
  let opt_lwork = wr[0].to_int()
  let work : FixedArray[Double] = FixedArray::make(opt_lwork, 0.0)
  // Allocate the optimum work array and do the requested computation.
  let info = @lapack.dgesvd(
    fixup_jobu(jobu),
    fixup_jobvt(jobvt),
    nrow,
    ncol,
    am,
    nrow,
    s,
    u,
    nrow,
    vt,
    ncol,
    work,
    opt_lwork,
    0,
  )
  share_lapack__set_dvec(a_mat, am)
  if info < 0 {
    merr("DGESVD: invalid arguments: ~D", [int(info)]) |> ignore
  } else if info > 0 {
    merr("DGESVD: failed to converge: ~D", [int(info)]) |> ignore
  }
  let to_lisp = (x : FixedArray[Double]) => {
    let v = share_lapack__flonum_array(x.length())
    share_lapack__set_dvec(v, x)
    v
  }
  let u_max = if jobu.truthy() {
    lapack_maxify_matrix(nrow_v, nrow_v, to_lisp(u))
  } else {
    Nil
  }
  let vt_max = if jobvt.truthy() {
    lapack_maxify_matrix(ncol_v, ncol_v, to_lisp(vt))
  } else {
    Nil
  }
  let sl = Collector::new()
  for v in s {
    sl.add(Flo(v))
  }
  let s_max = cons(list1(q_mlist), sl.result())
  list([list1(q_mlist), s_max, u_max, vt_max])
}

///|
/// The LAPACK norm type for NORM ('$max, '$one_norm, '$inf_norm,
/// '$frobenius), as the Lisp's ECASE.
fn share_lapack__norm_type(norm : Value) -> String raise {
  if eq(norm, q_d_max) {
    "M"
  } else if eq(norm, q_d_one_norm) {
    "O"
  } else if eq(norm, q_d_inf_norm) {
    "I"
  } else if eq(norm, q_d_frobenius) {
    "F"
  } else {
    raise LispError::SimpleError(
      prin1_to_string(norm) +
      " fell through ECASE expression.  Wanted one of ($MAX $ONE_NORM $INF_NORM $FROBENIUS).",
    )
  }
}

///|
/// DLANGE: max(abs(A(i,j))), the one norm, the infinity norm or the
/// Frobenius norm of A.
fn d_dlange(norm : Value, a : Value) -> Value raise {
  let (nrows_v, ncols_v) = maxima_matrix_dims(a)
  let nrows = to_int(nrows_v)
  let a_mat = lapack_lispify_matrix(a, nrows_v, ncols_v)
  let norm_type = share_lapack__norm_type(norm)
  let work : FixedArray[Double] = FixedArray::make(
    if norm_type == "I" { nrows } else { 0 },
    0.0,
  )
  Flo(
    @lapack.dlange(
      norm_type,
      nrows,
      to_int(ncols_v),
      share_lapack__dvec(a_mat),
      0,
      nrows,
      work,
      0,
    ),
  )
}

///|
/// ZLANGE: the norms of DLANGE for a complex matrix.
fn d_zlange(norm : Value, a : Value) -> Value raise {
  let (nrows_v, ncols_v) = maxima_matrix_dims(a)
  let nrows = to_int(nrows_v)
  let a_mat = lapack_lispify_matrix(a, nrows_v, ncols_v)
  let norm_type = share_lapack__norm_type(norm)
  let work : FixedArray[Double] = FixedArray::make(
    if norm_type == "I" { nrows } else { 0 },
    0.0,
  )
  Flo(
    @lapack.zlange(
      norm_type,
      nrows,
      to_int(ncols_v),
      share_lapack__zvec(a_mat),
      nrows,
      work,
    ),
  )
}

///|
fn share_lapack__make_eigval(w : FixedArray[@f2cl.Complex]) -> Value raise {
  let c = Collector::new()
  for z in w {
    c.add(add2(Flo(z.re), mul2(q_d__pcti, Flo(z.im))))
  }
  cons(list1(q_mlist), c.result())
}

///|
fn share_lapack__zlisp(x : FixedArray[@f2cl.Complex]) -> Value raise {
  let v = share_lapack__complex_array(x.length())
  share_lapack__set_zvec(v, x)
  v
}

///|
/// ZGEEV computes for an N-by-N complex nonsymmetric matrix A, the
/// eigenvalues and, optionally, the left and/or right eigenvectors.
fn d_zgeev(
  a : Value,
  right_vec_p? : Value = Nil,
  left_vec_p? : Value = Nil,
) -> Value raise {
  let n = to_int(maxima_matrix_dims(a).0)
  let a_mat = lapack_lispify_matrix(a, int(n), int(n), assume_complex_maxima_matrix_p=t)
  let am = share_lapack__zvec(a_mat)
  let w : FixedArray[@f2cl.Complex] = FixedArray::make(n, @f2cl.c_zero)
  let vl : FixedArray[@f2cl.Complex] = FixedArray::make(
    if left_vec_p.truthy() { n * n } else { 0 },
    @f2cl.c_zero,
  )
  let vr : FixedArray[@f2cl.Complex] = FixedArray::make(
    if right_vec_p.truthy() { n * n } else { 0 },
    @f2cl.c_zero,
  )
  let rwork0 : FixedArray[Double] = FixedArray::make(1, 0.0)
  let jobvl = if left_vec_p.truthy() { "V" } else { "N" }
  let jobvr = if right_vec_p.truthy() { "V" } else { "N" }
  // Figure out how much space we need in the work array.
  @lapack.zgeev(jobvl, jobvr, n, am, n, w, vl, n, vr, n, w, -1, rwork0, 0)
  |> ignore
  let opt_lwork = w[0].re.to_int()
  let work : FixedArray[@f2cl.Complex] = FixedArray::make(opt_lwork, @f2cl.c_zero)
  let rwork : FixedArray[Double] = FixedArray::make(opt_lwork, 0.0)
  // Now do the work with the optimum size of the work space.
  let info = @lapack.zgeev(
    jobvl, jobvr, n, am, n, w, vl, n, vr, n, work, opt_lwork, rwork, 0,
  )
  share_lapack__set_zvec(a_mat, am)
  if info < 0 {
    merr("ZGEEV: invalid arguments: ~D", [int(info)]) |> ignore
  } else if info > 0 {
    merr("ZGEEV: failed to converge: ~D", [int(info)]) |> ignore
  }
  let e_val = share_lapack__make_eigval(w)
  let e_vec_right = if right_vec_p.truthy() {
    lapack_maxify_matrix(int(n), int(n), share_lapack__zlisp(vr))
  } else {
    Nil
  }
  let e_vec_left = if left_vec_p.truthy() {
    lapack_maxify_matrix(int(n), int(n), share_lapack__zlisp(vl))
  } else {
    Nil
  }
  list([list1(q_mlist), e_val, e_vec_right, e_vec_left])
}

///|
/// ZHEEV computes the eigenvalues and, optionally, the eigenvectors of a
/// complex Hermitian matrix.  The result is [eigenvalues, eigenvectors or
/// false].
fn d_zheev(a : Value, eigen_vector_p? : Value = Nil) -> Value raise {
  let n = to_int(maxima_matrix_dims(a).0)
  let a_mat = lapack_lispify_matrix(a, int(n), int(n), assume_complex_maxima_matrix_p=t)
  let am = share_lapack__zvec(a_mat)
  let w : FixedArray[Double] = FixedArray::make(n, 0.0)
  let work0 : FixedArray[@f2cl.Complex] = FixedArray::make(1, @f2cl.c_zero)
  let rwork : FixedArray[Double] = FixedArray::make(
    if 3 * n - 2 > 1 { 3 * n - 2 } else { 1 },
    0.0,
  )
  let jobz = if eigen_vector_p.truthy() { "V" } else { "N" }
  // Figure out how much space we need in the work array.
  @lapack.zheev(jobz, "U", n, am, n, w, work0, -1, rwork, 0) |> ignore
  let opt_lwork = work0[0].re.to_int()
  let work : FixedArray[@f2cl.Complex] = FixedArray::make(opt_lwork, @f2cl.c_zero)
  // Now do the work with the optimum size of the work space.
  let (_, info) = @lapack.zheev(jobz, "U", n, am, n, w, work, opt_lwork, rwork, 0)
  share_lapack__set_zvec(a_mat, am)
  if info < 0 {
    merr("ZHEEV: invalid arguments: ~D", [int(info)]) |> ignore
  } else if info > 0 {
    merr("ZHEEV: failed to converge: ~D", [int(info)]) |> ignore
  }
  let c = Collector::new()
  for v in w {
    // (add (realpart z) (mul '$%i (imagpart z))) on a flonum
    c.add(add2(Flo(v), mul2(q_d__pcti, imagpart(Flo(v)))))
  }
  let e_val = cons(list1(q_mlist), c.result())
  let e_vec = if eigen_vector_p.truthy() {
    lapack_maxify_matrix(int(n), int(n), a_mat)
  } else {
    Nil
  }
  list([list1(q_mlist), e_val, e_vec])
}

///|
fn init_share_eigensys() -> Unit raise {
  share_f2cl__install_output()
}
