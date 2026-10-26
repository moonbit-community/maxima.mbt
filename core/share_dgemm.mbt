// Port of share/lapack/dgemm.lisp: simple raw interface to LAPACK dgemm,
// general real matrix multiplication.

///|
/// dgemm(a, b, c = C, transpose_a = .., transpose_b = .., alpha = .., beta
/// = ..) computes alpha * op(a) . op(b) + beta * C.
///
/// The Lisp's supplied-p flags of C and BETA are not available in the
/// generated keyword-argument interface: C counts as supplied when it is
/// not false, BETA when it is not the default 0.0.
fn d_dgemm(
  a : Value,
  b : Value,
  c? : Value = Nil,
  transpose_a? : Value = Nil,
  transpose_b? : Value = Nil,
  alpha? : Value = Flo(1.0),
  beta? : Value = Flo(0.0),
) -> Value raise {
  let cp = c.truthy()
  let betap = !(beta is Flo(0.0))
  let mut beta = beta
  let maybe_transpose_dims = (transp : Value, row : Int, col : Int) => if transp.truthy() {
    (col, row)
  } else {
    (row, col)
  }
  let (a_nrows_v, a_ncols_v) = maxima_matrix_dims(a)
  let a_nrows = to_int(a_nrows_v)
  let a_ncols = to_int(a_ncols_v)
  let (at_nrows, at_ncols) = maybe_transpose_dims(transpose_a, a_nrows, a_ncols)
  let (b_nrows_v, b_ncols_v) = maxima_matrix_dims(b)
  let b_nrows = to_int(b_nrows_v)
  let b_ncols = to_int(b_ncols_v)
  let (bt_nrows, bt_ncols) = maybe_transpose_dims(transpose_b, b_nrows, b_ncols)
  // Compute the dimensions of C.  If C is not given, we need to create a
  // space of the correct dimension to hold the result.
  let (c_nrows, c_ncols) = if c.truthy() {
    let (r, cc) = maxima_matrix_dims(c)
    (to_int(r), to_int(cc))
  } else {
    (at_nrows, bt_ncols)
  }
  // Do something nice if C is given but beta is not.  We take this to mean
  // that we just want to add C, implying that beta = 1.
  if cp && !betap {
    beta = Flo(0.0)
  }
  // Now for some error checking.
  if at_ncols != bt_nrows {
    merr("Cannot multiply a ~m by ~m matrix by a ~m by ~m matrix", [
      int(at_nrows),
      int(at_ncols),
      int(bt_nrows),
      int(bt_ncols),
    ])
    |> ignore
  }
  if c.truthy() && (at_nrows != c_nrows || bt_ncols != c_ncols) {
    merr("Cannot add a ~m by ~m matrix to a ~m by ~m C matrix", [
      int(at_nrows),
      int(bt_ncols),
      int(c_nrows),
      int(c_ncols),
    ])
    |> ignore
  }
  // But it doesn't make sense to supply beta without C.
  if betap && !cp {
    merr("beta given, but no C matrix supplied?", []) |> ignore
  }
  let alpha = d_float(alpha)
  beta = d_float(beta)
  let matrix_a = lapack_lispify_matrix(a, a_nrows_v, a_ncols_v)
  let matrix_b = lapack_lispify_matrix(b, b_nrows_v, b_ncols_v)
  let matrix_c = if c.truthy() && !zerop(beta) {
    lapack_lispify_matrix(c, a_nrows_v, b_ncols_v)
  } else {
    // No C matrix given, or beta is zero.  Force beta to be zero to tell
    // LAPACK not to add C.  But we still need to create a matrix.
    beta = Flo(0.0)
    share_lapack__flonum_array(c_nrows * c_ncols)
  }
  let trans_a = if transpose_a.truthy() { "t" } else { "n" }
  let trans_b = if transpose_b.truthy() { "t" } else { "n" }
  let cm = share_lapack__dvec(matrix_c)
  @lapack.dgemm(
    trans_a,
    trans_b,
    at_nrows,
    bt_ncols,
    at_ncols,
    share_f2cl__double(alpha),
    share_lapack__dvec(matrix_a),
    0,
    a_nrows,
    share_lapack__dvec(matrix_b),
    0,
    b_nrows,
    share_f2cl__double(beta),
    cm,
    0,
    c_nrows,
  )
  share_lapack__set_dvec(matrix_c, cm)
  // matrix-c contains the desired result.
  lapack_maxify_matrix(int(c_nrows), int(c_ncols), matrix_c)
}

///|
fn init_share_dgemm() -> Unit raise {
  share_f2cl__install_output()
}
