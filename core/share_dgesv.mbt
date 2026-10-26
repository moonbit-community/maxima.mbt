// Port of share/lapack/dgesv.lisp -- Maxima interface to lapack::dgesv.
// Copyright 2010 by Robert Dodier; GPL.

///|
/// dgesv(a, b) returns solution x of linear equations a . x = b as computed
/// by the LU decomposition.  a is a n-by-n Maxima matrix, b is a n-by-m
/// Maxima matrix, where m maybe be greater than or equal to 1.  a and b are
/// not modified.
fn d_dgesv(a : Value, b : Value) -> Value raise {
  let (a_nrow, a_ncol) = maxima_matrix_dims(a)
  let (b_nrow, b_ncol) = maxima_matrix_dims(b)
  let a_mat = lapack_lispify_matrix(a, a_nrow, a_ncol)
  let b_mat = lapack_lispify_matrix(b, b_nrow, b_ncol)
  let ipiv : FixedArray[Int] = FixedArray::make(to_int(a_nrow), 0)
  let am = share_lapack__dvec(a_mat)
  let bm = share_lapack__dvec(b_mat)
  let z_info = @lapack.dgesv(
    to_int(a_nrow),
    to_int(b_ncol),
    am,
    to_int(a_nrow),
    ipiv,
    bm,
    to_int(b_nrow),
    0,
  )
  share_lapack__set_dvec(a_mat, am)
  share_lapack__set_dvec(b_mat, bm)
  if z_info < 0 {
    merr("dgesv: ~M-th argument has an illegal value.", [int(-z_info)])
  } else if z_info > 0 {
    merr("dgesv: U(~M, ~M) is exactly zero; cannot compute a solution.", [
      int(z_info),
      int(z_info),
    ])
  } else {
    lapack_maxify_matrix(b_nrow, b_ncol, b_mat)
  }
}

///|
fn init_share_dgesv() -> Unit raise {
  share_f2cl__install_output()
}
