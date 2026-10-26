// Port of share/lapack/dgeqrf.lisp -- Maxima interface to lapack::dgeqrf.
// Copyright 2011 by Robert Dodier; GPL.
//
// dgeqrf(a) computes the QR factorization of an m-by-n Maxima matrix,
// where m and n might be equal or unequal.  a is not modified.  The
// unpacking of Q and R works on the Lisp vectors with CL arithmetic, as
// the Lisp does.

///|
fn d_dgeqrf(a : Value) -> Value raise {
  let (a_nrow, a_ncol) = maxima_matrix_dims(a)
  let m = to_int(a_nrow)
  let n = to_int(a_ncol)
  let a_mat = lapack_lispify_matrix(a, a_nrow, a_ncol)
  let am = share_lapack__dvec(a_mat)
  let work0 : FixedArray[Double] = FixedArray::make(1, 0.0)
  let tau_v = share_lapack__flonum_array(if m < n { m } else { n })
  let tau = share_lapack__dvec(tau_v)
  // First call DGEQRF with LWORK = -1 to find optimal block size NB.  Use
  // that to compute LWORK.
  @lapack.dgeqrf(m, n, am, m, tau, 0, work0, 0, -1, 0) |> ignore
  let lwork = work0[0].floor().to_int()
  let work : FixedArray[Double] = FixedArray::make(lwork, 0.0)
  let z_info = @lapack.dgeqrf(m, n, am, m, tau, 0, work, 0, lwork, 0)
  share_lapack__set_dvec(a_mat, am)
  share_lapack__set_dvec(tau_v, tau)
  if z_info < 0 {
    merr("dgeqrf: ~M-th argument has an illegal value.", [int(-z_info)])
  } else {
    dgeqrf_unpack(a_nrow, a_ncol, a_mat, tau_v)
  }
}

///|
fn dgeqrf_unpack(
  a_nrow : Value,
  a_ncol : Value,
  a_mat : Value,
  tau : Value,
) -> Value raise {
  let r = dgeqrf_unpack_r(a_nrow, a_ncol, a_mat)
  let q = dgeqrf_unpack_q(a_nrow, a_ncol, a_mat, tau)
  list3(list1(q_mlist), q, r)
}

///|
fn dgeqrf_unpack_r(a_nrow : Value, a_ncol : Value, a_mat : Value) -> Value raise {
  let nr = to_int(a_nrow)
  let nc = to_int(a_ncol)
  let r_nrow = nr
  let r_ncol = nc
  let r_mat = make_array([r_ncol * r_nrow], initial=Flo(0.0))
  for j in 0..<nc {
    for i in 0..<(j + 1) {
      if i < r_nrow {
        let a_ij = j * nr + i
        let r_ij = j * r_nrow + i
        aset1(r_mat, r_ij, aref1(a_mat, a_ij)) |> ignore
      }
    }
  }
  lapack_maxify_matrix(int(r_nrow), int(r_ncol), r_mat)
}

///|
fn dgeqrf_unpack_q(
  a_nrow : Value,
  a_ncol : Value,
  a_mat : Value,
  tau : Value,
) -> Value raise {
  let nr = to_int(a_nrow)
  let nc = to_int(a_ncol)
  let q_mat = make_array([nr * nr], initial=Flo(0.0))
  for i in 0..<nr {
    aset1(q_mat, i * nr + i, Flo(1.0)) |> ignore
  }
  for i in 0..<(if nr < nc { nr } else { nc }) {
    let h_mat_i = dgeqrf_h(int(i), tau, a_nrow, a_mat)
    dgeqrf_multiply_into(a_nrow, q_mat, h_mat_i) |> ignore
  }
  lapack_maxify_matrix(a_nrow, a_nrow, q_mat)
}

///|
fn dgeqrf_h(i : Value, tau : Value, a_nrow : Value, a_mat : Value) -> Value raise {
  let nr = to_int(a_nrow)
  let h_mat = make_array([nr * nr], initial=Flo(0.0))
  for j in 0..<nr {
    for k in 0..<nr {
      let v_j = dgeqrf_v(i, int(j), a_nrow, a_mat)
      let v_k = dgeqrf_v(i, int(k), a_nrow, a_mat)
      let foo = num_mul(num_mul(aref1(tau, to_int(i)), v_j), v_k)
      let bar = if j == k { num_add(num_neg(foo), Fix(1L)) } else { num_neg(foo) }
      aset1(h_mat, k * nr + j, bar) |> ignore
    }
  }
  h_mat
}

///|
fn dgeqrf_v(i : Value, j : Value, a_nrow : Value, a_mat : Value) -> Value raise {
  let ii = to_int(i)
  let jj = to_int(j)
  if jj == ii {
    Fix(1L)
  } else if jj > ii {
    aref1(a_mat, ii * to_int(a_nrow) + jj)
  } else {
    Fix(0L)
  }
}

///|
fn dgeqrf_multiply_into(n : Value, mat_1 : Value, mat_2 : Value) -> Value raise {
  let nn = to_int(n)
  let row = make_array([nn], initial=Flo(0.0))
  for i in 0..<nn {
    for j in 0..<nn {
      aset1(row, j, dgeqrf_inner_product(n, mat_1, mat_2, int(i), int(j)))
      |> ignore
    }
    for j in 0..<nn {
      aset1(mat_1, j * nn + i, aref1(row, j)) |> ignore
    }
  }
  Nil
}

///|
fn dgeqrf_inner_product(
  n : Value,
  mat_1 : Value,
  mat_2 : Value,
  i : Value,
  j : Value,
) -> Value raise {
  let nn = to_int(n)
  let ii = to_int(i)
  let jj = to_int(j)
  let mut sum : Value = Fix(0L)
  for k in 0..<nn {
    sum = num_add(sum, num_mul(aref1(mat_1, k * nn + ii), aref1(mat_2, jj * nn + k)))
  }
  sum
}

///|
fn init_share_dgeqrf() -> Unit raise {
  share_f2cl__install_output()
}
