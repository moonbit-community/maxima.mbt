// Port of share/linearalgebra/linalgcholesky.lisp.

///|
fn d_cholesky(m : Value, fld_name? : Value = q_d_generalring) -> Value raise {
  d_require_nonempty_matrix(m, q_d_first, q_d_cholesky) |> ignore
  d_require_selfadjoint_matrix(m, q_d_first, q_d_cholesky) |> ignore
  let mut n = to_int(d_first(d_matrix_size(m)))
  let fld = d_require_ring(fld_name, q_d_second, q_d_cholesky)
  let fzerop = (a : Value) => share_mring__call(fld, "fzerop", [a])
  let fpsqrt = (a : Value) => share_mring__call(fld, "psqrt", [a])
  let fsub = (a : Value, b : Value) => share_mring__call(fld, "sub", [a, b])
  let fmult = (a : Value, b : Value) => share_mring__call(fld, "mult", [a, b])
  let fadjoint = (a : Value) => share_mring__call(fld, "adjoint", [a])
  let freciprocal = (a : Value) => share_mring__call(fld, "reciprocal", [a])
  let fconvert = (a : Value) => share_mring__call(fld, "maxima-to-mring", [a])
  let frevert = lfunc("frevert", args => share_mring__call(
    fld,
    "mring-to-maxima",
    [args[0]],
  ))
  let l = share_linalgcholesky__array(n, mapcar(s => rest(s), margs(d_zerofor(m))))
  let mat = share_linalgcholesky__array(n, mapcar(s => rest(s), margs(m)))
  n -= 1
  // Convert each entry of mat to a ring member.
  for i in 0..=n {
    for j in 0..=n {
      aset(mat, [i, j], fconvert(aref(mat, [i, j]))) |> ignore
    }
  }
  let mut lii_inv : Value = Nil
  for i in 0..=n {
    let mut acc = aref(mat, [i, i])
    for k in 0..<i {
      acc = fsub(acc, fmult(aref(l, [i, k]), fadjoint(aref(l, [i, k]))))
    }
    let lii = if d_matrixp(acc).truthy() {
      d_cholesky(acc, fld_name~)
    } else {
      fpsqrt(acc)
    }
    if lii is Nil {
      merr("Unable to find the Cholesky factorization", []) |> ignore
    }
    aset(l, [i, i], lii) |> ignore
    if i + 1 <= n {
      if fzerop(lii).truthy() {
        merr("Unable to find the Cholesky factorization", []) |> ignore
      }
      lii_inv = fadjoint(freciprocal(lii))
    }
    for j in (i + 1)..=n {
      let mut acc = aref(mat, [j, i])
      for k in 0..<i {
        acc = fsub(acc, fmult(aref(l, [j, k]), fadjoint(aref(l, [i, k]))))
      }
      aset(l, [j, i], fmult(acc, lii_inv)) |> ignore
    }
  }
  let mut res : Value = Nil
  for i in 0..=n {
    let mut row : Value = Nil
    for j in 0..=n {
      row = cons(full_matrix_map(frevert, aref(l, [i, j])), row)
    }
    row = reverse(row)
    row = cons(list1(q_mlist), row)
    res = cons(row, res)
  }
  res = reverse(res)
  cons(list1(q_d_matrix), res)
}

///|
/// `(make-array (list n n) :initial-contents rows)`
fn share_linalgcholesky__array(n : Int, rows : Value) -> Value raise {
  let a = make_array([n, n])
  let mut i = 0
  for row in rows.iter() {
    let mut j = 0
    for x in row.iter() {
      aset(a, [i, j], x) |> ignore
      j += 1
    }
    i += 1
  }
  a
}

///|
fn init_share_linalgcholesky() -> Unit raise {
  d_put(q_d_cholesky, Fix(1L), q_d_version) |> ignore
}
