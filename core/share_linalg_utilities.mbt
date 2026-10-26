// Port of share/linearalgebra/linalg-utilities.lisp.

///|
fn inform(level : Value, pck : Value, msg : Value, arg : Value) -> Value raise {
  if member(
      level,
      member(
        d_get(q_d_infolevel, pck),
        list3(q_d_debug, q_d_verbose, q_d_silent),
      ),
    ).truthy() {
    apply(q_mtell, cons(msg, arg))
  } else {
    Nil
  }
}

///|
fn d_require_nonempty_matrix(m : Value, pos : Value, fun : Value) -> Value raise {
  if !(
      d_matrixp(m).truthy() &&
      num_gt(d_length(m), Fix(0L)) &&
      num_gt(d_length(d_first(m)), Fix(0L))
    ) {
    merr("The ~:M argument of the function ~:M must be a nonempty matrix", [
      pos, fun,
    ])
  } else {
    Nil
  }
}

///|
/// Why both some and every? Because we want blockmatrixp(matrix()) --> false.
fn d_blockmatrixp(m : Value) -> Value raise {
  if d_matrixp(m).truthy() && d_some(q_d_matrixp, list1(m)).truthy() {
    d_every(q_d_matrixp, list1(m))
  } else {
    Nil
  }
}

///|
fn d_require_matrix(m : Value, pos : Value, fun : Value) -> Value raise {
  if !d_matrixp(m).truthy() {
    merr("The ~:M argument of the function ~:M must be a matrix", [pos, fun])
  } else {
    Nil
  }
}

///|
fn d_require_unblockedmatrix(m : Value, pos : Value, fun : Value) -> Value raise {
  if !d_matrixp(m).truthy() || d_blockmatrixp(m).truthy() {
    merr("The ~:M argument of the function ~:M must be an unblocked matrix", [
      pos, fun,
    ])
  } else {
    Nil
  }
}

///|
fn d_require_square_matrix(m : Value, pos : Value, fun : Value) -> Value raise {
  if !(d_matrixp(m).truthy() && num_eq(d_length(m), d_length(d_first(m)))) {
    merr("The ~:M argument of the function ~:M must be a square matrix", [
      pos, fun,
    ])
  } else {
    Nil
  }
}

///|
fn array_elem(m : Value, i : Value, j : Value) -> Value raise {
  nth(to_int(j), nth(to_int(i), m))
}

///|
fn d_require_symmetric_matrix(m : Value, pos : Value, fun : Value) -> Value raise {
  if !d_matrixp(m).truthy() {
    merr("The ~:M argument to ~:M must be a matrix", [pos, fun]) |> ignore
  }
  let n = d_matrix_size(m)
  if !num_eq(d_first(n), share_lu__second(n)) {
    merr("The ~:M argument to ~:M must be a square matrix", [pos, fun])
    |> ignore
  }
  if !d_zeromatrixp(sub(m, d_transpose(m))).truthy() {
    merr("The ~:M argument to ~:M must be a symmetric matrix", [pos, fun])
    |> ignore
  }
  q_d_done
}

///|
fn d_require_real_symmetric_matrix(
  m : Value,
  pos : Value,
  fun : Value,
) -> Value raise {
  if !d_matrixp(m).truthy() {
    merr("The ~:M argument to ~:M must be a matrix", [pos, fun]) |> ignore
  }
  let n = d_matrix_size(m)
  if !num_eq(d_first(n), share_lu__second(n)) {
    merr("The ~:M argument to ~:M must be a square matrix", [pos, fun])
    |> ignore
  }
  if d_zeromatrixp(sub(m, d_transpose(m))).truthy() &&
    d_zeromatrixp(sub(m, take(list1(q_d_conjugate), [m]))).truthy() {
    q_d_done
  } else {
    merr("The ~:M argument to ~:M must be a real symmetric matrix", [pos, fun])
  }
}

///|
fn d_require_selfadjoint_matrix(
  m : Value,
  fun : Value,
  pos : Value,
) -> Value raise {
  if !d_matrixp(m).truthy() {
    merr("The ~:M argument to ~:M must be a matrix", [pos, fun]) |> ignore
  }
  let n = d_matrix_size(m)
  if !num_eq(d_first(n), share_lu__second(n)) {
    merr("The ~:M argument to ~:M must be a square matrix", [pos, fun])
    |> ignore
  }
  if !d_zeromatrixp(sub(m, d_ctranspose(m))).truthy() {
    merr(
      "The ~:M argument to ~:M must be a selfadjoint (hermitian) matrix",
      [pos, fun],
    )
    |> ignore
  }
  q_d_done
}

///|
/// matrix() is a 0 x 0 matrix, and matrix([]) is a 1 x 0 matrix.  There is
/// no representation for a 0 x 1 matrix.
fn d_matrix_size(m : Value) -> Value raise {
  d_require_matrix(m, q_d_first, q_d_matrix_size) |> ignore
  list3(
    list1(q_mlist),
    d_length(d_args(m)),
    if d_emptyp(d_args(m)).truthy() {
      Fix(0L)
    } else {
      d_length(d_first(d_args(m)))
    },
  )
}

///|
fn d_require_list(lst : Value, pos : Value, fun : Value) -> Value raise {
  if !d_listp(lst).truthy() {
    merr("The ~:M argument of the function ~:M must be a list", [pos, fun])
  } else {
    Nil
  }
}

///|
fn d_require_posinteger(i : Value, pos : Value, fun : Value) -> Value raise {
  if !(integerp(i) && num_gt(i, Fix(0L))) {
    merr("The ~:M argument of the function ~:M must be a positive integer", [
      pos, fun,
    ])
  } else {
    Nil
  }
}

///|
fn matrix_map(f : Value, mat : Value) -> Value raise {
  let mut mat = mapcar(s => cdr(s), cdr(mat))
  mat = mapcar(s => mapcar(x => funcall(f, [x]), s), mat)
  mat = mapcar(s => cons(list2(q_mlist, q_simp), s), mat)
  cons(list2(q_d_matrix, q_simp), mat)
}

///|
/// Map the lisp function fn over the matrix m. This function is block
/// matrix friendly.
fn full_matrix_map(fn_ : Value, m : Value) -> Value raise {
  if d_listp(m).truthy() || d_matrixp(m).truthy() {
    cons(car(m), mapcar(s => full_matrix_map(fn_, s), cdr(m)))
  } else {
    funcall(fn_, [m])
  }
}

///|
fn d_zerofor(mat : Value, fld_name? : Value = q_d_generalring) -> Value raise {
  let fld = d_require_ring(fld_name, q_d_second, q_d_zerofor)
  let add_id = share_mring__call(fld, "mring-to-maxima", [
    share_mring__call(fld, "add-id", []),
  ])
  zerofor(mat, add_id)
}

///|
fn zerofor(mat : Value, zero : Value) -> Value raise {
  if d_matrixp(mat).truthy() || d_listp(mat).truthy() {
    cons(car(mat), mapcar(s => zerofor(s, zero), cdr(mat)))
  } else {
    zero
  }
}

///|
/// Return an identity matrix that has the same shape as the matrix mat.
/// The first argument 'mat' should be a square Maxima matrix or a
/// non-matrix. When 'mat' is a matrix, each entry of 'mat' can be a square
/// matrix -- thus 'mat' can be a blocked Maxima matrix, to any (finite)
/// depth.
fn d_identfor(mat : Value, fld_name? : Value = q_d_generalring) -> Value raise {
  let fld = d_require_ring(fld_name, q_d_second, q_d_zerofor)
  let add_id = share_mring__call(fld, "mring-to-maxima", [
    share_mring__call(fld, "add-id", []),
  ])
  let mult_id = share_mring__call(fld, "mring-to-maxima", [
    share_mring__call(fld, "mult-id", []),
  ])
  if d_matrixp(mat).truthy() {
    identfor(mat, add_id, mult_id)
  } else {
    mult_id
  }
}

///|
fn identfor(mat : Value, zero : Value, one : Value) -> Value raise {
  let mut new_mat : Value = Nil
  let mut i = 0
  for row in rest(mat).iter() {
    let mut acc : Value = Nil
    let mut j = 0
    for aij in rest(row).iter() {
      acc = cons(
        if d_matrixp(aij).truthy() {
          if i == j {
            identfor(aij, zero, one)
          } else {
            zerofor(aij, zero)
          }
        } else if i == j {
          one
        } else {
          zero
        },
        acc,
      )
      j += 1
    }
    i += 1
    acc = cons(list1(q_mlist), acc)
    new_mat = cons(acc, new_mat)
  }
  cons(list1(q_d_matrix), new_mat)
}

///|
fn d_ctranspose(m : Value) -> Value raise {
  mfuncall(
    q_d_transpose,
    list1(
      full_matrix_map(
        lfunc("conjugate", args => simplifya(
          list2(list1(q_d_conjugate), args[0]),
          Nil,
        )),
        m,
      ),
    ),
  )
}

///|
fn d_zeromatrixp(m : Value) -> Value raise {
  if d_matrixp(m).truthy() || d_listp(m).truthy() {
    lbool(every(s => d_zeromatrixp(s).truthy(), cdr(m)))
  } else {
    lbool(eq(q_d_zero, csign(d_rectform(m))))
  }
}

///|
fn share_linalg_utilities__call(fn_ : Value, x : Value) -> Value raise {
  if eq(fn_, q_identity) {
    x
  } else {
    funcall(fn_, [x])
  }
}

///|
fn array_to_row_list(mat : Value, fn_? : Value = q_identity) -> Value raise {
  let r = array_dimension(mat, 0)
  let c = array_dimension(mat, 1)
  let mut acc : Value = Nil
  for i in 0..<r {
    let mut row : Value = Nil
    for j in 0..<c {
      row = cons(share_linalg_utilities__call(fn_, aref(mat, [i, j])), row)
    }
    row = reverse(row)
    acc = cons(row, acc)
  }
  reverse(acc)
}

///|
fn array_to_maxima_matrix(mat : Value, fn_? : Value = q_identity) -> Value raise {
  cons(
    list1(q_d_matrix),
    mapcar(s => cons(list1(q_mlist), s), array_to_row_list(mat, fn_~)),
  )
}

///|
fn array_to_maxima_list(ar : Value, fn_? : Value = q_identity) -> Value raise {
  cons(
    list1(q_mlist),
    mapcar(x => share_linalg_utilities__call(fn_, x), vector_to_list(ar)),
  )
}

///|
fn maxima_to_array(
  mat : Value,
  fn_? : Value = q_identity,
  typ? : Value = Nil,
) -> Value raise {
  ignore(typ)
  let r = d_matrix_size(mat)
  let c = to_int(share_lu__second(r))
  let r = to_int(d_first(r))
  let rows = mapcar(s => cdr(s), cdr(mat))
  let rows = mapcar(
    s => mapcar(w => share_linalg_utilities__call(fn_, w), s),
    rows,
  )
  let a = make_array([r, c])
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
fn init_share_linalg_utilities() -> Unit raise {
  d_put(q_d_linalgutilities, Fix(2L), q_d_version) |> ignore
}
