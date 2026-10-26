// Port of src/invert.lisp: adjoint and matrix inversion.

///|
fn d_adjoint(mat : Value) -> Value raise {
  let n = d_length(mat)
  let adj = simplify(d_ident(n))
  if !like(n, int(1)).truthy() {
    let nn = to_int(n)
    for i in 1..=nn {
      for j in 1..=nn {
        // (maset val adj i j): adj is a matrix, so this is MASET1.
        desoln__maset1(
          mul_star(
            list2(
              power(int(-1), int(i + j)),
              simplify(d_determinant(simplify(d_minor(mat, int(j), int(i))))),
            ),
          ),
          adj,
          [int(i), int(j)],
        )
        |> ignore
      }
    }
  }
  adj
}

///|
fn d_invert_by_adjoint(mat : Value) -> Value raise {
  let adj = simplify(d_adjoint(mat))
  let det = with_special(q_d_scalarmatrixp, t, () => ncmul2(
    simplify(d_row(mat, int(1))),
    simplify(d_col(adj, int(1))),
  ))
  let mat1 = if symval(q_d_scalarmatrixp).truthy() &&
    num_eq(d_length(mat), int(1)) {
    desoln__maref1(adj, [int(1), int(1)])
  } else {
    adj
  }
  if symval(q_d_detout).truthy() {
    list3(list1(q_mtimes), list3(list1(q_mexpt), det, int(-1)), mat1)
  } else {
    div(mat1, det)
  }
}

///|
fn d_invert(args : Value) -> Value raise {
  let m = symval(q_d_invert_method)
  if eq(m, q_d_lu) {
    apply(q_invert_via__dolinvert_by_lu, args)
  } else if eq(m, q_d_gausselim) {
    apply(q_d_invert_by_gausselim, args)
  } else if eq(m, q_d_adjoint) {
    apply(q_d_invert_by_adjoint, args)
  } else if m is Nil {
    // Select a method appropriate for the matrix.
    let my_matrix = first(args)
    let size = length(rest(my_matrix))
    if num_le(int(size), symval(q_d_invert_by_adjoint_size_limit)) {
      apply(q_d_invert_by_adjoint, args)
    } else {
      apply(q_d_invert_by_gausselim, args)
    }
  } else {
    mtell(
      list2(
        Str("invert: unrecognized invert_method=~M; assume default.~%"),
        symval(q_d_invert_method),
      ),
    )
    |> ignore
    with_special(q_d_invert_method, Nil, () => d_invert(args))
  }
}

///|
fn invert_via__dolinvert_by_lu(m : Value, field_name? : Value) -> Value raise {
  let field_name = match field_name {
    Some(f) => f
    None =>
      if symval(q_d_ratmx).truthy() {
        q_d_crering
      } else {
        q_d_generalring
      }
  }
  // Call functions from package linearalgebra via MFUNCALL to autoload them
  // if necessary.
  if symval(q_d_detout).truthy() {
    let field = mfuncall(
      q_d_require_ring,
      list3(field_name, Str("$second"), Str("$invert")),
    )
    let d_i = mfuncall(q_invert_by_lu_with_determinant, list2(m, field_name))
    let d = first(d_i)
    let i = second(d_i)
    let d_times_i = multiply_matrix_elements(
      d,
      mfuncall(q_mring_mult, list1(field)),
      i,
    )
    let d_inv = funcall(mfuncall(q_mring_reciprocal, list1(field)), [d])
    list3(list1(q_mtimes), d_inv, d_times_i)
  } else {
    mfuncall(q_d_invert_by_lu, list2(m, field_name))
  }
}

///|
fn multiply_matrix_elements(a : Value, multiply : Value, m : Value) -> Value raise {
  cons(
    car(m),
    mapcar(
      row => cons(car(row), mapcar(x => funcall(multiply, [a, x]), cdr(row))),
      cdr(m),
    ),
  )
}
