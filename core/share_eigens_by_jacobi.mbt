// Port of share/linearalgebra/eigens-by-jacobi.lisp.
//
// One sweep zeros each member of the matrix; for a n x n matrix, this
// requires n(n-1)/2 Jacobi rotations.  For flonum floats, eps is the machine
// epsilon; for bigfloats, it is 1/2^fpprec.  The variable 'change' tracks
// the greatest percent change in a diagonal entry in a sweep; the iteration
// stops when 'change' is less than eps.  The formulae have the form
// new value <-- old value + correction ("Numerical Recipes in Fortran").

///|
fn d_eigens_by_jacobi(mm : Value, fld_name? : Value = q_d_floatfield) -> Value raise {
  if !member(fld_name, list2(q_d_floatfield, q_d_bigfloatfield)).truthy() {
    merr("The field must either be 'floatfield' or 'bigfloatfield'", [])
    |> ignore
  }
  let mm = mfuncall(q_d_mat_fullunblocker, list1(mm))
  d_require_real_symmetric_matrix(mm, q_d_first, q_d_eigens_by_jacobi)
  |> ignore
  let mut sweeps = 0
  let mut rotations = 0
  let mut n = to_int(d_first(d_matrix_size(mm)))
  let mut continue_ = n > 1
  let fld = d_require_ring(fld_name, q_d_second, q_d_eigens_by_jacobi)
  let one = share_mring__call(fld, "mult-id", [])
  let zero = share_mring__call(fld, "add-id", [])
  let fzerop = (a : Value) => share_mring__call(fld, "fzerop", [a]).truthy()
  let fabs = (a : Value) => share_mring__call(fld, "abs", [a])
  let fnegate = (a : Value) => share_mring__call(fld, "negate", [a])
  let fpsqrt = (a : Value) => share_mring__call(fld, "psqrt", [a])
  let fadd = (a : Value, b : Value) => share_mring__call(fld, "add", [a, b])
  let fsub = (a : Value, b : Value) => share_mring__call(fld, "sub", [a, b])
  let fmult = (a : Value, b : Value) => share_mring__call(fld, "mult", [a, b])
  let fdiv = (a : Value, b : Value) => share_mring__call(fld, "div", [a, b])
  let fgreat = (a : Value, b : Value) => share_mring__call(fld, "great", [a, b]).truthy()
  let fmax = (a : Value, b : Value) => if fgreat(a, b) { a } else { b }
  let mat = share_linalgcholesky__array(
    n,
    mapcar(
      s => rest(s),
      margs(matrix_map(share_mring__slot(fld, "maxima-to-mring"), mm)),
    ),
  )
  let v = make_array([n, n], initial=zero)
  let d = make_array([n])
  let eps = if eq(fld_name, q_d_floatfield) {
    symval(q_n_plusflonum_epsilon_plus)
  } else {
    d_bfloat(div(Fix(1L), power(Fix(2L), symval(q_fpprec))))
  }
  n -= 1
  for i in 0..=n {
    aset(v, [i, i], one) |> ignore
    aset1(d, i, aref(mat, [i, i])) |> ignore
  }
  while continue_ {
    if sweeps > 50 {
      merr("Exceeded maximum allowable number of Jacobi sweeps", []) |> ignore
    }
    sweeps += 1
    for p in 0..=n {
      for q in (p + 1)..=n {
        let mpq = aref(mat, [p, q])
        if !fzerop(mpq) {
          rotations += 1
          let theta = fdiv(
            fsub(aref(mat, [q, q]), aref(mat, [p, p])),
            fmult(Fix(2L), mpq),
          )
          let mut tee = fdiv(
            one,
            fadd(fabs(theta), fpsqrt(fadd(one, fmult(theta, theta)))),
          )
          if fgreat(Fix(0L), theta) {
            tee = fnegate(tee)
          }
          let c = fdiv(one, fpsqrt(fadd(one, fmult(tee, tee))))
          let s = fmult(tee, c)
          let tau = fdiv(s, fadd(one, c))
          aset(mat, [p, q], zero) |> ignore
          for k in 0..<p {
            let g = aref(mat, [k, p])
            let h = aref(mat, [k, q])
            aset(mat, [k, p], fsub(g, fmult(s, fadd(h, fmult(g, tau))))) |> ignore
            aset(mat, [k, q], fadd(h, fmult(s, fsub(g, fmult(h, tau))))) |> ignore
          }
          for k in (p + 1)..<q {
            let g = aref(mat, [p, k])
            let h = aref(mat, [k, q])
            aset(mat, [p, k], fsub(g, fmult(s, fadd(h, fmult(g, tau))))) |> ignore
            aset(mat, [k, q], fadd(h, fmult(s, fsub(g, fmult(h, tau))))) |> ignore
          }
          for k in (q + 1)..=n {
            let g = aref(mat, [p, k])
            let h = aref(mat, [q, k])
            aset(mat, [p, k], fsub(g, fmult(s, fadd(h, fmult(g, tau))))) |> ignore
            aset(mat, [q, k], fadd(h, fmult(s, fsub(g, fmult(h, tau))))) |> ignore
          }
          aset(mat, [p, p], fsub(aref(mat, [p, p]), fmult(tee, mpq))) |> ignore
          aset(mat, [q, q], fadd(aref(mat, [q, q]), fmult(tee, mpq))) |> ignore
          for k in 0..=n {
            let g = aref(v, [k, p])
            let h = aref(v, [k, q])
            aset(v, [k, p], fsub(g, fmult(s, fadd(h, fmult(g, tau))))) |> ignore
            aset(v, [k, q], fadd(h, fmult(s, fsub(g, fmult(h, tau))))) |> ignore
          }
        }
      }
    }
    let mut change = zero
    for i in 0..=n {
      let x = aref(mat, [i, i])
      change = fmax(
        change,
        if fgreat(fabs(x), eps) {
          fabs(fdiv(fsub(aref1(d, i), x), x))
        } else {
          zero
        },
      )
      aset1(d, i, x) |> ignore
    }
    inform(
      q_d_debug,
      q_d_linearalgebra,
      Str("The largest percent change was ~:M~%"),
      list1(change),
    )
    |> ignore
    continue_ = fgreat(change, eps)
  }
  inform(
    q_d_verbose,
    q_d_linearalgebra,
    Str("number of sweeps: ~:M~%"),
    list1(int(sweeps)),
  )
  |> ignore
  inform(
    q_d_verbose,
    q_d_linearalgebra,
    Str("number of rotations: ~:M~%"),
    list1(int(rotations)),
  )
  |> ignore
  let mut res : Value = Nil
  for i in 0..=n {
    let mut row : Value = Nil
    for j in 0..=n {
      row = cons(aref(v, [i, j]), row)
    }
    row = reverse(row)
    row = cons(list1(q_mlist), row)
    res = cons(row, res)
  }
  res = reverse(res)
  res = cons(list1(q_d_matrix), res)
  let d = cons(list1(q_mlist), vector_to_list(d))
  list3(list1(q_mlist), d, res)
}

///|
fn init_share_eigens_by_jacobi() -> Unit raise {
  d_put(q_d_eigensbyjacobi, Fix(1L), q_d_version) |> ignore
}
