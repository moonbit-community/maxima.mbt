// Port of share/amatrix/amatrix.lisp (Robert Dodier, 2007): Maxima
// matrices implemented via an underlying Lisp array (the Maxima side is in
// amatrix.mac).

///|
/// The storage array of an amatrix: (get ($@-function m '$storage)
/// 'storage_array).
fn share_amatrix__storage_array(m : Value) -> Value raise {
  get(d__at_function(m, q_d_storage), q_storage_array)
}

///|
fn d_amatrixmap(f : Value, m : Value) -> Value raise {
  let nr = d_nrows(car(m))
  let nc = d_ncols(car(m))
  let m1 = mfuncall(q_d_make_matrix, list2(nr, nc))
  let a1 = share_amatrix__storage_array(m1)
  for i in 0..<to_int(nr) {
    for j in 0..<to_int(nc) {
      let args = mapcar(
        m0 => {
          let a0 = share_amatrix__storage_array(m0)
          let ij = mfuncall(q_d_compute_index0, list3(m0, int(i), int(j)))
          aref(a0, [to_int(ij)])
        },
        m,
      )
      let x = mapply1(f, args, f, Nil)
      aset(
        a1,
        [to_int(mfuncall(q_d_compute_index0, list3(m1, int(i), int(j))))],
        x,
      )
      |> ignore
    }
  }
  m1
}

///|
fn amatrix_assign(e : Value, x : Value) -> Value raise {
  let my_amatrix_name = caar(e)
  let my_amatrix = symval(caar(e))
  let n = length(e)
  if n == 2 {
    if num_eq(d_nrows(my_amatrix), Fix(1L)) {
      amatrix_assign1(my_amatrix_name, my_amatrix, Fix(1L), meval(cadr(e)), x)
    } else if num_eq(d_ncols(my_amatrix), Fix(1L)) {
      amatrix_assign1(my_amatrix_name, my_amatrix, meval(cadr(e)), Fix(1L), x)
    } else {
      merr("amatrix assignment: given one subscript, but expected two", [])
    }
  } else if n == 3 {
    amatrix_assign1(
      caar(e),
      symval(caar(e)),
      meval(cadr(e)),
      meval(caddr(e)),
      x,
    )
  } else {
    merr("amatrix assignment: expected one or two subscripts", [])
  }
}

///|
fn amatrix_assign1(
  lhs : Value,
  aa : Value,
  i : Value,
  j : Value,
  x : Value,
) -> Value raise {
  let storage = d__at_function(aa, q_d_storage)
  if num_gt(get(storage, q_refcount), Fix(1L)) {
    let a = gensym()
    putprop(a, Fix(1L), q_refcount) |> ignore
    putprop(
      a,
      mfuncall(q_d_copy_array, list1(get(storage, q_storage_array))),
      q_storage_array,
    )
    |> ignore
    putprop(storage, num_sub(get(storage, q_refcount), Fix(1L)), q_refcount)
    |> ignore
    mrecord_assign(list3(list1(q_d_op_at), lhs, q_d_storage), a) |> ignore
  }
  if integerp(i) && integerp(j) {
    amatrix_assign1_row_column(aa, i, j, x)
  } else if eq(i, q_d_all) && integerp(j) {
    amatrix_assign1_all_column(aa, j, x)
  } else if integerp(i) && eq(j, q_d_all) {
    amatrix_assign1_row_all(aa, i, x)
  } else if eq(i, q_d_all) && eq(j, q_d_all) {
    amatrix_assign1_all_all(aa, x)
  } else if d_listp(i).truthy() && integerp(j) {
    amatrix_assign1_list_integer(aa, i, j, x)
  } else if integerp(i) && d_listp(j).truthy() {
    amatrix_assign1_integer_list(aa, i, j, x)
  } else if d_listp(i).truthy() && eq(j, q_d_all) {
    amatrix_assign1_list_all(aa, i, x)
  } else if eq(i, q_d_all) && d_listp(j).truthy() {
    amatrix_assign1_all_list(aa, j, x)
  } else if d_listp(i).truthy() && d_listp(j).truthy() {
    amatrix_assign1_list_list(aa, i, j, x)
  } else {
    list3(list1(q_mset), list3(list2(aa, q_array), i, j), x)
  }
}

///|
fn amatrix_assign1_row_column(
  aa : Value,
  i : Value,
  j : Value,
  x : Value,
) -> Value raise {
  let a = share_amatrix__storage_array(aa)
  let ij = num_sub(mfuncall(q_d_compute_index1, list3(aa, i, j)), Fix(1L))
  aset(a, [to_int(ij)], x)
}

///|
fn amatrix_assign1_all_column(aa : Value, j : Value, x : Value) -> Value raise {
  let m = to_int(d__at_function(aa, q_d_nr))
  if d_amatrixp(x).truthy() {
    for i in 0..<m {
      amatrix_assign1_row_column(
        aa,
        int(i + 1),
        j,
        mfuncall(q_d_get_element, list3(x, int(i + 1), Fix(1L))),
      )
      |> ignore
    }
  } else {
    for i in 0..<m {
      amatrix_assign1_row_column(aa, int(i + 1), j, x) |> ignore
    }
  }
  x
}

///|
fn amatrix_assign1_row_all(aa : Value, i : Value, x : Value) -> Value raise {
  let n = to_int(d__at_function(aa, q_d_nc))
  if d_amatrixp(x).truthy() {
    for j in 0..<n {
      amatrix_assign1_row_column(
        aa,
        i,
        int(j + 1),
        mfuncall(q_d_get_element, list3(x, Fix(1L), int(j + 1))),
      )
      |> ignore
    }
  } else {
    for j in 0..<n {
      amatrix_assign1_row_column(aa, i, int(j + 1), x) |> ignore
    }
  }
  x
}

///|
fn amatrix_assign1_all_all(aa : Value, x : Value) -> Value raise {
  let m = to_int(d__at_function(aa, q_d_nr))
  let n = to_int(d__at_function(aa, q_d_nc))
  if d_amatrixp(x).truthy() {
    for i in 0..<m {
      for j in 0..<n {
        amatrix_assign1_row_column(
          aa,
          int(i + 1),
          int(j + 1),
          mfuncall(q_d_get_element, list3(x, int(i + 1), int(j + 1))),
        )
        |> ignore
      }
    }
  } else {
    for i in 0..<m {
      for j in 0..<n {
        amatrix_assign1_row_column(aa, int(i + 1), int(j + 1), x) |> ignore
      }
    }
  }
  x
}

///|
fn amatrix_assign1_list_integer(
  aa : Value,
  l : Value,
  j : Value,
  x : Value,
) -> Value raise {
  amatrix_assign1_list_list(aa, l, list2(list1(q_mlist), j), x)
}

///|
fn amatrix_assign1_integer_list(
  aa : Value,
  i : Value,
  l : Value,
  x : Value,
) -> Value raise {
  amatrix_assign1_list_list(aa, list2(list1(q_mlist), i), l, x)
}

///|
fn amatrix_assign1_list_all(aa : Value, l : Value, x : Value) -> Value raise {
  let m = to_int(d_length(l))
  let n = to_int(d__at_function(aa, q_d_nc))
  if d_amatrixp(x).truthy() {
    for i in 0..<m {
      for j in 0..<n {
        amatrix_assign1_row_column(
          aa,
          nth(i + 1, l),
          int(j + 1),
          mfuncall(q_d_get_element, list3(x, int(i + 1), int(j + 1))),
        )
        |> ignore
      }
    }
  } else {
    for i in 0..<m {
      for j in 0..<n {
        amatrix_assign1_row_column(aa, nth(i + 1, l), int(j + 1), x) |> ignore
      }
    }
  }
  x
}

///|
fn amatrix_assign1_all_list(aa : Value, l : Value, x : Value) -> Value raise {
  let m = to_int(d__at_function(aa, q_d_nr))
  let n = to_int(d_length(l))
  if d_amatrixp(x).truthy() {
    for i in 0..<m {
      for j in 0..<n {
        amatrix_assign1_row_column(
          aa,
          int(i + 1),
          nth(j + 1, l),
          mfuncall(q_d_get_element, list3(x, int(i + 1), int(j + 1))),
        )
        |> ignore
      }
    }
  } else {
    for i in 0..<m {
      for j in 0..<n {
        amatrix_assign1_row_column(aa, int(i + 1), nth(j + 1, l), x) |> ignore
      }
    }
  }
  x
}

///|
fn amatrix_assign1_list_list(
  aa : Value,
  l1 : Value,
  l2 : Value,
  x : Value,
) -> Value raise {
  let m = to_int(d_length(l1))
  let n = to_int(d_length(l2))
  if d_amatrixp(x).truthy() {
    for i in 0..<m {
      for j in 0..<n {
        amatrix_assign1_row_column(
          aa,
          nth(i + 1, l1),
          nth(j + 1, l2),
          mfuncall(q_d_get_element, list3(x, int(i + 1), int(j + 1))),
        )
        |> ignore
      }
    }
  } else {
    for i in 0..<m {
      for j in 0..<n {
        amatrix_assign1_row_column(aa, nth(i + 1, l1), nth(j + 1, l2), x)
        |> ignore
      }
    }
  }
  x
}

// UNFINISHED STUFF in amatrix.lisp: these do nothing.

///|
fn amatrix_assign1_amatrix_column(
  aa : Value,
  ai : Value,
  j : Value,
  x : Value,
) -> Value raise {
  ignore((aa, ai, j, x))
  Nil
}

///|
fn amatrix_assign1_row_amatrix(
  aa : Value,
  i : Value,
  aj : Value,
  x : Value,
) -> Value raise {
  ignore((aa, i, aj, x))
  Nil
}

///|
fn amatrix_assign1_amatrix_amatrix(
  aa : Value,
  ai : Value,
  aj : Value,
  x : Value,
) -> Value raise {
  ignore((aa, ai, aj, x))
  Nil
}

///|
fn amatrix_assign1_boolean_column(
  aa : Value,
  b : Value,
  j : Value,
  x : Value,
) -> Value raise {
  ignore((aa, b, j, x))
  Nil
}

///|
fn amatrix_assign1_row_boolean(
  aa : Value,
  i : Value,
  b : Value,
  x : Value,
) -> Value raise {
  ignore((aa, i, b, x))
  Nil
}

///|
fn amatrix_assign1_boolean_boolean(
  aa : Value,
  b1 : Value,
  b2 : Value,
  x : Value,
) -> Value raise {
  ignore((aa, b1, b2, x))
  Nil
}

///|
/// Calls SIMPLIFYA because DIM-$MATRIX needs to see the SIMP flag.
fn dim__dolamatrix(form : Value, result : Value) -> Value raise {
  let nr = d__at_function(form, q_d_nr)
  let r0 = d__at_function(form, q_d_r0)
  let rinc = d__at_function(form, q_d_rinc)
  let nc = d__at_function(form, q_d_nc)
  let c0 = d__at_function(form, q_d_c0)
  let cinc = d__at_function(form, q_d_cinc)
  let storage = d__at_function(form, q_d_storage)
  if integerp(nr) &&
    integerp(r0) &&
    integerp(rinc) &&
    integerp(nc) &&
    integerp(c0) &&
    integerp(cinc) &&
    symbolp(storage) &&
    arrayp(get(storage, q_storage_array)) {
    if num_eq(nr, Fix(0L)) || num_eq(nc, Fix(0L)) {
      dimension_function(list1(list2(q_d_amatrix, q_simp)), result)
    } else {
      dim__dolmatrix(
        simplifya(
          d_genmatrix(
            list3(
              list1(q_lambda),
              list3(list1(q_mlist), q_i, q_j),
              list([
                q_mfuncall,
                list2(q_quote, q_d_get_element),
                form,
                q_i,
                q_j,
              ]),
            ),
            d__at_function(form, q_d_nr),
            j2=d__at_function(form, q_d_nc),
          ),
          t,
        ),
        result,
      )
    }
  } else {
    dimension_function(form, result)
  }
}

///|
fn d_amatrixp(a : Value) -> Value raise {
  lbool(!d_atom(a).truthy() && eq(d_op(a), q_d_amatrix))
}

///|
fn d_nrows(a : Value) -> Value raise {
  if d_amatrixp(a).truthy() {
    d__at_function(a, q_d_nr)
  } else {
    list2(list1(q_d_nrows), a)
  }
}

///|
fn d_ncols(a : Value) -> Value raise {
  if d_amatrixp(a).truthy() {
    d__at_function(a, q_d_nc)
  } else {
    list2(list1(q_d_ncols), a)
  }
}

///|
fn d_amatrix_multiply(m1 : Value, m2 : Value) -> Value raise {
  let nc1 = d_ncols(m1)
  let nr2 = d_nrows(m2)
  if integerp(nc1) && integerp(nr2) {
    if eql(d_ncols(m1), d_nrows(m2)) {
      let aa = gensym()
      let nn = d_ncols(m1)
      let nr = d_nrows(m1)
      let a1 = share_amatrix__storage_array(m1)
      let a1_inc = d__at_function(m1, q_d_cinc)
      let nc = d_ncols(m2)
      let a2 = share_amatrix__storage_array(m2)
      let a2_inc = d__at_function(m2, q_d_rinc)
      let nri = to_int(nr)
      let nci = to_int(nc)
      putprop(aa, make_array([nri * nci], initial=Fix(0L)), q_storage_array)
      |> ignore
      for i in 0..<nri {
        for j in 0..<nci {
          let a1_base = mfuncall(q_d_compute_index0, list3(m1, int(i), Fix(0L)))
          let a2_base = mfuncall(q_d_compute_index0, list3(m2, Fix(0L), int(j)))
          aset(
            get(aa, q_storage_array),
            [i + j * nri],
            dot(nn, a1, a1_base, a1_inc, a2, a2_base, a2_inc),
          )
          |> ignore
        }
      }
      list([
        list1(q_d_amatrix),
        nr,
        Fix(0L),
        Fix(1L),
        nc,
        Fix(0L),
        nr,
        aa,
        Fix(0L),
      ])
    } else {
      merr("amatrix_multiply: inconformable operands", [])
    }
  } else {
    list3(list1(q_mnctimes), m1, m2)
  }
}

///|
fn dot(
  n : Value,
  a : Value,
  a0 : Value,
  ainc : Value,
  b : Value,
  b0 : Value,
  binc : Value,
) -> Value raise {
  let mut ai = a0
  let mut bi = b0
  let mut sum : Value = Fix(0L)
  for _ in 0..<to_int(n) {
    sum = num_add(sum, num_mul(aref(a, [to_int(ai)]), aref(b, [to_int(bi)])))
    ai = num_add(ai, ainc)
    bi = num_add(bi, binc)
  }
  sum
}

///|
fn init_share_amatrix() -> Unit raise {
  putprop(q_d_amatrix, t, q_d_present) |> ignore
  putprop(q_d_amatrix, q_amatrix_assign, q_mset_extension_operator) |> ignore
  putprop(q_d_amatrix, q_dim__dolamatrix, q_dimension) |> ignore
}
