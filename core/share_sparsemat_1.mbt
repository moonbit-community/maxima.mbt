// Translation of share/affine/sparsemat.lisp (part 1): sparse matrices
// for the affine package.
//
// A SPARSE-MATRIX (CL defstruct, not :type list) is
// `make_struct("sparse-matrix", [33 slots])`, the slots in defstruct order
// (0 rows, 1 number-of-rows, 2 type-of-entries, 3 current-row,
// 4 current-row-number, 5 current-row-length, 6 pivot-row,
// 7 pivot-row-number, 8 characteristic, 9 inverse-array,
// 10 special-inverse, 11 special-plus, 12 minimum-size-to-grow,
// 13 allow-reorder, 14 last-good-row, 15 columns-used-to-pivot,
// 16 column-used-in-row, 17 list-of-all-columns-occurring, 18 pivot-entry,
// 19 pivot-test-list, 20 row-number-before-swap, 21 special-multiply,
// 22 transpose, 23 reduced, 24 sort-pivot, 25 sign-of-row-permutation,
// 26 current-column-above-pivot-row-number, 27 columns-with-no-pivot,
// 28 rows-with-no-pivot, 29 solutions, 30 constants-column-number,
// 31 special-solution, 32 constants-column).  Other files reach the slots
// with `struct_ref(m, i)` / `struct_set(m, i, v)` (accessor names
// `sparsemat__<slot>` / `sparsemat__set_<slot>` below) and build one with
// `sparsemat__make_sparse_matrix()`.
//
// A row is a vector with fill pointer holding alternately a column number
// (or NIL for an empty slot) and the entry.
//
// SBCL fills arrays made without :initial-element with 0; the
// translations below pass `initial=Fix(0L)` where the Lisp relies on that.

///|
fn sparsemat__make_sparse_matrix() -> Value {
  make_struct("sparse-matrix", [
    Nil, // rows
    Nil, // number-of-rows
    Nil, // type-of-entries
    Nil, // current-row
    Nil, // current-row-number
    Nil, // current-row-length
    Nil, // pivot-row
    Nil, // pivot-row-number
    Nil, // characteristic
    Nil, // inverse-array
    Nil, // special-inverse
    Nil, // special-plus
    Fix(1L), // minimum-size-to-grow
    t, // allow-reorder
    Nil, // last-good-row
    Nil, // columns-used-to-pivot
    Nil, // column-used-in-row
    Nil, // list-of-all-columns-occurring
    Nil, // pivot-entry
    sparsemat__default_pivot_test_list, // pivot-test-list
    Nil, // row-number-before-swap
    Nil, // special-multiply
    Nil, // transpose
    Nil, // reduced
    Nil, // sort-pivot
    Fix(1L), // sign-of-row-permutation
    Nil, // current-column-above-pivot-row-number
    Nil, // columns-with-no-pivot
    Nil, // rows-with-no-pivot
    Nil, // solutions
    Nil, // constants-column-number
    Nil, // special-solution
    Nil, // constants-column
  ])
}

///|
let sparsemat__default_pivot_test_list : Value = list([q_unit, q_min])

///|
/// `(make-solution-row)`: a SOLUTION-ROW defstruct (number data).
fn sparsemat__make_solution_row() -> Value {
  make_struct("solution-row", [Nil, Nil])
}

///|
fn sparsemat__rows(m : Value) -> Value raise {
  struct_ref(m, 0)
}

///|
fn sparsemat__set_rows(m : Value, v : Value) -> Value raise {
  struct_set(m, 0, v)
}

///|
fn sparsemat__type_of_entries(m : Value) -> Value raise {
  struct_ref(m, 2)
}

///|
fn sparsemat__set_type_of_entries(m : Value, v : Value) -> Value raise {
  struct_set(m, 2, v)
}

///|
fn sparsemat__current_row(m : Value) -> Value raise {
  struct_ref(m, 3)
}

///|
fn sparsemat__set_current_row(m : Value, v : Value) -> Value raise {
  struct_set(m, 3, v)
}

///|
fn sparsemat__current_row_number(m : Value) -> Value raise {
  struct_ref(m, 4)
}

///|
fn sparsemat__set_current_row_number(m : Value, v : Value) -> Value raise {
  struct_set(m, 4, v)
}

///|
fn sparsemat__set_current_row_length(m : Value, v : Value) -> Value raise {
  struct_set(m, 5, v)
}

///|
fn sparsemat__pivot_row(m : Value) -> Value raise {
  struct_ref(m, 6)
}

///|
fn sparsemat__set_pivot_row(m : Value, v : Value) -> Value raise {
  struct_set(m, 6, v)
}

///|
fn sparsemat__pivot_row_number(m : Value) -> Value raise {
  struct_ref(m, 7)
}

///|
fn sparsemat__set_pivot_row_number(m : Value, v : Value) -> Value raise {
  struct_set(m, 7, v)
}

///|
fn sparsemat__characteristic(m : Value) -> Value raise {
  struct_ref(m, 8)
}

///|
fn sparsemat__set_characteristic(m : Value, v : Value) -> Value raise {
  struct_set(m, 8, v)
}

///|
fn sparsemat__minimum_size_to_grow(m : Value) -> Value raise {
  struct_ref(m, 12)
}

///|
fn sparsemat__last_good_row(m : Value) -> Value raise {
  struct_ref(m, 14)
}

///|
fn sparsemat__set_last_good_row(m : Value, v : Value) -> Value raise {
  struct_set(m, 14, v)
}

///|
fn sparsemat__columns_used_to_pivot(m : Value) -> Value raise {
  struct_ref(m, 15)
}

///|
fn sparsemat__set_columns_used_to_pivot(m : Value, v : Value) -> Value raise {
  struct_set(m, 15, v)
}

///|
fn sparsemat__column_used_in_row(m : Value) -> Value raise {
  struct_ref(m, 16)
}

///|
fn sparsemat__set_column_used_in_row(m : Value, v : Value) -> Value raise {
  struct_set(m, 16, v)
}

///|
fn sparsemat__list_of_all_columns_occurring(m : Value) -> Value raise {
  struct_ref(m, 17)
}

///|
fn sparsemat__set_list_of_all_columns_occurring(
  m : Value,
  v : Value,
) -> Value raise {
  struct_set(m, 17, v)
}

///|
fn sparsemat__pivot_entry(m : Value) -> Value raise {
  struct_ref(m, 18)
}

///|
fn sparsemat__set_pivot_entry(m : Value, v : Value) -> Value raise {
  struct_set(m, 18, v)
}

///|
fn sparsemat__pivot_test_list(m : Value) -> Value raise {
  struct_ref(m, 19)
}

///|
fn sparsemat__set_pivot_test_list(m : Value, v : Value) -> Value raise {
  struct_set(m, 19, v)
}

///|
fn sparsemat__row_number_before_swap(m : Value) -> Value raise {
  struct_ref(m, 20)
}

///|
fn sparsemat__set_row_number_before_swap(m : Value, v : Value) -> Value raise {
  struct_set(m, 20, v)
}

///|
fn sparsemat__set_transpose(m : Value, v : Value) -> Value raise {
  struct_set(m, 22, v)
}

///|
fn sparsemat__reduced(m : Value) -> Value raise {
  struct_ref(m, 23)
}

///|
fn sparsemat__set_reduced(m : Value, v : Value) -> Value raise {
  struct_set(m, 23, v)
}

///|
fn sparsemat__sign_of_row_permutation(m : Value) -> Value raise {
  struct_ref(m, 25)
}

///|
fn sparsemat__set_sign_of_row_permutation(
  m : Value,
  v : Value,
) -> Value raise {
  struct_set(m, 25, v)
}

///|
fn sparsemat__current_column_above_pivot_row_number(
  m : Value,
) -> Value raise {
  struct_ref(m, 26)
}

///|
fn sparsemat__set_current_column_above_pivot_row_number(
  m : Value,
  v : Value,
) -> Value raise {
  struct_set(m, 26, v)
}

///|
fn sparsemat__columns_with_no_pivot(m : Value) -> Value raise {
  struct_ref(m, 27)
}

///|
fn sparsemat__set_columns_with_no_pivot(m : Value, v : Value) -> Value raise {
  struct_set(m, 27, v)
}

///|
fn sparsemat__rows_with_no_pivot(m : Value) -> Value raise {
  struct_ref(m, 28)
}

///|
fn sparsemat__set_rows_with_no_pivot(m : Value, v : Value) -> Value raise {
  struct_set(m, 28, v)
}

///|
fn sparsemat__solutions(m : Value) -> Value raise {
  struct_ref(m, 29)
}

///|
fn sparsemat__set_solutions(m : Value, v : Value) -> Value raise {
  struct_set(m, 29, v)
}

///|
fn sparsemat__constants_column_number(m : Value) -> Value raise {
  struct_ref(m, 30)
}

///|
fn sparsemat__set_constants_column_number(
  m : Value,
  v : Value,
) -> Value raise {
  struct_set(m, 30, v)
}

///|
fn sparsemat__special_solution(m : Value) -> Value raise {
  struct_ref(m, 31)
}

///|
fn sparsemat__set_special_solution(m : Value, v : Value) -> Value raise {
  struct_set(m, 31, v)
}

///|
fn sparsemat__constants_column(m : Value) -> Value raise {
  struct_ref(m, 32)
}

///|
fn sparsemat__set_constants_column(m : Value, v : Value) -> Value raise {
  struct_set(m, 32, v)
}

// ---------------------------------------------------------------------
// Low-level helpers

///|
/// `(aref (sp-rows sp-mat) i)` with a Lisp integer index.
fn sparsemat__row(sp_mat : Value, i : Value) -> Value raise {
  aref1(sparsemat__rows(sp_mat), to_int(i))
}

///|
/// The number of rows: `(fill-pointer (sp-rows sp-mat))`.
fn sparsemat__nrows(sp_mat : Value) -> Int raise {
  fill_pointer(sparsemat__rows(sp_mat))
}

///|
/// CL `vector-push`: stores V at the fill pointer if there is room and
/// returns the index, else returns NIL.
fn sparsemat__vector_push(v : Value, arr : Value) -> Value raise {
  let a = as_array(arr)
  let f = fill_pointer(arr)
  if f < a.data.length() {
    a.data[f] = v
    a.fill = Some(f + 1)
    int(f)
  } else {
    Nil
  }
}

///|
/// `(rotatef (aref a m) (aref a n))`
fn sparsemat__swap(a : Value, m : Int, n : Int) -> Unit raise {
  let x = aref1(a, m)
  aset1(a, m, aref1(a, n)) |> ignore
  aset1(a, n, x) |> ignore
}

///|
/// CL `(gcd a b)`.
fn sparsemat__gcd(a : Value, b : Value) -> Value raise {
  num_gcd(a, b)
}

///|
/// A Lisp call of a function Maxima does not define (the affine sources
/// refer to some Lisp Machine functions): signals CL's undefined-function
/// error unless something defines it.
fn sparsemat__call_undefined(name : Value, args : Array[Value]) -> Value raise {
  funcall(name, args)
}

///|
/// SPECIAL-TIMES (and the WITH-CHARACTERISTIC body substitution): product
/// of ARGS in the arithmetic of the entries of SP-MAT.
fn sparsemat__times(sp_mat : Value, args : Array[Value]) -> Value raise {
  if equal(sparsemat__type_of_entries(sp_mat), q_kw_any_macsyma) {
    sp_mul_star(list(args))
  } else if zerop(sparsemat__characteristic(sp_mat)) {
    let mut p : Value = Fix(1L)
    for a in args {
      p = num_mul(p, a)
    }
    p
  } else {
    let mut p : Value = Fix(1L)
    for a in args {
      p = num_mul(p, a)
    }
    num_mod(p, sparsemat__characteristic(sp_mat))
  }
}

///|
/// SPECIAL-PLUS.
fn sparsemat__plus(sp_mat : Value, args : Array[Value]) -> Value raise {
  if eq(sparsemat__type_of_entries(sp_mat), q_kw_any_macsyma) {
    sp_add_star(list(args))
  } else if zerop(sparsemat__characteristic(sp_mat)) {
    let mut s : Value = Fix(0L)
    for a in args {
      s = num_add(s, a)
    }
    s
  } else {
    let mut s : Value = Fix(0L)
    for a in args {
      s = num_add(s, a)
    }
    num_mod(s, sparsemat__characteristic(sp_mat))
  }
}

///|
/// SPECIAL-MINUS: `(special-times -1 a)`.
fn sparsemat__minus(sp_mat : Value, a : Value) -> Value raise {
  sparsemat__times(sp_mat, [Fix(-1L), a])
}

///|
/// SPECIAL-INVERSE.
fn sparsemat__inverse(sp_mat : Value, x : Value) -> Value raise {
  if equal(sparsemat__type_of_entries(sp_mat), q_kw_any_macsyma) {
    sp_div_star(Fix(1L), x)
  } else if numberp(sparsemat__type_of_entries(sp_mat)) {
    with_special(q_modulus, sparsemat__type_of_entries(sp_mat), () => crecip(x))
  } else {
    // (sp-rational-quotient 1 x), sp-rational-quotient being CL /.
    num_div(Fix(1L), x)
  }
}

///|
/// `(format t ctl args...)` for the many diagnostic messages.
fn sparsemat__say(ctl : String, args : Array[Value]) -> Unit raise {
  format(t, ctl, args) |> ignore
}

///|
/// `(fmat t ctl args...)`
fn sparsemat__fmat(ctl : String, args : Array[Value]) -> Unit raise {
  fmat(cons(t, cons(Str(ctl), list(args)))) |> ignore
}

///|
/// `(make-array n :fill-pointer 0 :adjustable t)`
fn sparsemat__make_row(n : Int) -> Value {
  make_array([n], initial=Fix(0L), fill=0)
}

// ---------------------------------------------------------------------
// The macros of sparsemat.lisp, as functions.  SPECIAL-TIMES and friends
// refer to a lexical variable SP-MAT of their caller; called as functions
// they use the sparse matrix in *SPARSE-MATRIX* instead.  The translated
// call sites in this file use the sparsemat__ helpers with an explicit
// matrix.

///|
/// `(row-length arow)` = `(array-dimension-n 1 arow)`; ARRAY-DIMENSION-N
/// is a Lisp Machine function that Maxima does not define.
fn row_length(arow : Value) -> Value raise {
  sparsemat__call_undefined(q_array_dimension_n, [Fix(1L), arow])
}

///|
/// ARRAY-PUSH-EXTEND-REPLACE: like vector-push-extend.
fn array_push_extend_replace(
  aarray : Value,
  data : Value,
  amount_to_grow? : Value = Nil,
  replace? : Value = Nil,
) -> Value raise {
  ignore(replace)
  let r = sparsemat__vector_push(data, aarray)
  if r.truthy() {
    r
  } else {
    let grow = if amount_to_grow.truthy() {
      to_int(amount_to_grow)
    } else {
      100
    }
    let new = adjust_array(
      aarray,
      [grow + array_total_size(aarray)],
      initial=Fix(0L),
    )
    sparsemat__vector_push(data, new)
  }
}

///|
/// `(sp-number-of-rows self)` = `(fill-pointer (sp-rows self))`.
fn sp_number_of_rows(self_ : Value) -> Value raise {
  int(sparsemat__nrows(self_))
}

///|
/// FINITE-CHARACTERISTIC-TIMES: `(mod (* l...) .characteristic.)`; the
/// characteristic is taken from *SPARSE-MATRIX*.
fn finite_characteristic_times(l : Value) -> Value raise {
  let mut p : Value = Fix(1L)
  for a in l.iter() {
    p = num_mul(p, a)
  }
  num_mod(p, sparsemat__characteristic(symval(q_ear_sparse_matrix)))
}

///|
/// FINITE-CHARACTERISTIC-PLUS (see FINITE-CHARACTERISTIC-TIMES).
fn finite_characteristic_plus(l : Value) -> Value raise {
  let mut s : Value = Fix(0L)
  for a in l.iter() {
    s = num_add(s, a)
  }
  num_mod(s, sparsemat__characteristic(symval(q_ear_sparse_matrix)))
}

///|
fn special_minus(a : Value) -> Value raise {
  sparsemat__minus(symval(q_ear_sparse_matrix), a)
}

///|
fn special_times(l : Value) -> Value raise {
  sparsemat__times(symval(q_ear_sparse_matrix), list_to_array(l))
}

///|
fn special_plus(l : Value) -> Value raise {
  sparsemat__plus(symval(q_ear_sparse_matrix), list_to_array(l))
}

///|
/// NON-NEGATIVE-REMAINDER: the macro also stores (rem x y) into the place
/// X; as a function only the value is returned.
fn non_negative_remainder(x : Value, y : Value) -> Value raise {
  let x = num_rem(x, y)
  if minusp(x) {
    num_add(x, y)
  } else {
    x
  }
}

///|
/// `(below-fill a)`
fn below_fill(a : Value) -> Value raise {
  int(if length(a) - 2 > 0 { length(a) - 2 } else { 0 })
}

///|
/// `(sp-row sp-mat i)` = `(aref (sp-rows sp-mat) i)`.
fn sp_row(sp_mat : Value, i : Value) -> Value raise {
  sparsemat__row(sp_mat, i)
}

///|
/// ROW-SLOT: the slot that the INDEX (column) appears in ROW.
fn row_slot(row : Value, index : Value) -> Value raise {
  let n = length(row)
  for ii = 0; ii < n; ii = ii + 2 {
    if eql(index, aref1(row, ii)) {
      return int(ii)
    }
  }
  Nil
}

///|
/// SET-CURRENT-ROW-ENTRY-IN-NEW-COLUMN: puts a new entry in a column not
/// occurring in ROW.
fn set_current_row_entry_in_new_column(
  value : Value,
  row : Value,
  index : Value,
) -> Value raise {
  let val = value
  let ind = index
  if d_zerop(val).truthy() {
    Nil
  } else {
    let n = length(row)
    for ii = 0; ii < n; ii = ii + 2 {
      if aref1(row, ii) is Nil {
        aset1(row, ii, ind) |> ignore
        aset1(row, ii + 1, val) |> ignore
        return q_entry_is_set
      }
    }
    array_push_extend_replace(row, ind) |> ignore
    array_push_extend_replace(row, val) |> ignore
    Nil
  }
}

///|
/// SHOW-ROW: prints the occupied slots of AROW.
fn show_row(arow : Value) -> Value raise {
  let this_row = arow
  let n = length(this_row)
  for jj = 0; jj < n; jj = jj + 2 {
    let ind = aref1(this_row, jj)
    if ind.truthy() {
      sparsemat__say("~%In slot ~D ~D-->~D ", [
        int(jj / 2),
        ind,
        aref1(this_row, jj + 1),
      ])
    }
  }
  Nil
}

///|
/// SPECIAL-INVERSE (see SPECIAL-TIMES).
fn special_inverse(x : Value) -> Value raise {
  sparsemat__inverse(symval(q_ear_sparse_matrix), x)
}

///|
fn null_to_zero(x : Value) -> Value raise {
  if x is Nil {
    Fix(0L)
  } else {
    x
  }
}

///|
/// DSEND: `(progn (send object . body) (send object :show-matrix))`; SEND
/// (flavors) is not defined in Maxima.
fn dsend(object_ : Value, body : Value) -> Value raise {
  sparsemat__call_undefined(q_send, list_to_array(cons(object_, body))) |> ignore
  sparsemat__call_undefined(q_send, [object_, sparsemat__q_show_matrix])
}

///|
let sparsemat__q_show_matrix : Value = sym(":show-matrix")

///|
/// MAY-HAVE-PIVOT (see SPECIAL-TIMES).
fn may_have_pivot(row_number : Value) -> Value raise {
  sparsemat__may_have_pivot(symval(q_ear_sparse_matrix), row_number)
}

///|
fn sparsemat__may_have_pivot(sp_mat : Value, row_number : Value) -> Value raise {
  lbool(
    !eql(
      Fix(1L),
      aref1(sparsemat__rows_with_no_pivot(sp_mat), to_int(row_number)),
    ),
  )
}

///|
/// SWAP-ROWS-AND-CONSTANTS (see SPECIAL-TIMES).
fn swap_rows_and_constants(m : Value, n : Value) -> Value raise {
  sparsemat__swap_rows_and_constants(symval(q_ear_sparse_matrix), m, n)
}

///|
fn sparsemat__swap_rows_and_constants(
  sp_mat : Value,
  m : Value,
  n : Value,
) -> Value raise {
  let m = to_int(m)
  let n = to_int(n)
  sparsemat__swap(sparsemat__rows(sp_mat), m, n)
  sparsemat__set_sign_of_row_permutation(
    sp_mat,
    num_neg(sparsemat__sign_of_row_permutation(sp_mat)),
  )
  |> ignore
  let tem = sparsemat__current_column_above_pivot_row_number(sp_mat)
  if tem.truthy() {
    sparsemat__swap(tem, m, n)
  }
  if sparsemat__constants_column(sp_mat).truthy() {
    sparsemat__swap(sparsemat__constants_column(sp_mat), m, n)
  }
  Nil
}

// ---------------------------------------------------------------------
// The functions

///|
fn row_entry(arow : Value, j : Value) -> Value raise {
  let n = length(arow)
  for ii = 0; ii < n; ii = ii + 2 {
    let col = aref1(arow, ii)
    if col.truthy() && eql(j, col) {
      return aref1(arow, ii + 1)
    }
  }
  Nil
}

///|
fn sp_row_dot(sp_mat : Value, arow : Value, brow : Value) -> Value raise {
  let mut ans : Value = Fix(0L)
  let n = length(arow)
  for iii = 0; iii < n; iii = iii + 2 {
    let aindex = aref1(arow, iii)
    if aindex.truthy() {
      let val = row_entry(brow, aindex)
      if val.truthy() {
        ans = sparsemat__plus(sp_mat, [
          ans,
          sparsemat__times(sp_mat, [val, aref1(arow, iii + 1)]),
        ])
      }
    }
  }
  ans
}

///|
fn sp_row_dot_row_numbers(sp_mat : Value, i : Value, j : Value) -> Value raise {
  sp_row_dot(sp_mat, sparsemat__row(sp_mat, i), sparsemat__row(sp_mat, j))
}

///|
fn maybe_move_back_fill_pointer(arow : Value) -> Value raise {
  if length(arow) == 0 {
    Nil
  } else {
    let mut i = to_int(below_fill(arow))
    while i >= 0 {
      if aref1(arow, i).truthy() {
        set_fill_pointer(arow, i + 2)
        return q_done
      }
      i = i - 2
    }
    set_fill_pointer(arow, 0)
    Nil
  }
}

///|
fn sp_reduce_elements_for_type(sp_mat : Value) -> Value raise {
  if fixnump(sparsemat__type_of_entries(sp_mat)) {
    sparsemat__set_characteristic(sp_mat, sparsemat__type_of_entries(sp_mat))
    |> ignore
    let nrows = sparsemat__nrows(sp_mat)
    for iii in 0..<nrows {
      let this_row = aref1(sparsemat__rows(sp_mat), iii)
      let n = length(this_row)
      for ii = 0; ii < n; ii = ii + 2 {
        if aref1(this_row, ii).truthy() {
          let mut value = aref1(this_row, ii + 1)
          if value.truthy() {
            value = num_mod(value, sparsemat__type_of_entries(sp_mat))
            if eql(value, Fix(0L)) {
              aset1(this_row, ii, Nil) |> ignore
            } else {
              aset1(this_row, ii + 1, value) |> ignore
            }
          }
        }
      }
      maybe_move_back_fill_pointer(this_row) |> ignore
    }
  }
  Nil
}

///|
fn sp_reset_list_of_all_columns_occurring(sp_mat : Value) -> Value raise {
  let mut temp : Value = Nil
  let nrows = sparsemat__nrows(sp_mat)
  for ii in 0..<nrows {
    let this_row = aref1(sparsemat__rows(sp_mat), ii)
    let c = Collector::new()
    let n = length(this_row)
    for jj = 0; jj < n; jj = jj + 2 {
      let ind = aref1(this_row, jj)
      if ind.truthy() && !member(ind, temp).truthy() {
        c.add(ind)
      }
    }
    temp = append(temp, c.result())
  }
  sparsemat__set_list_of_all_columns_occurring(sp_mat, temp)
}

///|
fn sp_set_rows(
  sp_mat : Value,
  the_rows : Value,
  list_of_columns? : Value = Nil,
) -> Value raise {
  let rows = match as_array(the_rows).fill {
    Some(_) => the_rows
    None => {
      // (make-array (array-dimension the-rows 0) :adjustable t
      //   :displaced-to the-rows :fill-pointer t)
      let a = as_array(the_rows)
      let d = array_dimension(the_rows, 0)
      Vec({ data: a.data, dims: [d], fill: Some(d), elt: a.elt })
    }
  }
  sparsemat__set_rows(sp_mat, rows) |> ignore
  // (setf (sp-number-of-rows sp-mat) (fill-pointer (sp-rows sp-mat))):
  // SP-NUMBER-OF-ROWS is the fill pointer itself, so this changes nothing.
  sparsemat__set_last_good_row(sp_mat, int(sparsemat__nrows(sp_mat) - 1))
  |> ignore
  if list_of_columns is Nil {
    sp_reset_list_of_all_columns_occurring(sp_mat) |> ignore
  } else {
    sparsemat__set_list_of_all_columns_occurring(sp_mat, list_of_columns)
    |> ignore
  }
  let n = sparsemat__nrows(sp_mat)
  sparsemat__set_column_used_in_row(sp_mat, make_array([n], initial=Fix(0L)))
  |> ignore
  sparsemat__set_rows_with_no_pivot(sp_mat, make_array([n], elt="bit"))
  |> ignore
  sp_check_set_up(sp_mat) |> ignore
  let cutp = sparsemat__columns_used_to_pivot(sp_mat)
  if cutp.truthy() && hash_table_p(cutp) {
    clrhash(cutp)
  } else {
    sparsemat__set_columns_used_to_pivot(sp_mat, make_hash_table())
  }
}

///|
fn ml_sort(lis : Value, predicate? : Value) -> Value raise {
  match predicate {
    None => sort_list(lis, (a, b) => alphalessp(a, b).truthy())
    Some(p) => sort_list(lis, (a, b) => funcall(p, [a, b]).truthy())
  }
}

///|
fn sp_check_set_up(sp_mat : Value) -> Value raise {
  sparsemat__set_current_row(sp_mat, Nil) |> ignore
  sparsemat__set_reduced(sp_mat, Nil) |> ignore
  sparsemat__set_last_good_row(sp_mat, int(sparsemat__nrows(sp_mat))) |> ignore
  sparsemat__set_current_column_above_pivot_row_number(sp_mat, Nil) |> ignore
  let tem = sparsemat__columns_used_to_pivot(sp_mat)
  if tem.truthy() {
    clrhash(tem) |> ignore
  } else {
    sparsemat__set_columns_used_to_pivot(sp_mat, make_hash_table()) |> ignore
  }
  sparsemat__set_columns_with_no_pivot(sp_mat, Nil) |> ignore
  Nil
}

///|
fn sp_set_current_row(sp_mat : Value, i : Value) -> Value raise {
  sparsemat__set_current_row_number(sp_mat, i) |> ignore
  sparsemat__set_current_row(sp_mat, sparsemat__row(sp_mat, i)) |> ignore
  sparsemat__set_current_row_length(
    sp_mat,
    int(length(sparsemat__current_row(sp_mat))),
  )
  |> ignore
  sparsemat__current_row(sp_mat)
}

///|
fn sp_set_pivot_row(sp_mat : Value, i : Value) -> Value raise {
  sparsemat__set_pivot_row_number(sp_mat, i) |> ignore
  sparsemat__set_pivot_row(sp_mat, sparsemat__row(sp_mat, i)) |> ignore
  sparsemat__pivot_row(sp_mat)
}

///|
fn sp_entry(sp_mat : Value, i : Value, j : Value) -> Value raise {
  let this_row = sparsemat__row(sp_mat, i)
  let n = length(this_row)
  for ii = 0; ii < n; ii = ii + 2 {
    if eql(j, aref1(this_row, ii)) {
      return aref1(this_row, ii + 1)
    }
  }
  Nil
}

///|
fn fix_even(n : Value) -> Value raise {
  num_mul(Fix(2L), num_round(quot(n, Flo(2.0))).0)
}

///|
/// ARRAY-GROW is a Lisp Machine function that Maxima does not define.
fn sp_grow_current_row(sp_mat : Value, ratio? : Value = Flo(1.3)) -> Value raise {
  let new_length = num_max(
    fix_even(
      num_mul(
        ratio,
        row_length(
          sparsemat__row(sp_mat, sparsemat__current_row_number(sp_mat)),
        ),
      ),
    ),
    sparsemat__minimum_size_to_grow(sp_mat),
  )
  aset1(
    sparsemat__rows(sp_mat),
    to_int(sparsemat__current_row_number(sp_mat)),
    sparsemat__call_undefined(sparsemat__q_array_grow, [
      sparsemat__current_row(sp_mat),
      new_length,
    ]),
  )
  |> ignore
  sp_set_current_row(sp_mat, sparsemat__current_row_number(sp_mat))
}

///|
fn sp_grow_row(
  sp_mat : Value,
  row_number : Value,
  ratio? : Value = Flo(1.3),
) -> Value raise {
  let new_length = num_max(
    fix_even(num_mul(ratio, row_length(sparsemat__row(sp_mat, row_number)))),
    sparsemat__minimum_size_to_grow(sp_mat),
  )
  aset1(
    sparsemat__rows(sp_mat),
    to_int(row_number),
    sparsemat__call_undefined(sparsemat__q_array_grow, [
      sparsemat__row(sp_mat, row_number),
      new_length,
    ]),
  )
}

///|
/// Note: when VALUE is zero the Lisp clears `(aref arow index)`, using the
/// column number as a slot index; this is kept.
fn set_entry(value : Value, arow : Value, index : Value) -> Value raise {
  let aarow = arow
  let active_length = fill_pointer(arow)
  let mut first_empty_slot : Int? = None
  let limit = fill_pointer(aarow)
  for ii = 0; ii < limit; ii = ii + 2 {
    let j = aref1(aarow, ii)
    if j is Nil {
      first_empty_slot = Some(ii)
      break
    } else if eql(j, index) {
      if d_zerop(value).truthy() {
        aset1(aarow, to_int(index), Nil) |> ignore
        if ii == active_length - 2 {
          maybe_move_back_fill_pointer(aarow) |> ignore
        }
      } else {
        aset1(aarow, ii + 1, value) |> ignore
        aset1(aarow, ii, index) |> ignore
      }
      return t
    }
  }
  match first_empty_slot {
    Some(fes) => {
      for ii = fes; ii < active_length; ii = ii + 2 {
        if eql(index, aref1(aarow, ii)) {
          if d_zerop(value).truthy() {
            aset1(aarow, to_int(index), Nil) |> ignore
            if ii == active_length - 2 {
              maybe_move_back_fill_pointer(aarow) |> ignore
            }
          } else {
            aset1(aarow, ii + 1, value) |> ignore
            aset1(aarow, ii, index) |> ignore
          }
          return t
        }
      }
      if !d_zerop(value).truthy() {
        aset1(aarow, fes + 1, value) |> ignore
        aset1(aarow, fes, index) |> ignore
      }
      Nil
    }
    None =>
      if !d_zerop(value).truthy() {
        vector_push_extend(index, aarow) |> ignore
        int(vector_push_extend(value, aarow))
      } else {
        Nil
      }
  }
}

///|
fn sp_set_current_row_entry(
  sp_mat : Value,
  value : Value,
  ind : Value,
) -> Value raise {
  set_entry(value, sparsemat__current_row(sp_mat), ind)
}

///|
fn sp_set_entry(sp_mat : Value, value : Value, i : Value, j : Value) -> Value raise {
  set_entry(value, sparsemat__row(sp_mat, i), j)
}

///|
/// This replaces the current-row by current-row + factor pivot-row.
fn sp_row_operation(sp_mat : Value, factor : Value) -> Value raise {
  // WITH-ONCE-ONLY caches the pivot row and current row in locals and
  // stores them back at the end; the row vectors keep their identity, so
  // reading the slots directly is equivalent.
  let pivot_row = sparsemat__pivot_row(sp_mat)
  let current_row = sparsemat__current_row(sp_mat)
  if !equal(factor, Fix(0L)) {
    let n = length(pivot_row)
    for ii = 0; ii < n; ii = ii + 2 {
      let piv_col = aref1(pivot_row, ii)
      if piv_col.truthy() {
        let current_row_slot = row_slot(current_row, piv_col)
        if current_row_slot.truthy() {
          let crs = to_int(current_row_slot)
          let new_value = sparsemat__plus(sp_mat, [
            sparsemat__times(sp_mat, [factor, aref1(pivot_row, ii + 1)]),
            aref1(current_row, crs + 1),
          ])
          if d_zerop(new_value).truthy() {
            aset1(current_row, crs, Nil) |> ignore
          } else {
            aset1(current_row, crs + 1, new_value) |> ignore
          }
        } else {
          set_current_row_entry_in_new_column(
            sparsemat__times(sp_mat, [factor, aref1(pivot_row, ii + 1)]),
            current_row,
            piv_col,
          )
          |> ignore
        }
      }
    }
    maybe_move_back_fill_pointer(current_row) |> ignore
  }
  sparsemat__set_pivot_row(sp_mat, pivot_row) |> ignore
  sparsemat__set_current_row(sp_mat, current_row) |> ignore
  let cc = sparsemat__constants_column(sp_mat)
  if cc.truthy() {
    let temp = aref1(cc, to_int(sparsemat__pivot_row_number(sp_mat)))
    if !d_zerop(temp).truthy() {
      let crn = to_int(sparsemat__current_row_number(sp_mat))
      return aset1(
        cc,
        crn,
        sparsemat__plus(sp_mat, [
          aref1(cc, crn),
          sparsemat__times(sp_mat, [factor, temp]),
        ]),
      )
    }
  }
  Nil
}

///|
fn get_rows_from_array(matrix : Value) -> Value raise {
  let dims = array_dimensions(matrix)
  let d0 = to_int(car(dims))
  let d1 = to_int(cadr(dims))
  let the_rows = make_array([d0], initial=Fix(0L), fill=d0)
  for i in 0..<d0 {
    let arow = sparsemat__make_row(d1 * 2)
    aset1(the_rows, i, arow) |> ignore
    for j in 0..<d1 {
      let entry = aref(matrix, [i, j])
      if !equal(entry, Fix(0L)) {
        sparsemat__vector_push(int(j), arow) |> ignore
        sparsemat__vector_push(entry, arow) |> ignore
      }
    }
  }
  the_rows
}

///|
fn random_matrix(m : Value, n : Value, random_size? : Value = Fix(5L)) -> Value raise {
  let m = to_int(m)
  let n = to_int(n)
  let mat = make_array([m, n], initial=Fix(0L))
  for i in 0..<m {
    for j in 0..<n {
      aset(mat, [i, j], mt_random(random_size)) |> ignore
    }
  }
  mat
}

///|
fn sp_gcd_row(sp_mat : Value, i : Value) -> Value raise {
  let mut ans = sp_first_element_of_row(sp_mat, i)
  let this_row = sparsemat__row(sp_mat, i)
  let n = length(this_row)
  for ii = 0; ii < n; ii = ii + 2 {
    if aref1(this_row, ii).truthy() {
      ans = sparsemat__gcd(ans, aref1(this_row, ii + 1))
    }
  }
  ans
}

///|
fn sp_first_element_of_row(sp_mat : Value, ii : Value) -> Value raise {
  let this_row = sparsemat__row(sp_mat, ii)
  let n = length(this_row)
  for i = 0; i < n; i = i + 2 {
    if aref1(this_row, i).truthy() {
      return aref1(this_row, i + 1)
    }
  }
  Nil
}

///|
fn sp_show_row(sp_mat : Value, i : Value) -> Value raise {
  let this_row = sparsemat__row(sp_mat, i)
  sparsemat__say("~%Row ~D is ~A.", [i, this_row])
  show_row(this_row)
}

///|
fn sp_show_current_and_pivot(sp_mat : Value) -> Value raise {
  let crn = sparsemat__current_row_number(sp_mat)
  sparsemat__say("~%Current row is ~D which is ~A.", [
    crn,
    sparsemat__current_row(sp_mat),
  ])
  show_row(sparsemat__current_row(sp_mat)) |> ignore
  sparsemat__say("~%Pivot Row is ~D which is ~A.", [
    sparsemat__pivot_row_number(sp_mat),
    sparsemat__pivot_row(sp_mat),
  ])
  show_row(sparsemat__pivot_row(sp_mat))
}

///|
fn sp_rat(x : Value) -> Value raise {
  if affine_polynomialp(x).truthy() || rational_functionp(x).truthy() {
    x
  } else if d_bfloatp(x).truthy() {
    x
  } else {
    new_rat(x)
  }
}

///|
fn sp_choose_type_of_entries(sp_mat : Value) -> Value raise {
  let mut rational = false
  let mut float = false
  let rows = sparsemat__rows(sp_mat)
  let nr = length(rows)
  for i in 0..<nr {
    let a_row = aref1(rows, i)
    let n = length(a_row)
    for ii = 0; ii < n; ii = ii + 2 {
      if aref1(a_row, ii).truthy() {
        let tem1 = aref1(a_row, ii + 1)
        if numberp(tem1) {
          if float || floatp(tem1) {
            float = true
          } else if rationalp(tem1) {
            rational = true
          }
        } else {
          sp_set_type_of_entries(sp_mat, q_kw_any_macsyma) |> ignore
          return q_done
        }
      }
    }
  }
  // if any floating use float else if any rational use rational
  // else use integer
  if float {
    sp_set_type_of_entries(sp_mat, q_kw_float)
  } else if rational {
    sp_set_type_of_entries(sp_mat, q_kw_rational)
  } else {
    sp_set_type_of_entries(sp_mat, q_kw_integer)
  }
}

///|
let sparsemat__unit_gcd_column : Value = list([q_unit, q_gcd_column])

///|
let sparsemat__unit_any : Value = list([q_unit, q_any])

///|
let sparsemat__any : Value = list([q_any])

///|
let sparsemat__any_macsyma : Value = list([q_kw_any_macsyma])

///|
fn sparsemat__modulus_or_0() -> Value {
  let m = symval(q_modulus)
  if m.truthy() {
    m
  } else {
    Fix(0L)
  }
}

///|
fn sp_set_type_of_entries(sp_mat : Value, y : Value) -> Value raise {
  sparsemat__set_type_of_entries(sp_mat, y) |> ignore
  if equal(y, q_kw_integer) {
    sparsemat__set_characteristic(sp_mat, sparsemat__modulus_or_0()) |> ignore
    sparsemat__set_pivot_test_list(sp_mat, sparsemat__unit_gcd_column)
  } else if equal(y, q_kw_rational) {
    // any is bad do gcd of col etc.
    if symval(q_modulus).truthy() {
      sparsemat__set_characteristic(sp_mat, symval(q_modulus)) |> ignore
      sparsemat__set_type_of_entries(sp_mat, symval(q_modulus))
    } else {
      sparsemat__set_pivot_test_list(sp_mat, sparsemat__unit_any) |> ignore // removed gcd
      sparsemat__set_characteristic(sp_mat, Fix(0L))
    }
  } else if equal(y, q_kw_float) {
    sparsemat__set_pivot_test_list(sp_mat, sparsemat__any) |> ignore
    sparsemat__set_characteristic(sp_mat, sparsemat__modulus_or_0())
  } else if equal(y, q_kw_any_macsyma) {
    sparsemat__set_pivot_test_list(sp_mat, sparsemat__any_macsyma) |> ignore
    sparsemat__set_characteristic(sp_mat, sparsemat__modulus_or_0()) |> ignore
    let rows = sparsemat__rows(sp_mat)
    let nt = array_total_size(rows)
    for i in 0..<nt {
      let this_row = aref1(rows, i)
      let n = array_total_size(this_row)
      for j = 0; j < n; j = j + 2 {
        if aref1(this_row, j).truthy() {
          aset1(this_row, j + 1, sp_rat(aref1(this_row, j + 1))) |> ignore
        }
      }
    }
    Nil
  } else if fixnump(y) && num_gt(y, Fix(0L)) {
    sparsemat__set_characteristic(sp_mat, y)
  } else {
    merr(
      "At present only positive integers (ie finite char)\n\t\t\t    ,integer, rational, or':any-macsyma are valid types",
      [],
    )
  }
}

///|
fn sp_enter_pivot_data(sp_mat : Value, col : Value) -> Value raise {
  sethash(
    col,
    sparsemat__columns_used_to_pivot(sp_mat),
    sparsemat__pivot_row_number(sp_mat),
  )
  |> ignore
  aset1(
    sparsemat__column_used_in_row(sp_mat),
    to_int(sparsemat__pivot_row_number(sp_mat)),
    col,
  )
  |> ignore
  fmat(
    list([
      t,
      Str("Row ~D has pivot ~D in column ~D."),
      sparsemat__pivot_row_number(sp_mat),
      sparsemat__pivot_entry(sp_mat),
      col,
    ]),
  )
}

///|
/// Note: the Lisp clears `(aref this-row ii 0)`, a two-index reference to
/// a vector, which signals an error when an entry is NIL; kept.
fn sp_remove_zero_entries_from_row(sp_mat : Value, i : Value) -> Value raise {
  let this_row = sparsemat__row(sp_mat, i)
  let n = length(this_row)
  for ii = 0; ii < n; ii = ii + 2 {
    if aref1(this_row, ii).truthy() {
      if aref1(this_row, ii + 1) is Nil {
        aset(this_row, [ii, 0], Nil) |> ignore
      }
    }
  }
  maybe_move_back_fill_pointer(this_row)
}

///|
fn show_hash(tabl : Value) -> Value raise {
  maphash((x, y) => sparsemat__say("~%~A -->~A", [x, y]), tabl)
  Nil
}

///|
fn sp_show_rows(sp_mat : Value, l : Value) -> Value raise {
  let mut l = l
  if l is Nil {
    let c = Collector::new()
    for i in 0..<sparsemat__nrows(sp_mat) {
      c.add(int(i))
    }
    l = c.result()
  }
  for i in l.iter() {
    sp_show_row(sp_mat, i) |> ignore
  }
  sparsemat__say("~%Current row is row ~D.", [
    sparsemat__current_row_number(sp_mat),
  ])
  sparsemat__say("~%Pivot row is row ~D.", [sparsemat__pivot_row_number(sp_mat)])
  Nil
}

///|
fn sparsemat__pivot_pred(pred : Value) -> (Value) -> Bool raise {
  if pred is Nil {
    _ => true
  } else if equal(pred, sparsemat__q_kw_non_unit) {
    x => !eql(num_abs(x), Fix(1L))
  } else {
    x => funcall(pred, [x]).truthy()
  }
}

///|
fn sp_list_pivots(sp_mat : Value, pred? : Value = Nil) -> Value raise {
  let pred = sparsemat__pivot_pred(pred)
  let c = Collector::new()
  for i in 0..<sparsemat__nrows(sp_mat) {
    let col = aref1(sparsemat__column_used_in_row(sp_mat), i)
    if col.truthy() {
      let entry = sp_entry(sp_mat, int(i), col)
      if pred(entry) {
        c.add(entry)
      }
    }
  }
  c.result()
}

///|
fn sp_show_pivots(sp_mat : Value, pred? : Value = Nil) -> Value raise {
  let pred = sparsemat__pivot_pred(pred)
  for i in 0..<sparsemat__nrows(sp_mat) {
    let col = aref1(sparsemat__column_used_in_row(sp_mat), i)
    if col.truthy() {
      let entry = sp_entry(sp_mat, int(i), col)
      if pred(entry) {
        sparsemat__say("~%Row ~D has pivot ~D in column ~D.", [
          int(i),
          entry,
          col,
        ])
      }
    }
  }
  Nil
}

///|
fn sp_show_matrix(sp_mat : Value) -> Value raise {
  if !sparsemat__list_of_all_columns_occurring(sp_mat).truthy() {
    sparsemat__set_list_of_all_columns_occurring(
      sp_mat,
      sort_list(sparsemat__list_of_all_columns_occurring(sp_mat), (a, b) => num_lt(
        a, b,
      )),
    )
    |> ignore
  }
  sparsemat__say("~%       ", [])
  for i in sparsemat__list_of_all_columns_occurring(sp_mat).iter() {
    sparsemat__say("C~D   ", [i])
  }
  if sparsemat__constants_column(sp_mat).truthy() {
    sparsemat__say("Const~D", [sparsemat__constants_column_number(sp_mat)])
  }
  for i in 0..<sparsemat__nrows(sp_mat) {
    sparsemat__say("~%R~2D ", [int(i)])
    for j in sparsemat__list_of_all_columns_occurring(sp_mat).iter() {
      sparsemat__say("~5D", [null_to_zero(sp_entry(sp_mat, int(i), j))])
    }
    if sparsemat__constants_column(sp_mat).truthy() {
      sparsemat__say("~5D", [aref1(sparsemat__constants_column(sp_mat), i)])
    }
  }
  if sparsemat__special_solution(sp_mat).truthy() {
    sparsemat__say("~%SpSol", [])
    for j in sparsemat__list_of_all_columns_occurring(sp_mat).iter() {
      sparsemat__say("~5D", [
        null_to_zero(row_entry(sparsemat__special_solution(sp_mat), j)),
      ])
    }
  }
  Nil
}

///|
fn sp_reduce(sp_mat : Value, type_of_entry? : Value = Nil) -> Value raise {
  let original_number_of_rows = sparsemat__nrows(sp_mat)
  if type_of_entry.truthy() {
    sp_set_type_of_entries(sp_mat, type_of_entry) |> ignore
  }
  if fixnump(sparsemat__type_of_entries(sp_mat)) {
    sp_reduce_elements_for_type(sp_mat) |> ignore
  }
  sp_clear_pivots(sp_mat) |> ignore
  let mut i = 0
  while i < sparsemat__nrows(sp_mat) {
    sp_set_pivot_row(sp_mat, int(i)) |> ignore
    sp_best_pivot(sp_mat) |> ignore
    if sparsemat__pivot_entry(sp_mat).truthy() {
      let pivoting_column = aref1(
        sparsemat__column_used_in_row(sp_mat),
        to_int(sparsemat__pivot_row_number(sp_mat)),
      )
      let minus_inverse_pivot_entry = sparsemat__minus(
        sp_mat,
        sparsemat__inverse(sp_mat, sparsemat__pivot_entry(sp_mat)),
      )
      let limit = sparsemat__nrows(sp_mat)
      for ii in (i + 1)..<limit {
        sp_set_current_row(sp_mat, int(ii)) |> ignore
        let current_row_entry = sp_entry(sp_mat, int(ii), pivoting_column)
        if current_row_entry.truthy() {
          sp_row_operation(
            sp_mat,
            sparsemat__times(sp_mat, [
              current_row_entry, minus_inverse_pivot_entry,
            ]),
          )
          |> ignore
        }
      }
    }
    i = i + 1
  }
  sp_kill_extra_rows(sp_mat, int(original_number_of_rows)) |> ignore
  sparsemat__set_reduced(sp_mat, t)
}

///|
fn sp_kill_extra_rows(sp_mat : Value, original_number_of_rows : Value) -> Value raise {
  let rows = sparsemat__rows(sp_mat)
  let mut up_bound : Value = Nil
  for i in to_int(original_number_of_rows)..<sparsemat__nrows(sp_mat) {
    if fill_pointer(aref1(rows, i)) != 0 {
      up_bound = int(i + 1)
    }
  }
  if up_bound is Nil {
    up_bound = original_number_of_rows
  }
  set_fill_pointer(rows, to_int(up_bound))
  // (setf (sp-number-of-rows sp-mat) up-bound) sets the same fill pointer.
  set_fill_pointer(sparsemat__rows(sp_mat), to_int(up_bound))
  Nil
}

///|
fn sp_multiply_row(sp_mat : Value, row_number : Value, factor : Value) -> Value raise {
  let this_row = sparsemat__row(sp_mat, row_number)
  if equal(Fix(0L), sparsemat__times(sp_mat, [Fix(1L), factor])) {
    let n = fill_pointer(this_row)
    for i in 0..<n {
      aset1(this_row, i, Nil) |> ignore
      set_fill_pointer(this_row, 0)
    }
    Nil
  } else if equal(Fix(1L), factor) {
    Nil
  } else {
    let n = length(this_row)
    for i = 0; i < n; i = i + 2 {
      if aref1(this_row, i).truthy() {
        aset1(
          this_row,
          i + 1,
          sparsemat__times(sp_mat, [aref1(this_row, i + 1), factor]),
        )
        |> ignore
      }
    }
    Nil
  }
}

///|
fn sp_clear_pivots(sp_mat : Value) -> Value raise {
  clrhash(sparsemat__columns_used_to_pivot(sp_mat)) |> ignore
  fillarray(sparsemat__column_used_in_row(sp_mat), Nil) |> ignore
  fillarray(sparsemat__rows_with_no_pivot(sp_mat), list1(Fix(0L))) |> ignore
  for i in 0..<sparsemat__nrows(sp_mat) {
    aset1(sparsemat__column_used_in_row(sp_mat), i, Nil) |> ignore
  }
  Nil
}

///|
fn sp_get_rows_from_array(
  sp_mat : Value,
  aarray : Value,
  type_? : Value = q_kw_integer,
) -> Value raise {
  sp_set_rows(sp_mat, get_rows_from_array(aarray)) |> ignore
  sp_set_type_of_entries(sp_mat, type_) |> ignore
  sp_check_set_up(sp_mat)
}

///|
fn genmatrix(m : Value, n : Value, fun : Value) -> Value raise {
  let mi = to_int(m)
  let ni = to_int(n)
  let ans = make_array([mi, ni], initial=Fix(0L))
  for i in 0..<mi {
    for j in 0..<ni {
      aset(ans, [i, j], funcall(fun, [int(i), int(j)])) |> ignore
    }
  }
  ans
}

///|
fn macsyma_array_to_row(aarray : Value, grow_ratio? : Value = Fix(1L)) -> Value raise {
  let aarray = symbol_array(mget(aarray, q_hashar))
  let actual_size = aref1(aarray, 1)
  let ans = sparsemat__make_row(
    to_int(
      num_round(num_mul(num_mul(actual_size, Fix(2L)), grow_ratio)).0,
    ),
  )
  let dim = to_int(car(array_dimensions(aarray)))
  for i in 3..<dim {
    let val = aref1(aarray, i)
    if val.truthy() {
      for u in val.iter() {
        array_push_extend_replace(ans, caar(u)) |> ignore
        array_push_extend_replace(ans, cdr(u)) |> ignore
      }
    }
  }
  let index = num_div(int(fill_pointer(ans)), Fix(2L))
  if !equal(index, actual_size) {
    sparsemat__say(
      "We only found ~D elements while\n\t\t\t      there should have been ~D elements.",
      [index, actual_size],
    )
  }
  ans
}

///|
fn list_of_macsyma_arrays_to_rows(llist : Value) -> Value raise {
  let size = length(cdr(llist))
  let rows = make_array([size], initial=Fix(0L), fill=0)
  for u in cdr(llist).iter() {
    vector_push_extend(funcall(q_macsyma_array_to_row, [u]), rows) |> ignore
  }
  rows
}

///|
fn sp_number_of_pivots(sp_mat : Value, below_row? : Value) -> Value raise {
  let below_row = match below_row {
    Some(b) => to_int(b)
    None => sparsemat__nrows(sp_mat)
  }
  let mut count = 0
  for i in 0..<below_row {
    if aref1(sparsemat__column_used_in_row(sp_mat), i).truthy() {
      count = count + 1
    }
  }
  int(count)
}

///|
let sparsemat__q_array_grow : Value = sym("array-grow")

///|
let sparsemat__q_kw_non_unit : Value = sym(":non-unit")

///|
let sparsemat__q_sort_grouped_array : Value = sym("sort-grouped-array")

///|
let sparsemat__q_kw_solutions : Value = sym(":solutions")

///|
let sparsemat__q_kw_columns_used_to_pivot : Value = sym(":columns-used-to-pivot")

///|
let sparsemat__q_general_gcd : Value = sym("general-gcd")

///|
let sparsemat__q_list_array_leader : Value = sym("list-array-leader")

///|
let sparsemat__q_make_sparse_solution : Value = sym("make-sparse-solution")

///|
let sparsemat__q_sparse_solution_row : Value = sym("sparse-solution-row")

///|
let sparsemat__q_best : Value = sym("best")
