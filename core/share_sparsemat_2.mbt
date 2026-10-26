// Translation of share/affine/sparsemat.lisp (part 2): solving, pivoting,
// determinants.

///|
fn sp_solve(
  sp_mat : Value,
  reduce_? : Value = Nil,
  reset_list_of_columns_occurring? : Value = Nil,
) -> Value raise {
  if reset_list_of_columns_occurring.truthy() {
    sp_reset_list_of_all_columns_occurring(sp_mat) |> ignore
  }
  if reduce_.truthy() || sparsemat__reduced(sp_mat) is Nil {
    sp_clear_pivots(sp_mat) |> ignore
    sp_reduce(sp_mat) |> ignore
  }
  let cnp = Collector::new()
  for u in sparsemat__list_of_all_columns_occurring(sp_mat).iter() {
    if gethash(u, sparsemat__columns_used_to_pivot(sp_mat)) is Nil {
      cnp.add(u)
    }
  }
  sparsemat__set_columns_with_no_pivot(sp_mat, cnp.result()) |> ignore
  let number_of_columns = length(
    sparsemat__list_of_all_columns_occurring(sp_mat),
  )
  let number_of_pivots = to_int(sp_number_of_pivots(sp_mat))
  let number_of_solutions = number_of_columns - number_of_pivots
  let mut a_special_solution : Value = Nil
  let solution_rows = make_array(
    [length(sparsemat__columns_with_no_pivot(sp_mat))],
    initial=Fix(0L),
    fill=0,
  )
  if length(sparsemat__columns_with_no_pivot(sp_mat)) != number_of_solutions {
    sparsemat__say(
      "~%There are ~D columns and ~D pivots and ~D columns with no pivot,\nsomething is wrong",
      [
        int(length(sparsemat__list_of_all_columns_occurring(sp_mat))),
        int(number_of_pivots),
        int(length(sparsemat__columns_with_no_pivot(sp_mat))),
      ],
    )
  }
  if number_of_solutions > 0 {
    for u in sparsemat__columns_with_no_pivot(sp_mat).iter() {
      let a_solution = sparsemat__make_row((1 + number_of_pivots) * 2)
      sparsemat__vector_push(a_solution, solution_rows) |> ignore
      sparsemat__fmat("~%solution-rows ~A", [listarray(solution_rows)])
      set_entry(Fix(1L), a_solution, u) |> ignore
      let mut nn = fill_pointer(sparsemat__rows(sp_mat)) - 1
      while nn >= 0 {
        if aref1(sparsemat__column_used_in_row(sp_mat), nn).truthy() {
          sparsemat__set_pivot_entry(
            sp_mat,
            sp_entry(
              sp_mat,
              int(nn),
              aref1(sparsemat__column_used_in_row(sp_mat), nn),
            ),
          )
          |> ignore
          let a_new_entry = sparsemat__times(sp_mat, [
            Fix(-1L),
            sparsemat__inverse(sp_mat, sparsemat__pivot_entry(sp_mat)),
            sp_row_dot(sp_mat, a_solution, aref1(sparsemat__rows(sp_mat), nn)),
          ])
          if !d_zerop(a_new_entry).truthy() {
            sparsemat__vector_push(
              aref1(sparsemat__column_used_in_row(sp_mat), nn),
              a_solution,
            )
            |> ignore
            sparsemat__vector_push(a_new_entry, a_solution) |> ignore
          }
        }
        nn = nn - 1
      }
    }
  }
  let cc = sparsemat__constants_column(sp_mat)
  if cc.truthy() {
    let ncu = array_total_size(sparsemat__column_used_in_row(sp_mat))
    for i in 0..<ncu {
      if aref1(sparsemat__column_used_in_row(sp_mat), i) is Nil {
        if !d_zerop(aref1(sparsemat__constants_column(sp_mat), i)).truthy() {
          sparsemat__say("~%~%  ******************************~%", [])
          sparsemat__say(
            "~%Row ~D has no pivot but the (sp-constants-column sp-mat) has entry ~D.\n\t\t   ~%Warning: The equations were INCONSISTENT.\n\t\t   ~%The special-solution is NOT VALID.\n\t\t   ~%  ******************************",
            [int(i), aref1(sparsemat__constants_column(sp_mat), i)],
          )
        }
      }
    }
    // (show (sp-type-of-entries sp-mat))
    sparsemat__say("~%The value of ~A is ~A", [
      Str("(SP-TYPE-OF-ENTRIES SP-MAT)"),
      sparsemat__type_of_entries(sp_mat),
    ])
    a_special_solution = sparsemat__make_row((1 + number_of_pivots) * 2)
    let mut nn = fill_pointer(sparsemat__rows(sp_mat)) - 1
    while nn >= 0 {
      if aref1(sparsemat__column_used_in_row(sp_mat), nn).truthy() {
        sparsemat__set_pivot_entry(
          sp_mat,
          sp_entry(
            sp_mat,
            int(nn),
            aref1(sparsemat__column_used_in_row(sp_mat), nn),
          ),
        )
        |> ignore
        let a_new_entry = sparsemat__times(sp_mat, [
          Fix(-1L),
          sparsemat__inverse(sp_mat, sparsemat__pivot_entry(sp_mat)),
          sparsemat__plus(sp_mat, [
            sp_row_dot(
              sp_mat,
              a_special_solution,
              aref1(sparsemat__rows(sp_mat), nn),
            ),
            aref1(sparsemat__constants_column(sp_mat), nn),
          ]),
        ])
        if !d_zerop(a_new_entry).truthy() {
          sparsemat__vector_push(
            aref1(sparsemat__column_used_in_row(sp_mat), nn),
            a_special_solution,
          )
          |> ignore
          sparsemat__vector_push(a_new_entry, a_special_solution) |> ignore
        }
      }
      nn = nn - 1
    }
  }
  if !(sparsemat__solutions(sp_mat).truthy() &&
    struct_typep(sparsemat__solutions(sp_mat), "sparse-matrix")) {
    sparsemat__set_solutions(sp_mat, sparsemat__make_sparse_matrix()) |> ignore
  }
  sp_set_rows(sparsemat__solutions(sp_mat), solution_rows) |> ignore
  sp_set_type_of_entries(
    sparsemat__solutions(sp_mat),
    sparsemat__type_of_entries(sp_mat),
  )
  |> ignore
  sparsemat__set_special_solution(
    sparsemat__solutions(sp_mat),
    a_special_solution,
  )
}

///|
/// Converts a=b into a-b, or a into a also doing nothing if b is 0.
fn bring_to_left_side(possible_eqn : Value) -> Value raise {
  if atom(possible_eqn) {
    possible_eqn
  } else if eq(caar(possible_eqn), q_mequal) {
    if eql(caddr(possible_eqn), Fix(0L)) {
      cadr(possible_eqn)
    } else {
      sub(cadr(possible_eqn), caddr(possible_eqn))
    }
  } else {
    possible_eqn
  }
}

///|
fn sp_show_solutions(sp_mat : Value) -> Value raise {
  sp_show_matrix(sp_mat)
}

///|
fn sp_verify_solutions(sp_mat : Value) -> Value raise {
  for i in 0..<sparsemat__nrows(sp_mat) {
    for j in 0..<sparsemat__nrows(sparsemat__solutions(sp_mat)) {
      sparsemat__say("~%The dot product of row ~D and solution ~D is ~D", [
        int(i),
        int(j),
        sp_row_dot(
          sp_mat,
          sparsemat__row(sp_mat, int(i)),
          sparsemat__row(sparsemat__solutions(sp_mat), int(j)),
        ),
      ])
    }
  }
  let spec = sparsemat__special_solution(sparsemat__solutions(sp_mat))
  if spec.truthy() {
    let const_ = sparsemat__constants_column(sp_mat)
    for i in 0..<sparsemat__nrows(sp_mat) {
      let tem = sp_row_dot(sp_mat, sparsemat__row(sp_mat, int(i)), spec)
      sparsemat__say(
        "~%The dot product of the special solution and row ~D is ~A while the constant is ~A",
        [int(i), tem, aref1(const_, i)],
      )
      // (iassert (or ($zerop temm) (and (numberp temm) (< (abs temm) .00001))))
      let temm = sparsemat__plus(sp_mat, [aref1(const_, i), tem])
      if !(d_zerop(temm).truthy() ||
        (numberp(temm) && num_lt(num_abs(temm), Flo(0.00001)))) {
        fsignal(list1(Str("The expression ~A was not true"))) |> ignore
      }
    }
    sparsemat__say("~%The special solution is ok", [])
  }
  Nil
}

///|
fn nil_lessp(x : Value, y : Value) -> Value raise {
  if y is Nil {
    if x is Nil {
      Nil
    } else {
      t
    }
  } else if x is Nil {
    Nil
  } else {
    lbool(num_lt(x, y))
  }
}

///|
/// SORT-GROUPED-ARRAY is a Lisp Machine function that Maxima does not
/// define.
fn sp_sort_row(sp_mat : Value, i : Value) -> Value raise {
  sparsemat__call_undefined(sparsemat__q_sort_grouped_array, [
    sparsemat__row(sp_mat, i),
    Fix(2L),
    q_nil_lessp,
  ])
}

///|
fn desirable_row(x : Value) -> Value raise {
  ignore(x)
  Nil
}

///|
fn sp_best_pivot(sp_mat : Value) -> Value raise {
  sparsemat__set_pivot_entry(sp_mat, Nil) |> ignore
  sparsemat__set_row_number_before_swap(sp_mat, Nil) |> ignore
  sparsemat__fmat("~%What is best pivot in Row ~D?  ", [
    sparsemat__pivot_row_number(sp_mat),
  ])
  let prn = sparsemat__pivot_row_number(sp_mat)
  if eql(Fix(1L), aref1(sparsemat__rows_with_no_pivot(sp_mat), to_int(prn))) {
    sparsemat__fmat("Row ~D was previously found to have no possible pivot.", [
      sparsemat__pivot_row_number(sp_mat),
    ])
    return Nil
  }
  for test_name0 in sparsemat__pivot_test_list(sp_mat).iter() {
    let mut test_name = test_name0
    if !sparsemat__may_have_pivot(sp_mat, sparsemat__pivot_row_number(sp_mat)).truthy() {
      continue
    }
    sparsemat__set_last_good_row(sp_mat, int(sparsemat__nrows(sp_mat) - 1))
    |> ignore
    let mut fresh_row = true
    let mut best : Value = Nil
    let no_gcd : Value = Nil
    let mut test_fn : (Value, Value) -> Bool raise = (_, _) => true
    while fresh_row {
      if desirable_row(sparsemat__pivot_row(sp_mat)).truthy() &&
        equal(sparsemat__type_of_entries(sp_mat), q_kw_integer) {
        test_name = q_gcd_column
      }
      if eq(test_name, q_any) {
        test_fn = (_, _) => true
        best = Fix(1L)
      } else if eq(test_name, q_kw_any_macsyma) {
        sp_best_pivot_macsyma(sp_mat) |> ignore
        return q_here_maybe_pivot
      } else if eq(test_name, q_gcd) {
        // (multiple-value (best no-gcd) (catch-error ...)): neither
        // MULTIPLE-VALUE nor CATCH-ERROR is defined, so the form calls the
        // undefined function BEST.
        sparsemat__call_undefined(sparsemat__q_best, [no_gcd]) |> ignore
      } else if eq(test_name, q_min) {
        best = sp_smallest_possible_pivot(sp_mat)
        test_fn = (a, b) => equal(a, b)
      } else if eq(test_name, q_gcd_column) {
        best = sp_smallest_possible_pivot(sp_mat)
        test_fn = (a, b) => equal(a, b)
      } else if eq(test_name, q_unit) {
        if numberp(sparsemat__type_of_entries(sp_mat)) {
          best = Fix(1L)
          test_fn = (_, _) => true
        } else {
          best = Fix(1L)
          test_fn = (a, b) => equal(a, b)
        }
      } else {
        merr("~A is not a possible test.", [test_name]) |> ignore
      }
      let mut value : Value = Nil
      if no_gcd.truthy() {
        ()
      } else if best is Nil || d_zerop(best).truthy() {
        sparsemat__fmat("~%Row ~D was found to be zero while looking for ~A.", [
          sparsemat__pivot_row_number(sp_mat),
          test_name,
        ])
        sp_put_back_row_with_no_pivot(sp_mat) |> ignore
      } else if eq(test_name, q_gcd) && no_gcd.truthy() {
        ()
      } else {
        let pivot_row = sparsemat__pivot_row(sp_mat)
        let n = length(pivot_row)
        for ii = 0; ii < n; ii = ii + 2 {
          if aref1(sparsemat__pivot_row(sp_mat), ii).truthy() {
            value = num_abs(aref1(sparsemat__pivot_row(sp_mat), ii + 1))
            if test_fn(value, best) {
              let mut col_to_pivot = aref1(sparsemat__pivot_row(sp_mat), ii)
              if equal(test_name, q_gcd_column) {
                if desirable_row(sparsemat__pivot_row(sp_mat)).truthy() {
                  let temp_col = sp_find_good_column_to_pivot(sp_mat)
                  if temp_col.truthy() {
                    col_to_pivot = temp_col
                  }
                }
                sp_force_pivot_row_to_contain_gcd(sp_mat, col_to_pivot)
                |> ignore
                sparsemat__set_pivot_entry(
                  sp_mat,
                  sp_entry(
                    sp_mat,
                    sparsemat__pivot_row_number(sp_mat),
                    col_to_pivot,
                  ),
                )
                |> ignore
                sparsemat__set_pivot_row(
                  sp_mat,
                  sparsemat__row(sp_mat, sparsemat__pivot_row_number(sp_mat)),
                )
                |> ignore
              } else {
                sparsemat__set_pivot_entry(
                  sp_mat,
                  aref1(sparsemat__pivot_row(sp_mat), ii + 1),
                )
                |> ignore
              }
              sp_enter_pivot_data(sp_mat, col_to_pivot) |> ignore
              return q_here_is_pivot
            }
          }
        }
        // WITH-ONCE-ONLY stores the cached pivot row back.
        sparsemat__set_pivot_row(sp_mat, pivot_row) |> ignore
      }
      if no_gcd.truthy() {
        ()
      } else if value is Nil {
        sp_put_back_row_with_no_pivot(sp_mat) |> ignore
        sparsemat__fmat("It is zero.", [])
      }
      if no_gcd.truthy() {
        sparsemat__say("~%Row ~D has no gcd.", [
          sparsemat__pivot_row_number(sp_mat),
        ])
      } else if eq(test_name, q_gcd) {
        sparsemat__fmat("~%Row ~D has gcd ~D but no pivot of that size.", [
          sparsemat__pivot_row_number(sp_mat),
          best,
        ])
      } else if eq(test_name, q_unit) {
        sparsemat__fmat("~%Row ~D does not have a unit for a pivot.", [
          sparsemat__pivot_row_number(sp_mat),
        ])
      }
      fresh_row = sp_swap_pivot_row_with_later_one(sp_mat).truthy()
    }
  }
  Nil
}

///|
fn sp_put_back_row_with_no_pivot(sp_mat : Value) -> Value raise {
  if sparsemat__row_number_before_swap(sp_mat).truthy() {
    sparsemat__swap_rows_and_constants(
      sp_mat,
      sparsemat__pivot_row_number(sp_mat),
      sparsemat__row_number_before_swap(sp_mat),
    )
    |> ignore
    sparsemat__fmat("There is no pivot in row ~D so exchanging it back", [
      sparsemat__row_number_before_swap(sp_mat),
    ])
    sparsemat__set_pivot_row(
      sp_mat,
      sparsemat__row(sp_mat, sparsemat__pivot_row_number(sp_mat)),
    )
    |> ignore
    aset1(
      sparsemat__rows_with_no_pivot(sp_mat),
      to_int(sparsemat__row_number_before_swap(sp_mat)),
      Fix(1L),
    )
    |> ignore
    sparsemat__set_row_number_before_swap(sp_mat, Nil)
  } else {
    Nil
  }
}

///|
/// Returns t if it did nil if it did not.
fn sp_swap_pivot_row_with_later_one(sp_mat : Value) -> Value raise {
  let mut j = to_int(sparsemat__last_good_row(sp_mat))
  while j > to_int(sparsemat__pivot_row_number(sp_mat)) {
    if d_zerop(aref1(sparsemat__rows_with_no_pivot(sp_mat), j)).truthy() {
      sparsemat__swap_rows_and_constants(
        sp_mat,
        sparsemat__pivot_row_number(sp_mat),
        int(j),
      )
      |> ignore
      sparsemat__set_pivot_row(
        sp_mat,
        sparsemat__row(sp_mat, sparsemat__pivot_row_number(sp_mat)),
      )
      |> ignore
      sparsemat__set_last_good_row(sp_mat, int(j - 1)) |> ignore
      sparsemat__set_row_number_before_swap(sp_mat, int(j)) |> ignore
      sparsemat__fmat(" Exchanging Row ~D for Row ~D.", [
        sparsemat__pivot_row_number(sp_mat),
        int(j),
      ])
      return t
    }
    j = j - 1
  }
  Nil
}

///|
fn sp_best_pivot_macsyma(sp_mat : Value) -> Value raise {
  let tests : Array[(Value) -> Bool raise] = [
    x => eql(x, Fix(-1L)) || eql(x, Fix(1L)),
    x => numberp(x) && num_lt(num_abs(x), Fix(100L)),
    x => numberp(x),
    x => d_numberp(x).truthy(),
    _ => true,
  ]
  for test_fn in tests {
    let n = length(sparsemat__pivot_row(sp_mat))
    for i = 0; i < n; i = i + 2 {
      if aref1(sparsemat__pivot_row(sp_mat), i).truthy() &&
        test_fn(aref1(sparsemat__pivot_row(sp_mat), i + 1)) {
        sparsemat__set_pivot_entry(
          sp_mat,
          aref1(sparsemat__pivot_row(sp_mat), i + 1),
        )
        |> ignore
        sp_enter_pivot_data(sp_mat, aref1(sparsemat__pivot_row(sp_mat), i))
        |> ignore
        return q_done
      }
    }
  }
  if sp_swap_pivot_row_with_later_one(sp_mat).truthy() {
    sp_best_pivot_macsyma(sp_mat)
  } else {
    Nil
  }
}

///|
fn sp_smallest_possible_pivot(sp_mat : Value) -> Value raise {
  let pivot_row = sparsemat__pivot_row(sp_mat)
  let mut ans : Value = Nil
  let n = length(pivot_row)
  for ii = 0; ii < n; ii = ii + 2 {
    if aref1(pivot_row, ii).truthy() {
      let v = num_abs(aref1(pivot_row, ii + 1))
      if ans is Nil || num_lt(v, ans) {
        ans = v
      }
    }
  }
  // LOOP's MINIMIZE returns 0 when nothing was minimized.
  if ans is Nil {
    Fix(0L)
  } else {
    ans
  }
}

///|
fn sp_verify_solutions_for_original_array(
  sp_mat : Value,
  aarray : Value,
) -> Value raise {
  sp_get_rows_from_array(
    sp_mat,
    aarray,
    type_=sparsemat__type_of_entries(sp_mat),
  )
  |> ignore
  sp_verify_solutions(sp_mat)
}

///|
fn sp_init(sp_mat : Value, plist : Value) -> Value raise {
  let initial_data = get(plist, q_kw_rows)
  let atype_of_entries = get(plist, q_kw_type_of_entries)
  let asolutions = get(plist, sparsemat__q_kw_solutions)
  let acolumn_used_in_row = get(plist, q_kw_column_used_in_row)
  let acolumns_used_to_pivot = get(plist, sparsemat__q_kw_columns_used_to_pivot)
  if initial_data.truthy() {
    sp_set_rows(sp_mat, initial_data) |> ignore
  }
  if atype_of_entries.truthy() {
    sp_set_type_of_entries(sp_mat, atype_of_entries) |> ignore
  }
  if asolutions.truthy() {
    sparsemat__set_solutions(sp_mat, asolutions) |> ignore
  }
  if acolumns_used_to_pivot.truthy() {
    sparsemat__set_columns_used_to_pivot(sp_mat, acolumns_used_to_pivot)
    |> ignore
  }
  if acolumn_used_in_row.truthy() {
    sparsemat__set_column_used_in_row(sp_mat, acolumn_used_in_row)
  } else {
    Nil
  }
}

///|
/// Creates the transpose of the sparse-matrix.  The result is stored in
/// the transpose instance-variable.
fn sp_make_transpose(sp_mat : Value) -> Value raise {
  let transpose_rows = make_array(
    [length(sparsemat__list_of_all_columns_occurring(sp_mat))],
    initial=Fix(0L),
  )
  sparsemat__set_list_of_all_columns_occurring(
    sp_mat,
    sort_list(sparsemat__list_of_all_columns_occurring(sp_mat), (a, b) => num_lt(
      a, b,
    )),
  )
  |> ignore
  let ncols = length(sparsemat__list_of_all_columns_occurring(sp_mat))
  let mut i = 0
  for j in sparsemat__list_of_all_columns_occurring(sp_mat).iter() {
    if i >= ncols {
      break
    }
    let rowj = sparsemat__make_solution_row()
    struct_set(rowj, 1, sparsemat__make_row(100)) |> ignore
    struct_set(rowj, 0, j) |> ignore
    for ii in 0..<sparsemat__nrows(sp_mat) {
      let val = sp_entry(sp_mat, int(ii), j)
      if val.truthy() {
        array_push_extend_replace(struct_ref(rowj, 1), int(ii)) |> ignore
        array_push_extend_replace(struct_ref(rowj, 1), val) |> ignore
      }
    }
    aset1(transpose_rows, i, struct_ref(rowj, 1)) |> ignore
    i = i + 1
  }
  let tr = sparsemat__make_sparse_matrix()
  sparsemat__set_rows(tr, transpose_rows) |> ignore
  sparsemat__set_type_of_entries(tr, sparsemat__type_of_entries(sp_mat))
  |> ignore
  sparsemat__set_transpose(sp_mat, tr)
}

///|
fn sp_set_current_column_above_pivot_row_number(
  sp_mat : Value,
  j : Value,
) -> Value raise {
  let cur = sparsemat__current_column_above_pivot_row_number(sp_mat)
  if cur.truthy() {
    // (adjust-array c n :fill-pointer (fill-pointer c)): the array has no
    // fill pointer, which is an error in CL.
    let fp = fill_pointer(cur)
    let adj = adjust_array(cur, [sparsemat__nrows(sp_mat)], initial=Fix(0L))
    set_fill_pointer(adj, fp)
    sparsemat__set_current_column_above_pivot_row_number(sp_mat, adj) |> ignore
    fillarray(sparsemat__current_column_above_pivot_row_number(sp_mat), Nil)
    |> ignore
  } else {
    sparsemat__set_current_column_above_pivot_row_number(
      sp_mat,
      make_array([sparsemat__nrows(sp_mat)], initial=Fix(0L)),
    )
    |> ignore
  }
  for i in to_int(sparsemat__pivot_row_number(sp_mat))..<sparsemat__nrows(sp_mat) {
    aset1(
      sparsemat__current_column_above_pivot_row_number(sp_mat),
      i,
      sp_entry(sp_mat, int(i), j),
    )
    |> ignore
  }
  Nil
}

///|
fn sp_set_constants_column(sp_mat : Value, j : Value) -> Value raise {
  sparsemat__set_constants_column_number(sp_mat, j) |> ignore
  let cc = sparsemat__constants_column(sp_mat)
  if cc.truthy() {
    if array_total_size(cc) < array_total_size(sparsemat__rows(sp_mat)) {
      let fp = fill_pointer(cc)
      let adj = adjust_array(
        cc,
        [array_total_size(sparsemat__rows(sp_mat))],
        initial=Fix(0L),
      )
      set_fill_pointer(adj, fp)
      sparsemat__set_constants_column(sp_mat, adj) |> ignore
    }
  } else {
    sparsemat__set_constants_column(
      sp_mat,
      sparsemat__make_row(array_total_size(sparsemat__rows(sp_mat))),
    )
    |> ignore
  }
  let n = array_total_size(sparsemat__constants_column(sp_mat))
  for i in 0..<n {
    aset1(sparsemat__constants_column(sp_mat), i, Fix(0L)) |> ignore
  }
  sparsemat__set_list_of_all_columns_occurring(
    sp_mat,
    delete(
      sparsemat__constants_column_number(sp_mat),
      sparsemat__list_of_all_columns_occurring(sp_mat),
    ),
  )
  |> ignore
  for i in 0..<sparsemat__nrows(sp_mat) {
    let this_row = aref1(sparsemat__rows(sp_mat), i)
    let m = length(this_row)
    for ii = 0; ii < m; ii = ii + 2 {
      if eql(aref1(this_row, ii), j) {
        aset1(this_row, ii, Nil) |> ignore
        aset1(sparsemat__constants_column(sp_mat), i, aref1(this_row, ii + 1))
        |> ignore
      }
    }
  }
  Nil
}

///|
fn where_the_min(an_array : Value) -> Value raise {
  let n = array_total_size(an_array)
  let mut the_min : Value = Nil
  let mut where_the_min : Value = Nil
  let mut null_vector = true
  for i in 0..<n {
    if aref1(an_array, i).truthy() {
      the_min = num_abs(aref1(an_array, i))
      where_the_min = int(i)
      null_vector = false
      break
    }
  }
  if !null_vector {
    for i in 0..<n {
      let tem = aref1(an_array, i)
      if tem.truthy() {
        if num_lt(num_abs(tem), the_min) {
          where_the_min = int(i)
          the_min = num_abs(tem)
        }
      }
    }
    where_the_min
  } else {
    Nil
  }
}

///|
/// J is column number.  Elementary row operations and swaps of rows are
/// performed with rows occurring after the pivot row number to ensure that
/// the pivot-row contains the gcd of the entries in rows greater than the
/// pivot row number and in column j.
fn sp_force_pivot_row_to_contain_gcd(sp_mat : Value, j : Value) -> Value raise {
  sp_set_current_column_above_pivot_row_number(sp_mat, j) |> ignore
  let colj = sparsemat__current_column_above_pivot_row_number(sp_mat)
  let first_entry = aref1(colj, to_int(sparsemat__pivot_row_number(sp_mat)))
  if !physical_equal_value(
      colj,
      sparsemat__current_column_above_pivot_row_number(sp_mat),
    ) {
    merror(q_wow, Nil) |> ignore
  }
  let mut temp = first_entry
  let mut the_gcd = temp
  // (row-length ...) calls the undefined ARRAY-DIMENSION-N.
  let rl = to_int(
    row_length(sparsemat__current_column_above_pivot_row_number(sp_mat)),
  )
  for i in 0..<rl {
    temp = aref1(colj, i)
    if temp.truthy() {
      the_gcd = sparsemat__gcd(temp, the_gcd)
    }
  }
  while true {
    let where_the_min = where_the_min(colj)
    if !eql(where_the_min, sparsemat__pivot_row_number(sp_mat)) {
      sparsemat__swap_rows_and_constants(
        sp_mat,
        sparsemat__pivot_row_number(sp_mat),
        where_the_min,
      )
      |> ignore
      sparsemat__fmat(
        "~%Exchanging rows ~D and ~D to help force gcd ~D into pivot-row.",
        [sparsemat__pivot_row_number(sp_mat), where_the_min, the_gcd],
      )
      sp_set_pivot_row(sp_mat, sparsemat__pivot_row_number(sp_mat)) |> ignore
    }
    let prn = to_int(sparsemat__pivot_row_number(sp_mat))
    if equal(the_gcd, num_abs(null_to_zero(aref1(colj, prn)))) {
      sparsemat__fmat(
        "~%Row ~D has ~D in column ~D which is the gcd of the column above row ~D.",
        [
          sparsemat__pivot_row_number(sp_mat),
          aref1(colj, prn),
          j,
          sparsemat__pivot_row_number(sp_mat),
        ],
      )
      break
    } else {
      let piv_entry = aref1(colj, prn)
      let mut the_min_gcd = num_abs(piv_entry)
      let mut where_the_min_gcd : Value = Nil
      let n = array_total_size(colj)
      for i in 0..<n {
        if aref1(colj, i).truthy() {
          let tem = num_abs(sparsemat__gcd(piv_entry, aref1(colj, i)))
          if eql(tem, the_gcd) {
            where_the_min_gcd = int(i)
            break
          }
          if num_lt(tem, the_min_gcd) {
            the_min_gcd = tem
            where_the_min_gcd = int(i)
          }
        }
      }
      // GENERAL-GCD is not defined in Maxima.
      let gcdfacts = sparsemat__call_undefined(sparsemat__q_general_gcd, [
        piv_entry,
        aref1(colj, to_int(where_the_min_gcd)),
      ])
      // add new row (first gcdfacts)*pivot-row + (second gcdfacts)*row
      // and fix constants. redo force pivot row.
      sp_set_current_row(sp_mat, where_the_min_gcd) |> ignore
      let crow = sparsemat__current_row(sp_mat)
      let new_row = make_array(
        [fill_pointer(crow)],
        initial=Fix(0L),
        fill=fill_pointer(crow),
      )
      fillarray(new_row, crow) |> ignore
      let mut constant : Value = Nil
      let tem = sparsemat__constants_column(sp_mat)
      if tem.truthy() {
        constant = aref1(tem, to_int(sparsemat__current_row_number(sp_mat)))
      }
      sp_add_new_row(sp_mat, new_row, constant~) |> ignore
      sp_multiply_row(
        sp_mat,
        sparsemat__current_row_number(sp_mat),
        cadr(gcdfacts),
      )
      |> ignore
      sp_row_operation(sp_mat, car(gcdfacts)) |> ignore
      if symval(q_ear_verbose).truthy() {
        sparsemat__say(
          "~%The gcd is ~A Adding a new row with  entry in col ~A of ~A",
          [
            the_gcd,
            j,
            sp_entry(sp_mat, sparsemat__current_row_number(sp_mat), j),
          ],
        )
      }
      sp_force_pivot_row_to_contain_gcd(sp_mat, j) |> ignore
      break
    }
  }
  q_done
}

///|
fn sp_add_new_row(self_ : Value, a_row : Value, constant? : Value = Nil) -> Value raise {
  let dim = 1 + sparsemat__nrows(self_)
  let mut ok = false
  for i in 0..<(dim - 1) {
    maybe_move_back_fill_pointer(sparsemat__row(self_, int(i))) |> ignore
    if fill_pointer(sparsemat__row(self_, int(i))) == 0 {
      if constant.truthy() {
        if eql(
            Fix(0L),
            null_to_zero(aref1(sparsemat__constants_column(self_), i)),
          ) {
          aset1(sparsemat__constants_column(self_), i, constant) |> ignore
          ok = true
        }
      } else {
        ok = true
      }
      if ok {
        aset1(sparsemat__rows_with_no_pivot(self_), i, Fix(0L)) |> ignore
        aset1(sparsemat__rows(self_), i, a_row) |> ignore
      }
    }
  }
  if !ok {
    sparsemat__set_current_column_above_pivot_row_number(self_, Nil) |> ignore
    // ARRAY-GROW is a Lisp Machine function that Maxima does not define.
    sparsemat__set_rows_with_no_pivot(
      self_,
      sparsemat__call_undefined(sparsemat__q_array_grow, [
        sparsemat__rows_with_no_pivot(self_),
        int(dim),
      ]),
    )
    |> ignore
    sparsemat__set_column_used_in_row(
      self_,
      sparsemat__call_undefined(sparsemat__q_array_grow, [
        sparsemat__column_used_in_row(self_),
        int(dim),
      ]),
    )
    |> ignore
    vector_push_extend(a_row, sparsemat__rows(self_)) |> ignore
    set_fill_pointer(sparsemat__rows(self_), dim)
    if constant.truthy() {
      return int(
        vector_push_extend(constant, sparsemat__constants_column(self_)),
      )
    }
  }
  Nil
}

///|
/// Gcd of all non-nil elements occurring in an array.
fn gcd_array(an_array : Value) -> (Value, Value) raise {
  let n = array_total_size(an_array)
  let mut the_gcd : Value = Nil
  let mut where_ : Value = Nil
  for ii in 0..<n {
    the_gcd = aref1(an_array, ii)
    if the_gcd.truthy() {
      break
    }
  }
  for ii in 0..<n {
    let temp = aref1(an_array, ii)
    if temp.truthy() {
      the_gcd = sparsemat__gcd(the_gcd, temp)
      if equal(the_gcd, num_abs(temp)) {
        where_ = int(ii)
        if eql(the_gcd, Fix(1L)) {
          break
        }
      }
    }
  }
  (the_gcd, where_)
}

///|
fn rational_inverse(x : Value) -> Value raise {
  num_div(Fix(1L), x)
}

///|
fn divides(a : Value, b : Value) -> Value raise {
  d_zerop(num_mod(b, a))
}

///|
/// Tries to find a column where the gcd is equal to the entry of the
/// pivot-row without changing the pivot row.
fn sp_find_good_column_to_pivot(sp_mat : Value) -> Value raise {
  let n = length(sparsemat__pivot_row(sp_mat))
  for ii = 0; ii < n; ii = ii + 2 {
    if aref1(sparsemat__pivot_row(sp_mat), ii).truthy() {
      sp_set_current_column_above_pivot_row_number(
        sp_mat,
        aref1(sparsemat__pivot_row(sp_mat), ii),
      )
      |> ignore
      let the_gcd = gcd_array(
        sparsemat__current_column_above_pivot_row_number(sp_mat),
      ).0
      if eql(num_abs(aref1(sparsemat__pivot_row(sp_mat), ii + 1)), the_gcd) {
        return aref1(sparsemat__pivot_row(sp_mat), ii)
      }
    }
  }
  Nil
}

///|
/// Returns the primary value; `sparsemat__sp_gcd_column_mv` returns both
/// values of GCD-ARRAY.
fn sp_gcd_column(sp_mat : Value, j : Value) -> Value raise {
  sparsemat__sp_gcd_column_mv(sp_mat, j).0
}

///|
fn sparsemat__sp_gcd_column_mv(sp_mat : Value, j : Value) -> (Value, Value) raise {
  sparsemat__set_pivot_row_number(sp_mat, Fix(0L)) |> ignore
  sp_set_current_column_above_pivot_row_number(sp_mat, j) |> ignore
  gcd_array(sparsemat__current_column_above_pivot_row_number(sp_mat))
}

///|
/// The Lisp uses the undefined macro MULTIPLE-VALUE, so the form calls the
/// undefined function THE-GCD.
fn show_gcd_of_columns(a_sparse_matrix : Value) -> Value raise {
  let all_col = sparsemat__list_of_all_columns_occurring(a_sparse_matrix)
  for i in all_col.iter() {
    sparsemat__call_undefined(sparsemat__q_the_gcd, [sparsemat__q_where])
    |> ignore
    sparsemat__say("~%Column ~D has gcd ~D at it occurs in row ~A. ", [
      i,
      Nil,
      Nil,
    ])
  }
  Nil
}

///|
let sparsemat__q_the_gcd : Value = sym("the-gcd")

///|
let sparsemat__q_where : Value = Nil

///|
fn sp_show_row_array_leaders(sp_mat : Value) -> Value raise {
  let n = array_total_size(sparsemat__rows(sp_mat))
  for i in 0..<n {
    sparsemat__say("~% Row ~D has array-leader ~A.", [
      int(i),
      sparsemat__call_undefined(sparsemat__q_list_array_leader, [
        sparsemat__row(sp_mat, int(i)),
      ]),
    ])
  }
  Nil
}

///|
/// MAKE-SPARSE-SOLUTION is not defined in Maxima.
fn sp_make_rows_desirable(sp_mat : Value, a_list : Value) -> Value raise {
  for i in a_list.iter() {
    let this_row = sparsemat__row(sp_mat, i)
    let arr = make_array(
      [array_total_size(sparsemat__row(sp_mat, i))],
      initial=Fix(0L),
      fill=fill_pointer(this_row),
    )
    let temp = sparsemat__call_undefined(sparsemat__q_make_sparse_solution, [
      sparsemat__q_kw_row,
      arr,
    ])
    fillarray(
      sparsemat__call_undefined(sparsemat__q_sparse_solution_row, [temp]),
      this_row,
    )
    |> ignore
    aset1(sparsemat__rows(sp_mat), to_int(i), temp) |> ignore
  }
  Nil
}

///|
let sparsemat__q_kw_row : Value = sym(":row")

///|
fn fmat(l : Value) -> Value raise {
  if symval(q_ear_verbose).truthy() {
    // (apply 'format l)
    format(car(l), lstring(cadr(l)), list_to_array(cddr(l)))
  } else {
    Nil
  }
}

///|
fn sp_show_column(sp_mat : Value, j : Value) -> Value raise {
  for i in 0..<sparsemat__nrows(sp_mat) {
    sparsemat__say("~% entry in row ~D col ~D is ~A", [
      int(i),
      j,
      sp_entry(sp_mat, int(i), j),
    ])
  }
  Nil
}

///|
/// Verifies the entries above the pivot are indeed 0.
fn sp_verify_columns_above_pivots_are_zero(sp_mat : Value) -> Value raise {
  for i in 0..<sparsemat__nrows(sp_mat) {
    let col = aref1(sparsemat__column_used_in_row(sp_mat), i)
    if col.truthy() {
      let mut ok = true
      for ii in (i + 1)..<sparsemat__nrows(sp_mat) {
        if sp_entry(sp_mat, int(ii), col).truthy() {
          sparsemat__say(
            "~%Pivot in row ~A has nonzero entry above it in column ~A row ~D.",
            [int(i), col, int(ii)],
          )
          ok = false
        }
      }
      if ok {
        sparsemat__say("~%For Row ~D column ~D is ok above the pivot", [
          int(i),
          col,
        ])
      }
    }
  }
  Nil
}

///|
/// Cleans out all the columns in a-row such that rows has a pivot in that
/// column.
fn sp_reduce_row_with_respect_to_rows(sp_mat : Value, a_row : Value) -> Value raise {
  sparsemat__set_current_row(sp_mat, a_row) |> ignore
  sparsemat__set_current_row_number(sp_mat, Str("Fake row number")) |> ignore
  let mut not_done = true
  while not_done {
    let n = length(a_row)
    let mut found = false
    for ii = 0; ii < n; ii = ii + 2 {
      let col = aref1(a_row, ii)
      if col.truthy() {
        let piv_row = gethash(col, sparsemat__columns_used_to_pivot(sp_mat))
        if piv_row.truthy() {
          sp_set_pivot_row(sp_mat, piv_row) |> ignore
          sparsemat__set_pivot_entry(sp_mat, sp_entry(sp_mat, piv_row, col))
          |> ignore
          let factor = sparsemat__times(sp_mat, [
            Fix(-1L),
            sparsemat__inverse(sp_mat, sparsemat__pivot_entry(sp_mat)),
            aref1(a_row, ii + 1),
          ])
          sp_row_operation(sp_mat, factor) |> ignore
          found = true
          break
        }
      }
    }
    if !found {
      not_done = false
    }
  }
  sp_set_current_row(sp_mat, Fix(0L)) |> ignore
  a_row
}

///|
fn sp_determinant(sp_mat : Value) -> Value raise {
  let mut answer : Value = Nil
  let mut correct = 0
  sparsemat__set_sign_of_row_permutation(sp_mat, Fix(1L)) |> ignore
  if eq(sparsemat__type_of_entries(sp_mat), q_kw_integer) {
    sparsemat__say("Integer type is not good for determinant", [])
    if sparsemat__reduced(sp_mat).truthy() {
      fsignal(list1(Str("The expression ~A was not true"))) |> ignore
    }
    sp_set_type_of_entries(sp_mat, q_kw_any_macsyma) |> ignore
  }
  sp_reduce(sp_mat) |> ignore
  let mut finished = false
  for i in 0..<sparsemat__nrows(sp_mat) {
    // (show i)
    sparsemat__say("~%The value of ~A is ~A", [Str("I"), int(i)])
    let tem = aref1(sparsemat__column_used_in_row(sp_mat), i)
    if eql(Fix(0L), tem) {
      finished = true
      break
    }
    if tem is Nil {
      answer = Fix(0L)
      finished = true
      break
    }
  }
  if !finished {
    correct = -1
  }
  if answer is Nil {
    answer = sparsemat__sign_of_row_permutation(sp_mat)
    let tem = Collector::new()
    let mut no_pivot = false
    for i in 0..<sparsemat__nrows(sp_mat) {
      let col = aref1(sparsemat__column_used_in_row(sp_mat), i)
      if col.truthy() {
        let entry = sp_entry(sp_mat, int(i), col)
        answer = sp_mul_star(list([answer, entry]))
        tem.add(num_add(col, int(correct)))
      } else {
        sparsemat__say("~%There is no pivot in row ~A", [int(i)])
        answer = Fix(0L)
        no_pivot = true
        break
      }
    }
    if !no_pivot {
      answer = sp_mul_star(list([answer, sign_of_permutation(tem.result())]))
    }
  }
  answer
}

///|
fn sp_product_of_pivots(sp_mat : Value) -> Value raise {
  let mut answer : Value = Fix(1L)
  for i in 0..<sparsemat__nrows(sp_mat) {
    let col = aref1(sparsemat__column_used_in_row(sp_mat), i)
    if col.truthy() {
      let entry = sp_entry(sp_mat, int(i), col)
      if entry.truthy() {
        answer = sp_mul_star(list([answer, entry]))
      } else {
        sparsemat__say("~%Zero entry in (~A ,~A)", [int(i), col])
      }
    } else {
      sparsemat__say("~%There is no pivot in row ~A", [int(i)])
    }
  }
  answer
}

///|
/// Note: the parameters B and A are shadowed by the LET.
fn gcd_and_cofs(b : Value, a : Value) -> Value raise {
  let mut bp : Value = Fix(0L)
  let mut b_ : Value = Fix(1L)
  let mut ap : Value = Fix(1L)
  let mut a_ : Value = Fix(0L)
  let mut rp = a
  let mut rpp = b
  while true {
    let q = quot(rpp, rp)
    let r = num_sub(rpp, num_mul(q, rp))
    if eql(r, Fix(0L)) {
      return list([a_, b_, rp])
    }
    let nb = num_sub(bp, num_mul(b_, q))
    bp = b_
    b_ = nb
    let na = num_sub(ap, num_mul(a_, q))
    ap = a_
    a_ = na
    rpp = rp
    rp = r
  }
  Nil
}

///|
/// Converts a macsyma matrix or a list of lists to the corresponding sparse
/// matrix and sets up the type of entries.  It can be used to pick out a
/// submatrix.  Note if you don't renumber the columns the determinant of
/// submatrices may have wrong sign.
fn convert_to_sparse_matrix(
  row_list_matrix : Value,
  re_use_sparse_matrix? : Value = Nil,
  old_index_base? : Value = Fix(1L),
  rows_to_use? : Value = Nil,
  columns_to_use? : Value = Nil,
  rows_not_to_use? : Value = Nil,
  renumber_columns? : Value = Fix(0L),
  columns_not_to_use? : Value = Nil,
) -> Value raise {
  // The supplied-p variables RUSE, CUSE, RNUSE, CNUSE are approximated by
  // the values being non-NIL (NIL and an omitted argument behave alike).
  let ruse = rows_to_use.truthy()
  let cuse = columns_to_use.truthy()
  let rnuse = rows_not_to_use.truthy()
  let cnuse = columns_not_to_use.truthy()
  let row_list_matrix = if d_matrixp(row_list_matrix).truthy() {
    cdr(row_list_matrix)
  } else {
    row_list_matrix
  }
  let rows = Collector::new()
  let mut i = old_index_base
  for v0 in row_list_matrix.iter() {
    let v = if d_listp(v0).truthy() { cdr(v0) } else { v0 }
    if (!ruse || member(i, rows_to_use).truthy()) &&
      (!rnuse || !member(i, rows_not_to_use).truthy()) {
      let mut count = 0
      for u in v.iter() {
        if !d_zerop(u).truthy() {
          count = count + 1
        }
      }
      let ar = sparsemat__make_row(2 * count)
      rows.add(ar)
      let mut jj = num_sub(renumber_columns, Fix(1L))
      let mut j = old_index_base
      for w in v.iter() {
        if (!cuse || member(j, columns_to_use).truthy()) &&
          (!cnuse || !member(j, columns_not_to_use).truthy()) {
          if renumber_columns.truthy() {
            jj = one_plus(jj)
          } else {
            jj = j
          }
          if !d_zerop(w).truthy() {
            vector_push_extend(jj, ar) |> ignore
            vector_push_extend(w, ar) |> ignore
          }
        }
        j = one_plus(j)
      }
    }
    i = one_plus(i)
  }
  let rows = rows.result()
  let ar_rows = make_array([length(rows)], initial=Fix(0L), fill=length(rows))
  fillarray(ar_rows, rows) |> ignore
  let sp = if re_use_sparse_matrix.truthy() {
    re_use_sparse_matrix
  } else {
    sparsemat__make_sparse_matrix()
  }
  sparsemat__set_constants_column(sp, Nil) |> ignore
  sp_set_rows(sp, ar_rows) |> ignore
  sp_choose_type_of_entries(sp) |> ignore
  sp
}

///|
fn make_test(n : Value) -> Value raise {
  let nn = expt(n, Fix(2L))
  let lim = to_int(nn)
  let c = Collector::new()
  for i in 1..=lim {
    let r = Collector::new()
    for j in 1..=lim {
      if i == j {
        r.add(Fix(4L))
      } else if (i - j).abs() == 1 {
        r.add(Fix(-1L))
      } else if eql(int((i - j).abs()), n) {
        r.add(Fix(-1L))
      } else {
        r.add(Fix(0L))
      }
    }
    c.add(cons(list1(q_mlist), r.result()))
  }
  cons(list1(q_d_matrix), c.result())
}

///|
fn d_coerce_matrix(mat : Value) -> Value raise {
  if d_matrixp(mat).truthy() {
    mat
  } else if arrayp(mat) {
    let dims = array_dimensions(mat)
    let mut rows : Value = Nil
    match length(dims) {
      1 => rows = cons(list1(q_mlist), listarray(mat))
      2 => {
        let c = Collector::new()
        for i in 0..<to_int(car(dims)) {
          let r = Collector::new()
          for j in 0..<to_int(cadr(dims)) {
            r.add(aref(mat, [i, j]))
          }
          c.add(cons(list1(q_mlist), r.result()))
        }
        rows = c.result()
      }
      _ => ()
    }
    cons(list1(q_d_matrix), rows)
  } else {
    let c = Collector::new()
    for v in mat.iter() {
      c.add(cons(list1(q_mlist), v))
    }
    cons(list1(q_d_matrix), c.result())
  }
}

///|
fn sp_float(sp_mat : Value) -> Value raise {
  for i in 0..<sparsemat__nrows(sp_mat) {
    let row = aref1(sparsemat__rows(sp_mat), i)
    let n = fill_pointer(row)
    for j = 1; j < n; j = j + 2 {
      let tem = aref1(row, j)
      if numberp(tem) {
        aset1(row, j, lfloat(tem)) |> ignore
      }
    }
  }
  sp_set_type_of_entries(sp_mat, q_kw_float) |> ignore
  Nil
}

///|
fn float_zerop(n : Value) -> Value raise {
  if numberp(n) {
    lbool(zerop(n) || (floatp(n) && num_lt(num_abs(n), Flo(0.0001))))
  } else if atom(n) {
    Nil
  } else if affine_polynomialp(n).truthy() {
    Nil
  } else if rational_functionp(n).truthy() {
    float_zerop(car(n))
  } else {
    let type_of_n = caar(n)
    if eq(type_of_n, q_mrat) || eq(type_of_n, q_rat) {
      lbool(equal(cdr(n), rzero()))
    } else {
      let tem = d_ratsimp(n, Nil)
      lbool(numberp(tem) && zerop(tem))
    }
  }
}

///|
/// Takes a List-of-rows which is a list or array of arrays with
/// fill-pointer and alternating column number and entry and converts to a
/// sparse matrix.
fn sp_make_sparse_matrix(
  list_of_rows : Value,
  sp? : Value,
  type_of_entries? : Value = q_kw_any_macsyma,
) -> Value raise {
  let sp = match sp {
    Some(s) => s
    None => sparsemat__make_sparse_matrix()
  }
  let rows = if arrayp(list_of_rows) {
    list_of_rows
  } else {
    let r = make_array(
      [length(list_of_rows)],
      initial=Fix(0L),
      fill=length(list_of_rows),
    )
    fillarray(r, list_of_rows) |> ignore
    r
  }
  sp_set_rows(sp, rows) |> ignore
  sp_set_type_of_entries(sp, type_of_entries) |> ignore
  sp
}

///|
/// Takes list-subspace-rows and finds a basis for the space spanned by
/// all-rows modulo list-subspace-rows.  Returns two values: the reduced
/// sparse matrix for the quotient space and then the one for the subspace.
/// Note all-rows need not contain list-subspace-rows.
fn sp_quotient_space_basis(
  list_subspace_rows : Value,
  all_rows : Value,
) -> (Value, Value) raise {
  let sp_sub = sp_make_sparse_matrix(list_subspace_rows)
  sp_reduce(sp_sub) |> ignore
  let all_rows = if arrayp(all_rows) { listarray(all_rows) } else { all_rows }
  let real_rows = Collector::new()
  for v in all_rows.iter() {
    sp_reduce_row_with_respect_to_rows(sp_sub, v) |> ignore
    if fill_pointer(v) != 0 {
      real_rows.add(v)
    }
  }
  let sp = sp_make_sparse_matrix(real_rows.result())
  sp_reduce(sp) |> ignore
  (sp, sp_sub)
}

///|
fn d_fast_determinant(matrix : Value) -> Value raise {
  if symval(q_ear_sparse_matrix) is Nil {
    set(q_ear_sparse_matrix, sparsemat__make_sparse_matrix()) |> ignore
  }
  let sp = convert_to_sparse_matrix(
    matrix,
    re_use_sparse_matrix=symval(q_ear_sparse_matrix),
  )
  new_disrep(sp_determinant(sp))
}

///|
fn init_share_sparsemat() -> Unit raise {
  // (deff sp-rational-quotient #'/): the calls are translated as CL /.
  // (defvar *sparse-matrix* (make-sparse-matrix))
  if !boundp(q_ear_sparse_matrix) {
    set(q_ear_sparse_matrix, sparsemat__make_sparse_matrix()) |> ignore
  }
}
