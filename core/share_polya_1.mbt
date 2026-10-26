// Port of share/affine/polya.lisp (part 1): converting polynomials to
// sparse-matrix rows, the polynomial-vectors structure, dot
// simplification.
//
// The idea is to take a list of vectors containing polynomials, such that
// the rows will represent the rows of the eventual sparse matrix to be
// created. A table lists the terms occurring somewhere; each polynomial is
// associated with a sparse-matrix row whose entries are the coefficients
// obtained from looking in the hash table.
//
// Structures: polynomial-vectors and poly-data are described in
// share_amacros.mbt; the sparse-matrix structure belongs to sparsemat.lisp
// (make_struct("sparse-matrix", slots in defstruct order)), whose slots
// are accessed here by index (polya__sp_*).

///|
/// Slot indices of the sparse-matrix defstruct (sparsemat.lisp).
const POLYA_SP_ROWS : Int = 0

///|
const POLYA_SP_COLUMNS_USED_TO_PIVOT : Int = 15

///|
const POLYA_SP_COLUMN_USED_IN_ROW : Int = 16

///|
const POLYA_SP_LIST_OF_ALL_COLUMNS_OCCURRING : Int = 17

///|
const POLYA_SP_COLUMNS_WITH_NO_PIVOT : Int = 27

///|
const POLYA_SP_SOLUTIONS : Int = 29

///|
const POLYA_SP_SPECIAL_SOLUTION : Int = 31

///|
const POLYA_SP_CONSTANTS_COLUMN : Int = 32

///|
/// `(make-sparse-matrix)` with the defstruct defaults (sparsemat.lisp).
fn polya__make_sparse_matrix() -> Value {
  let slots : Array[Value] = Array::make(33, Nil)
  slots[12] = Fix(1L) // minimum-size-to-grow
  slots[13] = t // allow-reorder
  slots[19] = list2(q_unit, q_min) // pivot-test-list
  slots[25] = Fix(1L) // sign-of-row-permutation
  make_struct("sparse-matrix", slots)
}

///|
fn polya__pv(self_ : Value, slot : String) -> Value raise {
  amacros__slot_ref(self_, "pv-", slot)
}

///|
fn polya__set_pv(self_ : Value, slot : String, v : Value) -> Value raise {
  amacros__slot_set(self_, "pv-", slot, v)
}

///|
/// polya.lisp's $FIRSTN (n a-list), which replaces the core $firstn in
/// the function cell when the file is loaded: the Maxima list of the
/// first N elements.
fn polya__firstn(n : Value, a_list : Value) -> Value raise {
  subseq(a_list, 0, end=to_int(n) + 1)
}

///|
/// Takes a macsyma form and displays it.
fn macsyma_display(form : Value) -> Value raise {
  displa(list3(list1(q_mlabel), Fix(1L), form))
}

///|
fn gt(form : Value) -> Value raise {
  ignore(form)
  // GRIND-TOP-LEVEL is not defined in Maxima.
  raise LispError::SimpleError("The function GRIND-TOP-LEVEL is undefined.")
}

///|
fn list_terms(poly : Value) -> Value raise {
  if eql(poly, Fix(0L)) {
    Nil
  } else if atom(poly) {
    list1(poly)
  } else {
    let op = caar(poly)
    if eq(op, q_mplus) {
      cdr(poly)
    } else if eq(op, q_mtimes) ||
      eq(op, q_mexpt) ||
      eq(op, q_mnctimes) ||
      eq(op, q_mncexpt) {
      list1(poly)
    } else {
      raise LispError::SimpleError(
        format_to_string("~A is not a polynomial", [poly]),
      )
    }
  }
}

///|
/// `(rplaca (cdr a-list) (car a-list))`
fn remove_second(a_list : Value) -> Value raise {
  rplaca(cdr(a_list), car(a_list))
}

///|
/// Returns two values: the numerical coefficient and either 1 or an
/// atomic variable or a power eg ((mexpt simp) $x 2) or a list l whose
/// elements would be multiplied (by doing (cons '(mtimes simp) l)) to
/// obtain the appropriate monomial.
fn numerical_coefficient_and_monomial(term : Value) -> (Value, Value) raise {
  let mut answer : Value = Fix(1L)
  let mut monomial : Value = Fix(1L)
  if numberp(term) {
    answer = term
  } else if atom(term) {
    monomial = term
  } else {
    let op = caar(term)
    if eq(op, q_mtimes) {
      if d_numberp(second(term)).truthy() {
        answer = second(term)
        monomial = cddr(term)
      } else {
        monomial = cdr(term)
      }
      if atom(car(monomial)) {
        ()
      } else if appears_in(caar(monomial), q_mplus).truthy() {
        raise LispError::SimpleError("Some monomial with a sum in it")
      }
    } else if eq(op, q_mexpt) || eq(op, q_mnctimes) || eq(op, q_mncexpt) {
      monomial = term
    } else {
      raise LispError::SimpleError(format_to_string("~A is not a term.", [term]))
    }
    if length(monomial) == 1 {
      monomial = car(monomial)
    }
  }
  // Note this a monomial less the '(mtimes simp)!
  (answer, monomial)
}

// A monomial is 1, or a symbol, or ((mexpt simp) var number) or
// ((mncexpt simp) var number) or ((mtimes simp) a1 a2 ... an) where a1, a2,
// ... an are in the above list (but not 1). A term is a number, or a
// monomial, or ((mtimes simp) number monomial). A polynomial is either a
// term or ((mplus simp) t1 t2 ... tn). A premonomial is a monomial with the
// (mtimes simp) deleted; the keys in our hash table are premonomials.

///|
/// Returns a monomial given a premonomial.
fn make_monomial(premonomial : Value) -> Value raise {
  if atom(premonomial) {
    premonomial
  } else if atom(car(premonomial)) {
    cons(list2(q_mtimes, q_simp), premonomial)
  } else {
    let op = caar(premonomial)
    if eq(op, q_mexpt) || eq(op, q_mnctimes) || eq(op, q_mncexpt) {
      premonomial
    } else {
      cons(list2(q_mtimes, q_simp), premonomial)
    }
  }
}

///|
fn make_premonomial(monomial : Value) -> Value raise {
  if atom(monomial) {
    monomial
  } else {
    polyc__delete_equal(list2(q_mtimes, q_simp), monomial)
  }
}

///|
fn macsyma_list(l : Value) -> Value raise {
  cons(list2(q_mlist, q_simp), copy_list(l))
}

///|
fn show_coeff(poly : Value) -> Value raise {
  for u in list_terms(poly).iter() {
    let (coefficient, guts_monomial) = numerical_coefficient_and_monomial(u)
    format(t, "~%~A has coefficient ~D and monomial ~A", [
      u,
      coefficient,
      make_monomial(guts_monomial),
    ])
    |> ignore
    displa(macsyma_list(list3(u, coefficient, make_monomial(guts_monomial))))
    |> ignore
  }
  Nil
}

///|
/// Calls PARTS-OF-MONOMIAL (a function designator returning two values).
fn polya__parts_of_monomial(f : Value, u : Value) -> (Value, Value) raise {
  if eq(f, q_numerical_coefficient_and_monomial) {
    numerical_coefficient_and_monomial(u)
  } else if eq(f, q_sc_and_nc_parts) {
    sc_and_nc_parts_mv(u)
  } else if eq(f, q_extract_nc_and_sc_parts) {
    extract_nc_and_sc_parts(u)
  } else {
    (funcall(f, [u]), Nil)
  }
}

///|
/// Returns the row corresponding to the polynomial and the new
/// last-column-number. The first argument is a regular macsyma polynomial
/// in expanded form as returned by expand(polynomial). The second argument
/// is the hash-table, and the last is the number of entries in the hash
/// table.
fn convert_polynomial_to_vector(
  polynomial : Value,
  hash_table : Value,
  last_column_number? : Value = Nil,
  parts_of_monomial? : Value = Nil,
) -> (Value, Value) raise {
  let terms = list_terms(polynomial)
  let a_table = hash_table
  let answer = make_array([2 * length(terms)], fill=0)
  let mut last_column_number = last_column_number
  let mut parts_of_monomial = parts_of_monomial
  if last_column_number is Nil {
    last_column_number = int(hash_table_count(hash_table))
  }
  if parts_of_monomial is Nil {
    parts_of_monomial = q_numerical_coefficient_and_monomial
  }
  for u in terms.iter() {
    let (coeff, mon) = polya__parts_of_monomial(parts_of_monomial, u)
    let mut col = gethash(mon, a_table)
    if col is Nil {
      col = num_add(last_column_number, Fix(1L))
      last_column_number = col
      sethash(mon, a_table, col) |> ignore
    }
    vector_push_extend(col, answer) |> ignore
    vector_push_extend(coeff, answer) |> ignore
  }
  collect_coefficients(answer) |> ignore
  maybe_move_back_fill_pointer(answer) |> ignore
  (answer, last_column_number)
}

///|
/// `(multiple-value-bind (.first. .second.) form (values .second. .first.))`
/// on an already evaluated FORM: returns it (its secondary value is lost).
fn reverse_two_values(form : Value) -> Value raise {
  form
}

///|
fn mac_add_star(l : Value) -> Value raise {
  let tem = apply(q_add_star, l)
  if d_zerop(tem).truthy() {
    Fix(0L)
  } else {
    tem
  }
}

///|
fn collect_coefficients(a_row : Value) -> Value raise {
  let n = length(a_row)
  let mut i = 0
  while i < n {
    let col = aref1(a_row, i)
    if col.truthy() {
      let mut sum = aref1(a_row, i + 1)
      let mut ii = i + 2
      while ii < n {
        if equal(col, aref1(a_row, ii)) {
          sum = mac_add_star(list2(sum, aref1(a_row, ii + 1)))
          aset1(a_row, ii, Nil) |> ignore
          aset1(a_row, i + 1, sum) |> ignore
        }
        ii += 2
      }
    }
    i += 2
  }
  Nil
}

///|
fn sc_and_nc_parts(monomial : Value) -> Value raise {
  sc_and_nc_parts_mv(monomial).0
}

///|
/// SC_AND_NC_PARTS with both of its values: the scalar part and the
/// non-commutative part.
fn sc_and_nc_parts_mv(monomial : Value) -> (Value, Value) raise {
  let (nc, sc) = extract_nc_and_sc_parts(monomial)
  (sc, nc)
}

///|
fn d_list_terms(f : Value) -> Value raise {
  macsyma_list(list1(list_terms(f)))
}

///|
fn get_key(table : Value, value : Value) -> Value raise {
  let mut found : Value = Nil
  let mut done = false
  maphash(
    (ke, val) => if !done && equal(val, value) {
      found = ke
      done = true
    },
    table,
  )
  found
}

///|
/// This should actually return something equal to the original polynomial
/// which was fed into convert-polynomial-to-vector.
fn convert_polynomial_row(row : Value, hash_table : Value) -> Value raise {
  let terms = Collector::new()
  let n = length(row)
  let mut ii = 0
  while ii < n {
    let col = aref1(row, ii)
    if col.truthy() {
      let mon = get_key(hash_table, col)
      let cof = aref1(row, ii + 1)
      terms.add(mul_star(list2(cof, make_monomial(mon))))
    }
    ii += 2
  }
  add_star(terms.result())
}

///|
fn make_one_dimensional(an_array : Value) -> Value raise {
  if array_rank(an_array) == 1 {
    an_array
  } else {
    // A displaced array in CL; here a one-dimensional copy in row-major
    // order.
    let dims = list_to_array(array_dimensions(an_array)).map(d => to_int(d))
    let total = dims.fold(init=1, (a, b) => a * b)
    let v = make_array([total])
    let idx : Array[Int] = Array::make(dims.length(), 0)
    for k in 0..<total {
      aset1(v, k, aref(an_array, idx)) |> ignore
      let mut j = dims.length() - 1
      while j >= 0 {
        idx[j] += 1
        if idx[j] < dims[j] {
          break
        }
        idx[j] = 0
        j -= 1
      }
    }
    v
  }
}

///|
fn total_dimension(an_array : Value) -> Value raise {
  let mut p : Value = Fix(1L)
  for d in array_dimensions(an_array).iter() {
    p = num_mul(p, d)
  }
  p
}

///|
fn equation_length(eqn : Value) -> Value raise {
  if atom(eqn) {
    Fix(1L)
  } else if d_plusp(eqn).truthy() {
    int(length(eqn) - 1)
  } else {
    Fix(1L)
  }
}

///|
fn pv_get_rows_from_macsyma_equations(
  self_ : Value,
  equations : Value,
) -> Value raise {
  check_arg(equations, q_d_listp, list1(Str("Macsyma list"))) |> ignore
  let temp_array = make_array([length(equations)], fill=0)
  for u in cdr(equations).iter() {
    let tem = bring_to_left_side(u)
    if numberp(tem) {
      if zerop(tem) {
        format(t, "~%Eliminate Trivial equation", []) |> ignore
      } else {
        format(t, "~%Warning: Inconsistent equation ~A = 0", [tem]) |> ignore
      }
    } else {
      vector_push_extend(tem, temp_array) |> ignore
    }
  }
  pv_get_rows_from_array_of_polynomials(self_, temp_array) |> ignore
  polya__set_pv(
    self_,
    "constants-column-number",
    gethash(Fix(1L), polya__pv(self_, "table")),
  )
  |> ignore
  pv_set_up_sparse_matrix_from_rows(self_)
}

///|
fn pv_set_up_sparse_matrix_from_rows(self_ : Value) -> Value raise {
  if polya__pv(self_, "the-sparse-matrix") is Nil {
    polya__set_pv(self_, "the-sparse-matrix", polya__make_sparse_matrix())
    |> ignore
  }
  let sp = polya__pv(self_, "the-sparse-matrix")
  sp_set_rows(sp, polya__pv(self_, "rows")) |> ignore
  sp_set_type_of_entries(sp, polya__pv(self_, "type-of-entries")) |> ignore
  if polya__pv(self_, "constants-column-number").truthy() {
    sp_set_constants_column(sp, polya__pv(self_, "constants-column-number"))
  } else {
    struct_set(sp, POLYA_SP_CONSTANTS_COLUMN, Nil)
  }
}

///|
fn pv_reduce(self_ : Value) -> Value raise {
  pv_set_up_sparse_matrix_from_rows(self_) |> ignore
  sp_reduce(polya__pv(self_, "the-sparse-matrix")) |> ignore
  format(t, "~%The rank is ~D", [
    sp_number_of_pivots(polya__pv(self_, "the-sparse-matrix")),
  ])
}

///|
/// The SOLUTION-CORRESPONDS-TO-COLUMN macro refers to the variable SELF of
/// the function it is used in (pv-solve-suitable-to-sublis, where it is
/// expanded inline); on its own it has no SELF.
fn solution_corresponds_to_column(a_solution : Value) -> Value raise {
  ignore(a_solution)
  raise LispError::SimpleError("The variable SELF is unbound.")
}

///|
fn poly_identity(x : Value) -> Value raise {
  if x is Nil {
    Fix(0L)
  } else {
    x
  }
}

///|
fn pv_solve_suitable_to_sublis(self_ : Value) -> Value raise {
  let sp = polya__pv(self_, "the-sparse-matrix")
  if symval(q_ear_show_solve).truthy() {
    format(
      t,
      "~%Starting to solve.  There are ~D equations with ~D unknowns occurring.",
      [
        sp_number_of_rows(sp),
        int(length(struct_ref(sp, POLYA_SP_LIST_OF_ALL_COLUMNS_OCCURRING))),
      ],
    )
    |> ignore
  }
  sp_solve(sp, reduce_=t) |> ignore
  let col_list = struct_ref(sp, POLYA_SP_LIST_OF_ALL_COLUMNS_OCCURRING)
  let the_solutions = struct_ref(
    struct_ref(sp, POLYA_SP_SOLUTIONS),
    POLYA_SP_ROWS,
  )
  let the_special_solution = struct_ref(
    struct_ref(sp, POLYA_SP_SOLUTIONS),
    POLYA_SP_SPECIAL_SOLUTION,
  )
  let dim = array_total_size(the_solutions)
  let no_pivot = struct_ref(sp, POLYA_SP_COLUMNS_WITH_NO_PIVOT)
  ignore(no_pivot)
  let mut columns_used_to_pivot : Value = Nil
  if the_special_solution.truthy() {
    columns_used_to_pivot = struct_ref(sp, POLYA_SP_COLUMNS_USED_TO_PIVOT)
  }
  ignore(columns_used_to_pivot)
  if symval(q_ear_show_solve).truthy() {
    format(t, "~%The dimension of the solution space is ~D", [int(dim)])
    |> ignore
  }
  let final_answer = Collector::new()
  for i in col_list.iter() {
    let mut answer : Value = Fix(0L)
    let mut special_contribution : Value = Fix(0L)
    let n = length(the_solutions)
    for ii in 0..<n {
      let this_row = aref1(the_solutions, ii)
      // (solution-corresponds-to-column this-row)
      let corresponding_variables_column = getf(
        polya__pv(self_, "solution-plist"),
        this_row,
      )
      let tem = row_entry(this_row, i)
      if tem.truthy() {
        let parameter = if symval(q_d_solution_parameter).truthy() {
          Value::Sym(
            intern(
              format_to_string("~a~d", [
                symval(q_d_solution_parameter),
                int(ii),
              ]),
            ),
          )
        } else {
          ignore(corresponding_variables_column)
          raise LispError::SimpleError("unexpected case")
        }
        let val = sp_mul_star(list2(tem, parameter))
        answer = sp_add_star(list2(answer, val))
      }
    }
    if the_special_solution.truthy() {
      special_contribution = poly_identity(row_entry(the_special_solution, i))
    }
    answer = sp_add_star(list2(answer, special_contribution))
    final_answer.add(
      list3(
        list2(q_mequal, q_simp),
        get_key(polya__pv(self_, "table"), i),
        new_disrep(answer),
      ),
    )
  }
  polya__set_pv(
    self_,
    "solution-in-macsyma-format",
    cons(list1(q_mlist), final_answer.result()),
  )
}

///|
fn pv_get_rows_from_list_of_polynomials(
  self_ : Value,
  mac_list : Value,
  parts_of_monomial? : Value = Nil,
) -> Value raise {
  let ar = make_array([length(cdr(mac_list))])
  fillarray(ar, cdr(mac_list)) |> ignore
  pv_get_rows_from_array_of_polynomials(self_, ar, parts_of_monomial~)
}

///|
fn d_find_rank_of_list_of_polynomials(a_list : Value) -> Value raise {
  let pv = symval(q_d_poly_vector)
  pv_get_rows_from_list_of_polynomials(pv, a_list) |> ignore
  pv_set_up_sparse_matrix_from_rows(pv) |> ignore
  let sp = polya__pv(pv, "the-sparse-matrix")
  sp_reduce(sp) |> ignore
  let cols = struct_ref(sp, POLYA_SP_COLUMN_USED_IN_ROW)
  let mut rank = 0
  for i in 0..<length(cols) {
    if aref1(cols, i).truthy() {
      rank += 1
    }
  }
  int(rank)
}

///|
/// Takes AN-ARRAY whose entries are polynomials or arrays of polynomials.
/// It uses the parts-of-monomial if supplied to get the coefficients.
fn pv_get_rows_from_array_of_polynomials(
  self_ : Value,
  an_array : Value,
  parts_of_monomial? : Value = Nil,
  last_column_number? : Value = Nil,
) -> Value raise {
  let mut last_column_number = last_column_number
  let number_of_rows = length(an_array)
  let mut first_element : Value = Nil
  if 0 > number_of_rows {
    first_element = aref1(an_array, 0)
  }
  if arrayp(first_element) {
    polya__set_pv(
      self_,
      "length-of-array-of-tables",
      total_dimension(first_element),
    )
    |> ignore
    polya__set_pv(self_, "type-of-polynomials", q_kw_polynomial_vectors)
    |> ignore
    if polya__pv(self_, "array-of-tables") is Nil {
      pv_set_up_hash_tables(self_) |> ignore
    }
  } else {
    polya__set_pv(self_, "type-of-polynomials", q_kw_polynomial) |> ignore
    if polya__pv(self_, "table").truthy() {
      clrhash(polya__pv(self_, "table")) |> ignore
    } else {
      pv_set_up_hash_tables(self_) |> ignore
    }
  }
  polya__set_pv(self_, "rows", make_array([number_of_rows])) |> ignore
  polya__set_pv(self_, "array-of-polynomials", an_array) |> ignore
  let typ = polya__pv(self_, "type-of-polynomials")
  if eq(typ, q_kw_polynomial) {
    for i in 0..<number_of_rows {
      let poly = aref1(an_array, i)
      let a_row = convert_polynomial_to_vector(
        poly,
        polya__pv(self_, "table"),
        parts_of_monomial~,
      ).0
      aset1(polya__pv(self_, "rows"), i, a_row) |> ignore
      if polya__pv(self_, "verify-conversion").truthy() {
        check_conversion(poly, a_row, polya__pv(self_, "table")) |> ignore
      }
    }
  } else if eq(typ, q_kw_polynomial_vectors) {
    for i in 0..<number_of_rows {
      let poly_vector = make_one_dimensional(
        aref1(polya__pv(self_, "array-of-polynomials"), i),
      )
      aset1(polya__pv(self_, "array-of-polynomials"), i, poly_vector) |> ignore
      let a_row = make_array([length(poly_vector)], fill=0)
      aset1(polya__pv(self_, "rows"), i, a_row) |> ignore
      for ii in 0..<array_total_size(poly_vector) {
        let poly = aref1(poly_vector, ii)
        // (multiple-value (partial-row last-column-number)
        //   (convert-polynomial-to-vector poly (aref (pv-array-of-tables
        //   self) i) (pv-last-column-number self) parts-of-monomial))
        let (partial_row, lcn) = polya__multiple_value2("PARTIAL-ROW")
        last_column_number = lcn
        polya__set_pv(self_, "last-column-number", last_column_number)
        |> ignore
        if polya__pv(self_, "verify-conversion").truthy() {
          check_conversion(
            poly,
            partial_row,
            aref1(polya__pv(self_, "array-of-tables"), i),
          )
          |> ignore
        }
        for k in 0..<length(partial_row) {
          vector_push_extend(aref1(partial_row, k), a_row) |> ignore
        }
      }
    }
  }
  pv_check_type_of_entries(self_)
}

///|
let q_kw_polynomial_vectors : Value = kw("polynomial-vectors")

///|
fn check_conversion(polynomial : Value, row : Value, table : Value) -> Value raise {
  let poly = convert_polynomial_row(row, table)
  if equal(poly, polynomial) {
    format(t, "~%Checking polynomial ~A and table ~A. Conversion OK.", [
      row, table,
    ])
  } else {
    format(
      t,
      "~%The converted row ~A and the polynomial ~A with translation table\n     ~A do not agree.  They differ by ",
      [row, polynomial, table],
    )
    |> ignore
    displa(mul_star(list2(poly, add_star(list2(Fix(-1L), polynomial)))))
  }
}

///|
fn pv_check_type_of_entries(self_ : Value) -> Value raise {
  let m = symval(q_modulus)
  polya__set_pv(
    self_,
    "type-of-entries",
    if m.truthy() {
      m
    } else {
      q_kw_rational
    },
  )
  |> ignore
  let rows = polya__pv(self_, "rows")
  let nrows = length(rows)
  let mut done = false
  for ii in 0..<nrows {
    let a_row = aref1(rows, ii)
    let n = length(a_row)
    let mut i = 0
    while i < n {
      if aref1(a_row, i).truthy() && !numberp(aref1(a_row, i + 1)) {
        polya__set_pv(self_, "type-of-entries", q_kw_any_macsyma) |> ignore
        done = true
        break
      }
      i += 2
    }
    if done {
      break
    }
  }
  format(t, "~%Using entry type ~A.", [polya__pv(self_, "type-of-entries")])
}

///|
fn pv_set_up_hash_tables(self_ : Value) -> Value raise {
  let typ = polya__pv(self_, "type-of-polynomials")
  if eq(typ, q_kw_polynomial) {
    polya__set_pv(self_, "table", make_hash_table(kind=Equal))
  } else if eq(typ, q_kw_polynomial_vectors) {
    polya__set_pv(self_, "last-column-number", Fix(0L)) |> ignore
    let n = to_int(polya__pv(self_, "length-of-array-of-tables"))
    polya__set_pv(self_, "array-of-tables", make_array([n], fill=0)) |> ignore
    for i in 0..<n {
      ignore(i)
      vector_push_extend(
        make_hash_table(kind=Equal),
        polya__pv(self_, "array-of-tables"),
      )
      |> ignore
    }
    Nil
  } else {
    Nil
  }
}

///|
fn d_my_sum(
  quote_form : Value,
  quote_index : Value,
  start : Value,
  end? : Value = Nil,
) -> Value raise {
  // The loop variable IND is lexical in the Lisp code, so MEVAL of the
  // form does not see it.
  let quote_form = subst(q_ind, quote_index, quote_form)
  let start = meval(start)
  let end = meval(end)
  let answer = Collector::new()
  if end.truthy() {
    let mut ind = start
    while num_le(ind, end) {
      answer.add(meval(quote_form))
      ind = num_add(ind, Fix(1L))
    }
  } else {
    for ind in cdr(start).iter() {
      ignore(ind)
      answer.add(meval(quote_form))
    }
  }
  meval_star(cons(list1(q_mplus), answer.result()))
}

///|
fn d_list_dot(l : Value, ll : Value) -> Value raise {
  let c = Collector::new()
  let mut u = cdr(l)
  let mut v = cdr(ll)
  while u is Cons(_) && v is Cons(_) {
    c.add(mul_star(list2(car(u), car(v))))
    u = cdr(u)
    v = cdr(v)
  }
  add_star(c.result())
}

///|
fn permutations(a_list : Value, size? : Value) -> Value raise {
  let size = match size {
    Some(s) => to_int(s)
    None => length(a_list)
  }
  let mut answer = mapcar(u => list1(u), a_list)
  for i in 0..<(size - 1) {
    ignore(i)
    let c = Collector::new()
    for v in a_list.iter() {
      for perm in answer.iter() {
        if member_equal(v, perm) is Nil {
          c.add(cons(v, perm))
        }
      }
    }
    answer = c.result()
  }
  answer
}

///|
/// Will return the proper sign of a permutation of the first n
/// non-negative integers.
fn sign_of_permutation(perm_of_first_n_non_negative_integers : Value) -> Value raise {
  nsign_of_permutation(copy_list(perm_of_first_n_non_negative_integers))
}

///|
fn nsign_of_permutation(perm : Value) -> Value raise {
  let sub1_leng = length(perm) - 1
  if sub1_leng == 0 {
    Fix(1L)
  } else {
    let tem = car(last(perm))
    if eq(tem, int(sub1_leng)) {
      nsign_of_permutation(nbutlast(perm))
    } else {
      polya__nsubst(tem, int(sub1_leng), perm)
      num_neg(nsign_of_permutation(nbutlast(perm)))
    }
  }
}

///|
/// `(nsubst new old tree)` with the EQL test.
fn polya__nsubst(new_ : Value, old : Value, tree : Value) -> Unit {
  let mut v = tree
  while v is Cons(_) {
    if eql(car(v), old) {
      rplaca(v, new_) |> ignore
    } else if car(v) is Cons(_) {
      polya__nsubst(new_, old, car(v))
    }
    if eql(cdr(v), old) {
      rplacd(v, new_) |> ignore
      break
    }
    v = cdr(v)
  }
}

///|
fn d_make_art_q(indices : Value) -> Value raise {
  make_array(list_to_array(indices).map(x => to_int(x)))
}

///|
fn d_first_variable(monomial : Value) -> Value raise {
  if numberp(monomial) {
    return Nil
  }
  if atom(monomial) {
    return monomial
  }
  let headers = list([
    list2(q_mtimes, q_simp),
    list1(q_mtimes),
    list2(q_mexpt, q_simp),
    list2(q_mncexpt, q_simp),
    list1(q_mncexpt),
    list2(q_mnctimes, q_simp),
    list1(q_mnctimes),
  ])
  let products = list([
    list2(q_mtimes, q_simp),
    list1(q_mtimes),
    list2(q_mnctimes, q_simp),
    list1(q_mnctimes),
  ])
  for u in monomial.iter() {
    print(u) |> ignore
    if numberp(u) {
      ()
    } else if atom(u) {
      return u
    } else if member_equal(u, headers).truthy() {
      ()
    } else if member_equal(car(u), products).truthy() {
      return d_first_variable(cdr(u))
    } else {
      return second(u)
    }
  }
  Nil
}

///|
fn m_dot(l : Value) -> Value raise {
  simplifya(cons(list1(q_mnctimes), copy_list(l)), Nil)
}

///|
fn polya__split_x_y(terms : Value) -> Value raise {
  let mut x_terms : Value = Nil
  let mut y_terms : Value = Nil
  for u in terms.iter() {
    format(t, "~%For term ~A", [u]) |> ignore
    let fv = d_first_variable(u)
    if equal(fv, q_d_x) {
      x_terms = cons(u, x_terms)
    } else if equal(fv, q_d_y) {
      y_terms = cons(u, y_terms)
    } else {
      raise LispError::SimpleError(
        format_to_string("~A has first variable not x or y", [u]),
      )
    }
  }
  macsyma_list(list2(add_star(x_terms), add_star(y_terms)))
}

///|
fn d_convert_right_to_left(a : Value, b : Value) -> Value raise {
  let f = d_expand(
    add_star(list2(m_dot(list2(a, q_d_x)), m_dot(list2(b, q_d_y)))),
  )
  polya__split_x_y(list_terms(f))
}

///|
fn d_split_into_x_and_y(f : Value) -> Value raise {
  polya__split_x_y(list_terms(f))
}

///|
fn d_matrix_entry(x : Value, i : Value, j : Value) -> Value raise {
  nth(to_int(i), nth(to_int(j), x))
}

///|
fn initial_equal(list_a : Value, list_b : Value) -> Value raise {
  let mut u = list_a
  let mut v = list_b
  while u is Cons(_) && v is Cons(_) {
    if !eql(car(u), car(v)) {
      return Nil
    }
    u = cdr(u)
    v = cdr(v)
  }
  t
}

///|
fn initial_sublist(lista : Value, biglist : Value) -> Value raise {
  if length(biglist) < length(lista) {
    Nil
  } else {
    initial_equal(lista, biglist)
  }
}

///|
/// Replaces the pattern in ADP (a dot product) by replacement. When
/// inserted in the simplifier simpmnct it does the replacement whenever
/// called.
fn d_replace_the_pattern(
  adp : Value,
  pattern : Value,
  replacement : Value,
) -> Value raise {
  if atom(adp) {
    adp
  } else if equal(caar(adp), q_mnctimes) {
    let tem = ordered_sublist(cdr(pattern), cdr(adp))
    if tem.truthy() {
      ncmul_star(
        list3(ncmuln(car(tem), t), replacement, ncmuln(cadr(tem), t)),
      )
    } else {
      adp
    }
  } else {
    adp
  }
}

///|
fn dotsimp_one_term(monom : Value, coeff : Value, ignor : Value) -> Value raise {
  ignore(ignor)
  mul_star(list2(coeff, d_expand(d_dot_simp_monomial(monom))))
}

///|
fn dotsimp_atom(expr : Value) -> Value raise {
  let mut i = 1
  for u in cdr(symval(q_d_dot_simplifications)).iter() {
    if i % 2 == 1 && eq(u, expr) {
      return nth(i + 1, symval(q_d_dot_simplifications))
    }
    i += 1
  }
  expr
}

///|
fn check_rat_order(expr : Value, variables? : Value) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => symval(q_ear_troublesome_variables)
  }
  let mut expr = expr
  let mut maybe_out_of_order = false
  let mut nc_product_appeared = false
  if consp(expr) && d_ratp(expr).truthy() {
    for v in third(car(expr)).iter() {
      if fast_scalarp(v) is Nil {
        nc_product_appeared = true
      }
      if memq(v, variables).truthy() && nc_product_appeared {
        maybe_out_of_order = true
      }
    }
  }
  if maybe_out_of_order {
    nc_product_appeared = false
    maybe_out_of_order = false
    let mut v = third(car(expr))
    let mut w = fourth(car(expr))
    while v is Cons(_) && w is Cons(_) {
      if !atom(car(v)) && eq(caar(car(v)), q_mnctimes) {
        nc_product_appeared = true
      }
      if memq(car(v), variables).truthy() &&
        nc_product_appeared &&
        appears_in(cdr(expr), car(w)).truthy() {
        maybe_out_of_order = true
      }
      v = cdr(v)
      w = cdr(w)
    }
  }
  if maybe_out_of_order {
    nc_product_appeared = false
    let mut found = false
    let mut v = third(car(expr))
    let mut w = fourth(car(expr))
    while v is Cons(_) && w is Cons(_) {
      if !atom(car(v)) &&
        eq(caar(car(v)), q_mnctimes) &&
        appears_in(cdr(expr), car(w)).truthy() {
        nc_product_appeared = true
      }
      if memq(car(v), variables).truthy() &&
        nc_product_appeared &&
        appears_in(cdr(expr), car(w)).truthy() {
        found = true
        break
      }
      v = cdr(v)
      w = cdr(w)
    }
    if found {
      format(t, "~%~%~%*************Changing rat order", []) |> ignore
      // (beep) (break 'change)
      amacros__break("CHANGE") |> ignore
      expr = d_nc_rat(expr)
    }
  }
  expr
}

///|
fn get_varlist(expr : Value) -> Value raise {
  if d_ratp(expr).truthy() {
    third(car(expr))
  } else {
    Nil
  }
}

///|
/// The CHECK-NC-RAT-ORDER macro, on the value of the form.
fn check_nc_rat_order(expr : Value) -> Value raise {
  format(t, "~%checking order for ~A", [expr]) |> ignore
  check_rat_order(expr)
}

///|
fn varlist(expr : Value) -> Value raise {
  third(car(expr))
}

///|
fn genvar(expr : Value) -> Value raise {
  fourth(car(expr))
}

///|
/// The SHOW-VARLIST macro, on the value of the form.
fn show_varlist(expr : Value) -> Value raise {
  format(t, "~%The varlist for ~A is", [expr]) |> ignore
  gt(varlist(expr))
}

///|
/// Gives nil if monom not in radical otherwise gives the power it is in.
fn nil_radicalp(monom : Value) -> Value raise {
  let monom = if atom(monom) { list2(Nil, monom) } else { monom }
  if symval(q_d_radical).truthy() {
    let mut answer = 0
    for v in cdr(symval(q_d_radical)).iter() {
      for w in cdr(monom).iter() {
        if eq(w, v) {
          answer += 1
        }
      }
    }
    if answer == 0 {
      Nil
    } else {
      int(answer)
    }
  } else {
    Nil
  }
}

///|
fn in_nth_power_radical(monom : Value, n : Value) -> Value raise {
  let tem = nil_radicalp(monom)
  if tem.truthy() {
    lbool(num_gt(tem, num_sub(n, Fix(1L))))
  } else {
    Nil
  }
}

///|
/// `(string-trim "$" (string sym))` as CL prints it (upper case).
fn polya__dot_name(v : Value) -> String raise {
  string_trim("$", invert_case(lstring(string(v))))
}

///|
fn dot_show(nc_list : Value) -> Value raise {
  if atom(nc_list) {
    princ(nc_list)
  } else {
    format(t, "~A", [Str(polya__dot_name(second(nc_list)))]) |> ignore
    for v in cddr(nc_list).iter() {
      format(t, ".~A", [Str(polya__dot_name(v))]) |> ignore
    }
    Nil
  }
}

///|
fn new_rat_dotsimp(expr : Value) -> Value raise {
  let mut expr = expr
  let mut answer : Value = Fix(0L)
  format(t, "~%Beginnning to new-rat-dotsimp ", []) |> ignore
  if d_must_replacep(expr) is Nil {
    return header_poly(expr)
  }
  while d_zerop(expr) is Nil {
    amacros__show("ANSWER", answer)
    if d_must_replacep(expr) is Nil {
      return header_poly(n_plus(answer, expr))
    }
    // (setq-num-den the-num the-denom expr)
    let (the_num, the_denom) : (Value, Value) = if affine_polynomialp(expr).truthy() {
      (expr, Fix(1L))
    } else if rational_functionp(expr).truthy() {
      (num(expr), denom(expr))
    } else {
      fsignal(list1(Str("expr is supposed to be poly or rational-functionp")))
      |> ignore
      (Nil, Nil)
    }
    amacros__show("THE-NUM", the_num)
    if poly_scalarp(the_num).truthy() {
      answer = n_plus(answer, expr)
      return header_poly(answer)
    }
    let tem = get(car(the_num), q_disrep)
    if contains_a_zero_replacement(tem).truthy() {
      format(t, "~%Simplifying the worst monomial: ", []) |> ignore
      dot_show(tem) |> ignore
      expr = fifth(the_num)
      if expr is Nil {
        expr = Fix(0L)
      }
    } else if d_must_replacep(tem).truthy() {
      format(t, "~%Simplifying the worst monomial: ", []) |> ignore
      dot_show(tem) |> ignore
      let repl = n_star(list2(third(the_num), d_dot_simp_monomial(tem)))
      let the_rest = fifth(the_num)
      if the_rest.truthy() {
        amacros__show("THE-REST", the_rest)
        amacros__show("REPL", repl)
        expr = n_plus(the_rest, repl)
        amacros__show("EXPR", expr)
        expr = nred(expr, the_denom)
      } else {
        expr = nred(repl, the_denom)
      }
    } else {
      format(t, "~%Simplifying the worst monomial: ", []) |> ignore
      dot_show(tem) |> ignore
      format(t, "adding it to answer", []) |> ignore
      if fifth(the_num).truthy() {
        expr = nred(fifth(the_num), the_denom)
      } else {
        expr = Fix(0L)
      }
      answer = n_plus(answer, nred(subseq(the_num, 0, end=3), the_denom))
    }
  }
  header_poly(answer)
}

///|
fn rat_dotsimp(expr : Value) -> Value raise {
  let mut answer : Value = Fix(0L)
  format(t, "~%Beginning to rat-dotsimp..", []) |> ignore
  let mut expr = minimize_varlist(expr)
  while d_zerop(expr) is Nil && d_must_replacep(expr).truthy() {
    let (monom, cof, _) = polya__multiple_value3("MONOM")
    if d_must_replacep(monom).truthy() {
      expr = vsub_star(expr, vmul_star(list2(cof, monom)))
      let simped_monom = d_dot_simp_monomial(monom)
      let repl = vmul_star(list2(cof, simped_monom))
      if d_must_replacep(repl).truthy() {
        let tem = vadd_star(list2(repl, expr))
        expr = tem
      } else {
        answer = vadd_star(list2(repl, answer))
      }
    } else {
      let term = vmul_star(list2(cof, monom))
      expr = vsub_star(expr, term)
      answer = vadd_star(list2(term, answer))
    }
  }
  minimize_varlist(vadd_star(list2(expr, answer)))
}

///|
/// polya.lisp's $dotsimp. ndotsimp.lisp, loaded after polya.lisp,
/// redefines $dotsimp (d_dotsimp below), so this one is never called in
/// the Lisp image; its recursive calls go through the symbol, to the
/// ndotsimp version.
fn polya__dotsimp(expr : Value) -> Value raise {
  let mut expr = expr
  let mut answer : Value = Fix(0L)
  with_special(q_varlist, Nil, () => {
    if symval(q_d_fast_dotsimp).truthy() &&
      !(mbagp(expr).truthy() || d_ratp(expr).truthy()) {
      if symval(q_d_new_fast_dotsimp).truthy() {
        expr = d_new_rat(expr)
      } else {
        expr = d_vrat(expr)
      }
    }
    if !(atom(expr) ||
      symval(q_d_fast_dotsimp).truthy() ||
      d_ratp(expr).truthy()) {
      expr = d_multthru(d_ratsimp(d_expand(expr), Nil))
    }
    if atom(expr) {
      answer = dotsimp_atom(expr)
    } else if d_ratp(expr).truthy() {
      if symval(q_d_new_fast_dotsimp).truthy() {
        answer = new_rat_dotsimp(cdr(expr))
      } else {
        answer = rat_dotsimp(expr)
      }
    } else if mbagp(expr).truthy() {
      answer = cons(car(expr), mapcar(x => d_dotsimp(x), cdr(expr)))
    } else if member_equal(caar(expr), list2(q_mtimes, q_mnctimes)).truthy() {
      let (m, c, u) = find_worst_nc_monomial(expr)
      answer = dotsimp_one_term(m, c, u)
      if d_must_replacep(answer).truthy() {
        answer = d_dotsimp(answer)
      }
    } else if equal(caar(expr), q_mplus) {
      let mut prev_monom = q_zzzzz
      let mut the_count = 0
      while !(numberp(expr) && zerop(expr)) {
        the_count += 1
        if !atom(expr) {
          amacros__show("(LENGTH EXPR)", int(length(expr)))
        }
        let (monom, cof, term) = polya__multiple_value3("MONOM")
        if funcall(symval(q_d_order_function), [monom, prev_monom]) is Nil {
          amacros__show("PREV-MONOM", prev_monom)
          amacros__show("MONOM", monom)
          format(t, "****** out of order ****", []) |> ignore
          raise LispError::SimpleError("The function BEEP is undefined.")
        }
        prev_monom = monom
        if d_must_replacep(monom).truthy() {
          // the following expand may be unnecessary with dotdistrib at true.
          let mut repl = d_multthru(
            mul_star(list2(cof, d_expand(d_dot_simp_monomial(monom)))),
          )
          let mut troublesome = false
          for v in symval(q_ear_troublesome_variables).iter() {
            if appears_in(repl, v).truthy() {
              troublesome = true
              break
            }
          }
          if troublesome {
            format(t, "~%Ratsimping repl", []) |> ignore
            repl = d_multthru(d_ratsimp(repl, Nil))
          }
          expr = sub_star(expr, term)
          expr = add_star(list2(repl, expr))
        } else {
          if fast_scalarp(term).truthy() {
            expr = d_multthru(d_ratsimp(expr, Nil))
          }
          expr = sub_star(expr, term)
          answer = add_star(list2(answer, term))
        }
      }
      amacros__show("THE-COUNT", int(the_count))
    }
    answer
  })
}

///|
/// `$dotsimp` as defined by ndotsimp.lisp (which replaces polya.lisp's
/// definition when the affine package is loaded).
fn d_dotsimp(expr : Value) -> Value raise {
  if d_listp(expr).truthy() {
    cons(list1(q_mlist), mapcar(x => d_dotsimp(x), cdr(expr)))
  } else {
    let expr = if rational_functionp(expr).truthy() ||
      affine_polynomialp(expr).truthy() {
      expr
    } else {
      new_rat(expr)
    }
    header_poly(new_dotsimp(expr))
  }
}

///|
/// `(multiple-value (v1 v2 ...) form)`: MULTIPLE-VALUE is not defined in
/// Maxima, so the compiled Lisp code calls the function V1 (with the
/// values of V2 ...), which is undefined.
fn polya__multiple_value2(var_ : String) -> (Value, Value) raise {
  raise LispError::Condition(
    intern("undefined-function"),
    "The function MAXIMA::" + var_ + " is undefined.",
    sym(string_downcase(var_)),
  )
}

///|
fn polya__multiple_value3(var_ : String) -> (Value, Value, Value) raise {
  let (a, b) = polya__multiple_value2(var_)
  (a, b, Nil)
}

///|
fn remove_nth(n : Value, a_list : Value) -> Value raise {
  let n_ = to_int(n)
  if n_ == 0 {
    rplaca(a_list, cadr(a_list)) |> ignore
    rplacd(a_list, cddr(a_list)) |> ignore
    a_list
  } else if n_ < length(a_list) {
    rplacd(nthcdr(n_ - 1, a_list), nthcdr(n_ + 1, a_list)) |> ignore
    a_list
  } else {
    a_list
  }
}

///|
fn d_simp_ncmuln(a_list : Value, flag : Value) -> Value raise {
  if symval(q_d_free_dot).truthy() &&
    symval(q_d_dot_simplifications).truthy() {
    d_dotsimp(ncmuln(a_list, flag))
  } else {
    ncmuln(a_list, flag)
  }
}

///|
fn d_simp_ncmul(a_list : Value) -> Value raise {
  d_simp_ncmuln(copy_list(a_list), Nil)
}

///|
fn d_dncmul(f : Value, g : Value) -> Value raise {
  if d_plusp(f).truthy() {
    let vtemp = mapcar(v => d_dncmul(v, g), cdr(f))
    add(vtemp)
  } else if d_plusp(g).truthy() {
    let tem = mapcar(u => ncmul(list2(f, u)), cdr(g))
    add(tem)
  } else {
    ncmul(list2(f, g))
  }
}

///|
fn dotsimp2(expression : Value) -> Value raise {
  if atom(expression) {
    ()
  } else if equal(caar(expression), q_mnctimes) {
    return d_dot_simp_monomial(expression)
  } else {
    dotsimp1(expression) |> ignore
  }
  expression
}

///|
fn dotsimp1(expression : Value) -> Value raise {
  if atom(expression) {
    expression
  } else {
    rplaca(expression, d_dot_simp_monomial(car(expression))) |> ignore
    dotsimp1(car(expression)) |> ignore
    dotsimp1(cdr(expression))
  }
}

///|
fn d_dot_simp_monomial(monom : Value) -> Value raise {
  let init_monom = monom
  if atom(monom) {
    return dotsimp_atom(monom)
  }
  if atom(car(monom)) {
    return monom
  }
  if !equal(caar(monom), q_mnctimes) {
    return monom
  }
  if symval(q_d_dot_simplifications) is Nil {
    return init_monom
  }
  let answer = catch_tag(q_found_replace, () => {
    let mut monom = monom
    while monom.truthy() {
      let mut tem = cdr(symval(q_d_dot_simplifications))
      monom = cdr(monom)
      while tem.truthy() {
        if symval(q_d_new_fast_dotsimp).truthy() &&
          (eql(Fix(0L), second(tem)) || eq(rzero(), cdr(second(tem)))) {
          tem = cddr(tem)
        } else {
          let mut pattern = car(tem)
          if atom(pattern) {
            if member_equal(pattern, monom).truthy() {
              // we have to handle the case of an atomic pattern by making it
              // a standard list '(nonsense)
              pattern = list1(pattern)
            } else {
              pattern = symval(q_ear_nonsense)
            }
          } else {
            pattern = cdr(pattern)
          }
          tem = cdr(tem)
          let replacement = car(tem)
          tem = cdr(tem)
          if initial_sublist(pattern, monom).truthy() {
            let tema = subseq(
              cdr(init_monom),
              0,
              end=length(init_monom) - length(monom) - 1,
            )
            let answer = if symval(q_d_new_fast_dotsimp).truthy() {
              new_rat_ncmul1(
                ncmuln(tema, t),
                replacement,
                ncmuln(nthcdr(length(pattern), monom), t),
              )
            } else {
              rat_ncmul(
                list3(
                  ncmuln(tema, t),
                  replacement,
                  ncmuln(nthcdr(length(pattern), monom), t),
                ),
              )
            }
            throw_tag(q_found_replace, answer) |> ignore
          }
        }
      }
    }
    Nil
  })
  if answer.truthy() {
    answer
  } else {
    init_monom
  }
}

///|
/// A Lisp macro (unevaluated arguments): `declare_order_weights(x, 2, ...)`.
fn d_declare_order_weights(l : Value) -> Value raise {
  let n = length(l)
  let mut i = 0
  while i < n {
    putprop(nth(i, l), nth(i + 1, l), amacros__q_kw_order_weight) |> ignore
    i += 2
  }
  Nil
}

///|
/// A Lisp macro (unevaluated arguments): `declare_weights(x, 2, ...)`.
fn d_declare_weights(l : Value) -> Value raise {
  let n = length(l)
  let mut i = 0
  while i < n {
    putprop(nth(i, l), nth(i + 1, l), q_kw_weight) |> ignore
    i += 2
  }
  Nil
}

///|
fn d_dot_productp(x : Value) -> Value raise {
  if atom(x) {
    Nil
  } else if atom(car(x)) {
    Nil
  } else {
    lbool(equal(caar(x), q_mnctimes))
  }
}

///|
fn d_dot(l : Value) -> Value raise {
  m_dot(l)
}

///|
/// Like $coeff except it always works on general rep, and if x is 1 it
/// picks the scalar part.
fn d_my_coeff(f : Value, x : Value) -> Value raise {
  let f = if d_ratp(f).truthy() { d_ratsimp(f, Nil) } else { f }
  if atom(f) {
    if equal(f, x) {
      Fix(1L)
    } else {
      Fix(0L)
    }
  } else if equal(f, x) {
    Fix(1L)
  } else if eq(caar(f), q_mtimes) {
    if member_equal(x, f).truthy() {
      polyc__delete_equal(x, copy_list(f))
    } else if equal(x, Fix(1L)) && d_scalarp(f).truthy() {
      f
    } else {
      Fix(0L)
    }
  } else if memq(caar(f), list3(q_mplus, q_mlist, q_mequal)).truthy() {
    simplifya(
      cons(list1(caar(f)), mapcar(y => d_my_coeff(y, x), cdr(f))),
      Nil,
    )
  } else {
    Nil
  }
}

///|
fn d_ncoeff(f : Value, x : Value, exponent? : Value = Fix(1L)) -> Value raise {
  if eql(x, Fix(1L)) {
    d_my_coeff(f, x)
  } else if equal(exponent, Fix(1L)) {
    d_coeff(f, x)
  } else {
    d_coeff(f, x, n=exponent)
  }
}

///|
fn d_matrix_equationp(expr : Value) -> Value raise {
  let m = d_matrixp(expr)
  if m.truthy() {
    m
  } else if !atom(expr) &&
    eq(caar(expr), q_mequal) &&
    !atom(second(expr)) {
    d_matrixp(second(expr))
  } else {
    Nil
  }
}
