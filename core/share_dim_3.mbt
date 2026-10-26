// Port of share/affine/dim-3.lisp: utilities for the dimension-3 algebra
// computations (tensors, matrices, traces, normalizing elements).
//
// Notes:
// - `swapf` and `seta` are called by the Lisp code but defined nowhere in
//   Maxima: they are undefined-function calls there, so they are made as
//   `funcall`s of the undefined symbols here too.
// - `tr`, `vars`, `gen` and `degs` are free (global) variables in the
//   Lisp code: their global values are set.
// - The sparse matrix accessors `sp-column-used-in-row` and
//   `sp-constants-column` (sparsemat.lisp, a `:named` defstruct) are slots
//   16 and 32 of the `sparse-matrix` structure.

// ---------------------------------------------------------------------------
// Symbols without generated constants

///|
let dim_3__q_tr : Value = sym("tr")

///|
let dim_3__q_swapf : Value = sym("swapf")

///|
let dim_3__q_seta : Value = sym("seta")

///|
let dim_3__q_all_dotsimp_denoms : Value = sym("*all-dotsimp-denoms*")

///|
/// `'(lambda (i j) ($concat '$u i j))` of `$half_quantum_rels`.
let dim_3__lit_concat_u : Value = try! lread(
  "(lambda (i j) ($concat (quote $u) i j))",
)

///|
/// The pairs of `(loop for a in l1 for b in l2 ...)`.
fn dim_3__zip(l1 : Value, l2 : Value) -> Array[(Value, Value)] {
  let r = []
  let mut a = l1
  let mut b = l2
  while consp(a) && consp(b) {
    r.push((car(a), car(b)))
    a = cdr(a)
    b = cdr(b)
  }
  r
}

///|
/// `(ncmul* a b)` (amacros.lisp).
fn dim_3__ncmul2(a : Value, b : Value) -> Value raise {
  ncmul2_star(a, b)
}

///|
/// `(ncmul* a b c)` (amacros.lisp).
fn dim_3__ncmul3(a : Value, b : Value, c : Value) -> Value raise {
  ncmuln(list([a, b, c]), Nil)
}

///|
/// `(n* a b)`
fn dim_3__ntimes(a : Value, b : Value) -> Value raise {
  n_star(list2(a, b))
}

///|
/// `(assert form)`
fn dim_3__assert(ok : Bool, form : String) -> Unit raise {
  if !ok {
    raise LispError::SimpleError("The assertion " + form + " failed.")
  }
}

///|
/// Value of a global (non-declared) variable; unbound is an error.
fn dim_3__global(s : Value) -> Value raise {
  if !boundp(s) {
    raise LispError::SimpleError(
      format_to_string("The variable ~S is unbound.", [s]),
    )
  }
  symval(s)
}

///|
/// `(y-or-n-p ctl)` on the query stream: ask until the answer starts with
/// y or n.
fn dim_3__y_or_n_p(ctl : String) -> Bool raise {
  while true {
    format(t, "~%" + ctl + " (y or n) ", []) |> ignore
    match read_line(stream=symval(standard_input)) {
      None => raise LispError::SimpleError("y-or-n-p: end of file")
      Some(line) => {
        let s = string_trim(" \t", line)
        if s.length() > 0 {
          let c = s.get_char(0).unwrap()
          if c == 'y' || c == 'Y' {
            return true
          }
          if c == 'n' || c == 'N' {
            return false
          }
        }
        format(t, "Please type \"y\" for yes or \"n\" for no. ", []) |> ignore
      }
    }
  }
  false
}

///|
/// `(matrix-p x)` of the list-type named `matrix` structure.
fn dim_3__matrix_p(x : Value) -> Bool {
  consp(x) && eq(car(x), q_matrix)
}

///|
fn point_of_tensors(
  special_tensor : Value,
  standard_tensor : Value,
  nc_monomials? : Value,
) -> Value raise {
  let nc_monomials = match nc_monomials {
    Some(v) => v
    None => d_list_nc_monomials(standard_tensor)
  }
  let st_tensor = st_rat(standard_tensor)
  let sp_tensor = st_rat(special_tensor)
  let mut nc_monoms = st_rat(nc_monomials)
  nc_monoms = sort_list(nc_monoms, (a, b) => alphalessp(a, b).truthy())
  let variable_names = Collector::new()
  let variable_values = Collector::new()
  for v in nc_monoms.iter() {
    variable_names.add(pcoeff(st_tensor, v))
    variable_values.add(pcoeff(sp_tensor, v))
  }
  let result = Collector::new()
  for vw in dim_3__zip(variable_names.result(), variable_values.result()) {
    let (vv, ww) = vw
    if consp(vv) && affine_polynomialp(vv).truthy() && length(vv) == 3 {
      result.add(cons(car(vv), ww))
    }
  }
  result.result()
}

///|
fn gen_matrix_rows(mat : Value) -> Value raise {
  if dim_3__matrix_p(mat) {
    cdr(mat)
  } else if d_matrixp(mat).truthy() {
    mapcar(x => cdr(x), cdr(mat))
  } else {
    merr("not a matrix", [])
  }
}

///|
fn dim_3__append_all(lists : Value) -> Value {
  let mut acc : Value = Nil
  for l in reverse(lists).iter() {
    acc = append(l, acc)
  }
  acc
}

///|
fn point_of_algebras(
  special_tensor : Value,
  standard_tensor : Value,
  q : Value,
  standard_q : Value,
) -> Value raise {
  let tensor_subs = point_of_tensors(special_tensor, standard_tensor)
  let vs = mapcar(x => st_rat(x), dim_3__append_all(gen_matrix_rows(q)))
  let ws = mapcar(
    x => st_rat(x),
    dim_3__append_all(gen_matrix_rows(standard_q)),
  )
  let c = Collector::new()
  let mut vl = vs
  let mut wl = ws
  while consp(vl) && consp(wl) {
    c.add(cons(car(car(wl)), car(vl)))
    vl = cdr(vl)
    wl = cdr(wl)
  }
  append(tensor_subs, c.result())
}

///|
fn d_dimensions_for_replacements(
  d_repl_list : Value,
  degree? : Value = Fix(7L),
) -> Value raise {
  let ds = Collector::new()
  for v in cdr(d_repl_list).iter() {
    ds.add(v)
    ds.add(int(0))
  }
  let dot_simps = cons(list1(q_mlist), ds.result())
  let current = d_list_variables(d_repl_list, Nil)
  with_specials(
    [(q_d_dot_simplifications, dot_simps), (q_d_current_variables, current)],
    () => {
      let n = to_int(degree)
      for i in 0..<n {
        format(t, "~%The dimension in deg ~A is ~A and hilbert is ~A", [
          d_length(d_mono(symval(q_d_current_variables), int(i))),
          int(i),
          hilbert(int(i), Nil),
        ])
        |> ignore
      }
      Nil
    },
  )
}

///|
fn d_normalizing_element_p(elmt : Value) -> Value raise {
  let final_ = Collector::new()
  for v in cdr(symval(q_d_current_variables)).iter() {
    let a = dim_3__ncmul2(v, elmt)
    let oth = d_general_sum(
      symval(q_d_current_variables),
      coefficients=symval(q_d_aaaa),
    ).0
    let tem = sub_star(a, dim_3__ncmul2(elmt, oth))
    let answ = d_totaldisrep(d_numerator(d_dotsimp(tem)))
    let eqns = d_extract_linear_equations(list2(list1(q_mlist), answ))
    let solns = d_fast_linsolve(
      eqns,
      variables=subseq(
        symval(q_d_aaaa),
        0,
        end=length(symval(q_d_current_variables)),
      ),
    )
    final_.add(d_sublis(solns, oth))
    sheafa__mshow("(CONS '(MLIST) FINAL)", cons(list1(q_mlist), final_.result()))
  }
  cons(list1(q_mlist), final_.result())
}

///|
fn collect_atoms(tree : Value, pred? : Value) -> Value raise {
  let pred = match pred {
    Some(p) => p
    None => lfunc("collect-atoms-pred", _ => t)
  }
  with_special(q_result, Nil, () => {
    collect_atoms1(tree, pred) |> ignore
    symval(q_result)
  })
}

///|
fn collect_atoms1(tree : Value, pred : Value) -> Value raise {
  if atom(car(tree)) {
    if funcall(pred, [car(tree)]).truthy() {
      if member_equal(car(tree), symval(q_result)) is Nil {
        set(q_result, cons(car(tree), symval(q_result))) |> ignore
      }
    }
  } else {
    collect_atoms1(car(tree), pred) |> ignore
  }
  if atom(cdr(tree)) {
    if funcall(pred, [cdr(tree)]).truthy() {
      if member_equal(cdr(tree), symval(q_result)) is Nil {
        set(q_result, cons(cdr(tree), symval(q_result)))
      } else {
        Nil
      }
    } else {
      Nil
    }
  } else {
    collect_atoms1(cdr(tree), pred)
  }
}

///|
fn d_find_coefficients_for_linear_combination(
  items : Value,
  in_terms_of : Value,
  monoms : Value,
  cofs? : Value,
) -> Value raise {
  let mut cofs = match cofs {
    Some(c) => c
    None => symval(q_d_aaaa)
  }
  let mut items = items
  let mut in_terms_of = in_terms_of
  let mut gen_sum = int(0)
  let mut final_answ : Value = Nil
  let monoms = nreverse(st_rat(monoms))
  while true {
    in_terms_of = cdr(in_terms_of)
    if in_terms_of is Nil {
      break
    }
    cofs = cdr(cofs)
    gen_sum = n_plus(gen_sum, dim_3__ntimes(car(cofs), car(in_terms_of)))
  }
  while true {
    items = cdr(items)
    if items is Nil {
      break
    }
    let dif = n__(car(items), gen_sum)
    let mut answ : Value = Nil
    let mut rest_monoms = monoms
    while true {
      let mut tem = car(rest_monoms)
      if tem is Nil {
        break
      }
      rest_monoms = cdr(rest_monoms)
      if rest_monoms is Nil {
        break
      }
      tem = gencoeff(dif, tem)
      answ = cons(new_disrep(tem), answ)
    }
    final_answ = cons(cons(list1(q_mlist), answ), final_answ)
  }
  cons(list1(q_mlist), final_answ)
}

///|
fn d_generate_matrix(fun : Value, i : Value, j : Value) -> Value raise {
  let rows = Collector::new()
  let ni = to_int(i)
  let nj = to_int(j)
  for ii in 1..=ni {
    let row = Collector::new()
    for jj in 1..=nj {
      row.add(meval_star(list3(list1(fun), int(ii), int(jj))))
    }
    rows.add(cons(list1(q_mlist), row.result()))
  }
  cons(list1(q_d_matrix), rows.result())
}

///|
/// Form row1+row2 where you may specify multiples.
fn gen_matrix_row_plus(
  row1 : Value,
  row2 : Value,
  row1_multiple? : Value = Nil,
  row2_multiple? : Value = Nil,
) -> Value raise {
  let mut row1_multiple = row1_multiple
  let mut row2_multiple = row2_multiple
  if row1_multiple.truthy() {
    row1_multiple = st_rat(row1_multiple)
  }
  if row1_multiple.truthy() {
    row2_multiple = st_rat(row2_multiple)
  }
  let result = Collector::new()
  for vw in dim_3__zip(cdr(row1), cdr(row2)) {
    let (v, w) = vw
    let mut v = v
    let mut w = w
    if row1_multiple.truthy() {
      v = dim_3__ntimes(row1_multiple, v)
    }
    if row2_multiple.truthy() {
      w = dim_3__ntimes(row2_multiple, w)
    }
    result.add(n_plus(v, w))
  }
  cons(list1(q_mlist), result.result())
}

///|
fn d_interchange_matrix_columns(
  matrix : Value,
  i : Value,
  j : Value,
  copy_? : Value = Nil,
) -> Value raise {
  let mut matrix = matrix
  if copy_.truthy() {
    let max = to_int(num_max(i, j)) + 1
    let rows = Collector::new()
    for u in cdr(matrix).iter() {
      rows.add(nconc(subseq(u, 0, end=max), nthcdr(max, u)))
    }
    matrix = cons(car(matrix), rows.result())
  }
  for u in cdr(matrix).iter() {
    funcall(dim_3__q_swapf, [nth(to_int(i), u), nth(to_int(j), u)]) |> ignore
  }
  matrix
}

///|
/// Interchange MATRIX rows I and J.  If COPY then copy then don't do it
/// destructively.
fn d_interchange_matrix_rows(
  matrix : Value,
  i : Value,
  j : Value,
  copy_? : Value = Nil,
) -> Value raise {
  let mut matrix = matrix
  if copy_.truthy() {
    let c = to_int(num_max(i, j)) + 1
    matrix = nconc(subseq(matrix, 0, end=c), nthcdr(c, matrix))
  }
  funcall(dim_3__q_swapf, [nth(to_int(i), matrix), nth(to_int(j), matrix)])
  |> ignore
  matrix
}

///|
/// `(matrix-entry matrix i j)` = `(nth j (nth i matrix))`.
fn matrix_entry(matrix : Value, i : Value, j : Value) -> Value raise {
  nth(to_int(j), nth(to_int(i), matrix))
}

///|
fn d_multiply_row(list_ : Value, factor : Value) -> Value raise {
  cons(car(list_), mapcar(v => dim_3__ntimes(factor, v), cdr(list_)))
}

///|
fn dim_3__set_nth(i : Int, l : Value, v : Value) -> Unit raise {
  let cell = nthcdr(i, l)
  if cell is Nil {
    raise LispError::SimpleError(
      format_to_string("~A is too large an index for SETF of NTH.", [int(i)]),
    )
  }
  setf_car(cell, v) |> ignore
}

///|
/// Write MATRIX as a product of P.DIAGONAL.TRANSPOSE(P).  This returns
/// value P.  (Still must remove the factors along the diagonal.)
fn d_decompose_symmetric_matrix(matrix : Value) -> Value raise {
  let ident = d_ident(d_length(matrix))
  let matrix = cons(car(matrix), mapcar(v => copy_list(v), cdr(matrix)))
  let len = to_int(d_length(matrix))
  let me = (i : Int, j : Int) => nth(j, nth(i, matrix))
  for ii in 1..<len {
    let mut found = false
    for i in ii..=len {
      if !pzerop(me(i, ii)).truthy() {
        if i == ii {
          found = true
          break
        } else {
          dim_3__set_nth(
            ii,
            matrix,
            gen_matrix_row_plus(nth(i, matrix), nth(ii, matrix)),
          )
          dim_3__set_nth(
            ii,
            ident,
            gen_matrix_row_plus(nth(i, ident), nth(ii, ident)),
          )
          for i1 in ii..=len {
            dim_3__set_nth(ii, nth(i1, matrix), n_plus(me(i1, ii), me(i1, i)))
          }
          found = true
          break
        }
      }
    }
    if !found {
      fsignal(list1(Str("This implementation assumes the matrix is nonsingular")))
      |> ignore
    }
    let mut fact = nred(int(1), me(ii, ii))
    let pivot_row = d_multiply_row(nth(ii, matrix), fact)
    let ident_pivot_row = d_multiply_row(nth(ii, ident), fact)
    for i in (ii + 1)..=len {
      fact = dim_3__ntimes(int(-1), me(i, ii))
      dim_3__set_nth(
        i,
        matrix,
        gen_matrix_row_plus(nth(i, matrix), pivot_row, row2_multiple=fact),
      )
      dim_3__set_nth(
        i,
        ident,
        gen_matrix_row_plus(nth(i, ident), ident_pivot_row, row2_multiple=fact),
      )
    }
  }
  d_new_disrep(ident)
}

///|
fn d_new_disrep(item : Value) -> Value raise {
  if atom(item) {
    new_disrep(item)
  } else if listp(car(item)) && mbagp(item).truthy() {
    cons(car(item), mapcar(x => d_new_disrep(x), cdr(item)))
  } else {
    new_disrep(item)
  }
}

///|
/// Generate the matrix of symbols starting with SYMBOL with ROWS rows and
/// COLUMNS columns.
fn d_symbol_matrix(symbol : Value, rows : Value, columns : Value) -> Value raise {
  let rs = Collector::new()
  for i in 1..=to_int(rows) {
    let tem = Collector::new()
    for j in 1..=to_int(columns) {
      tem.add(d_concat(list([symbol, int(i), int(j)])))
    }
    rs.add(cons(list2(q_mlist, q_simp), tem.result()))
  }
  cons(list2(q_d_matrix, q_simp), rs.result())
}

///|
fn replace_symbols(
  form : Value,
  containing_string : Value,
  prefix? : Value = Nil,
  replacements? : Value = Nil,
) -> Value raise {
  let vari = d_list_variables(form, list1(containing_string))
  let subs = if prefix.truthy() {
    mapcar(v => cons(v, d_concat(list2(prefix, v))), cdr(vari))
  } else {
    check_arg(
      replacements,
      lbool(
        listp(replacements) &&
        !num_lt(d_length(replacements), d_length(vari)),
      ),
      list1(Str("long enough macsyma-list")),
    )
    |> ignore
    if prefix.truthy() {
      setf_cdr(vari, sort_list(cdr(vari), (a, b) => alphalessp(a, b).truthy()))
      |> ignore
    }
    // pairlis (SBCL pushes the pairs, so the alist is reversed)
    let keys = cdr(vari)
    let data = subseq(cdr(replacements), 0, end=to_int(d_length(vari)))
    if length(keys) != length(data) {
      raise LispError::SimpleError(
        "The lists of keys and data are of unequal length.",
      )
    }
    let mut alist : Value = Nil
    for kd in dim_3__zip(keys, data) {
      let (k, d) = kd
      alist = cons(cons(k, d), alist)
    }
    alist
  }
  sublis(subs, form)
}

///|
fn check_cases(roots_of_one : Value) -> Value raise {
  for v in cdr(roots_of_one).iter() {
    let relats = subst(v, q_d_b, symval(q_d_relationsb))
    d_set_up_dot_simplifications(relats) |> ignore
    for i in [2, 5, 10, 3, 4] {
      d_check_overlaps(int(i + 1), add_to_simps=t, maybe_reset=Nil) |> ignore
      set(
        q_d_centrals_so_far,
        cons(
          d_fast_central_elements(symval(q_d_current_variables), int(i)),
          symval(q_d_centrals_so_far),
        ),
      )
      |> ignore
      displa(cons(list1(q_mlist), symval(q_d_centrals_so_far))) |> ignore
    }
  }
  Nil
}

///|
fn check_centrals(
  in_degree : Value,
  relations? : Value = Nil,
  set_up? : Value = Nil,
) -> Value raise {
  if set_up.truthy() {
    d_set_up_dot_simplifications(relations) |> ignore
  }
  for i in in_degree.iter() {
    d_check_overlaps(num_add(i, int(1)), add_to_simps=t, maybe_reset=Nil)
    |> ignore
    set(
      q_d_centrals_so_far,
      cons(
        d_fast_central_elements(symval(q_d_current_variables), i),
        symval(q_d_centrals_so_far),
      ),
    )
    |> ignore
    displa(cons(list1(q_mlist), symval(q_d_centrals_so_far))) |> ignore
  }
  Nil
}

///|
fn d_check_transpose_condition_2_1(
  mm : Value,
  q : Value,
  variables? : Value,
) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  let he = dim_3__ncmul2(variables, mm)
  sub_star(he, d_transpose(dim_3__ncmul3(q, mm, d_transpose(variables))))
}

///|
fn d_m_from_f(f : Value) -> Value raise {
  let mut n : Value = Nil
  for v in cdr(f).iter() {
    if !numberp(v) {
      n = d_nc_degree(v)
      break
    }
  }
  let monoms = d_mono(symval(q_d_current_variables), num_sub(n, int(1)))
  let rows = Collector::new()
  for fi in cdr(f).iter() {
    let row = Collector::new()
    for v in cdr(symval(q_d_current_variables)).iter() {
      let mut answ = int(0)
      for w in cdr(monoms).iter() {
        answ = add_star(
          list2(
            answ,
            mul_star(list2(d_ratcoef(fi, dim_3__ncmul2(w, v)), w)),
          ),
        )
      }
      row.add(answ)
    }
    rows.add(cons(list1(q_mlist), row.result()))
  }
  cons(list1(q_d_matrix), rows.result())
}

///|
fn d_diagonal(lis : Value) -> Value raise {
  let rows = Collector::new()
  let n = length(cdr(lis))
  let mut i = 0
  for v in cdr(lis).iter() {
    let tem = Collector::new()
    for k in 0..<n {
      tem.add(if k == i { v } else { int(0) })
    }
    rows.add(cons(list1(q_mlist), tem.result()))
    i += 1
  }
  cons(list2(q_d_matrix, q_simp), rows.result())
}

///|
fn d_dim3_relations(type_ : Value, number_variables : Value) -> Value raise {
  let mut mat : Value = Nil
  let subs_and_relations = if eql(number_variables, int(2)) {
    let rels = symval(q_d_relations_2)
    mat = symval(q_d_rtx)
    set(q_vars, list([list1(q_mlist), q_d__pctalpha, q_d__pctbeta])) |> ignore
    if eq(type_, q_d_a) {
      nth(1, rels)
    } else if eq(type_, q_d_e) {
      nth(2, rels)
    } else if eq(type_, q_d_h) {
      nth(3, rels)
    } else if eq(type_, q_d_s1) {
      nth(4, rels)
    } else if eq(type_, q_d_s2) {
      nth(5, rels)
    } else if eq(type_, q_d_s2p) {
      nth(6, rels)
    } else {
      fsignal(list1(Str("type one of a,b,h,s1,s2,or s2p")))
    }
  } else if eql(number_variables, int(3)) {
    let rels = symval(q_d_relations_3)
    set(
      q_vars,
      list([list1(q_mlist), q_d__pctalpha, q_d__pctbeta, q_d__pctgamma]),
    )
    |> ignore
    mat = symval(q_d_rtx3)
    if eq(type_, q_d_a) {
      nth(1, rels)
    } else if eq(type_, q_d_b) {
      nth(2, rels)
    } else if eq(type_, q_d_e) {
      nth(3, rels)
    } else if eq(type_, q_d_h) {
      nth(4, rels)
    } else if eq(type_, q_d_s1) {
      nth(5, rels)
    } else if eq(type_, q_d_s1p) {
      nth(6, rels)
    } else if eq(type_, q_d_s1pp) {
      nth(7, rels)
    } else if eq(type_, q_d_s2) {
      nth(8, rels)
    } else {
      fsignal(list1(Str("type one of a,b,e,h,s1,s1p,s1pp,  or s2p")))
    }
  } else {
    Nil
  }
  d_totaldisrep(
    d_sub_list(
      list2(
        list1(q_mlist),
        list3(
          list1(q_mequal),
          symval(q_vars),
          second(subs_and_relations),
        ),
      ),
      d_list_matrix_entries(dim_3__ncmul2(third(subs_and_relations), mat)),
    ),
  )
}

///|
fn d_maybe_ldata_solve(
  eqns : Value,
  inequality? : Value = Fix(1L),
  yes? : Value = Nil,
) -> Value raise {
  set(q_d_last_equations, eqns) |> ignore
  format(t, "The value of Last_equations is :..", []) |> ignore
  displa(eqns) |> ignore
  if yes.truthy() || dim_3__y_or_n_p("solve the system") {
    let ld = sheafa__make_ldata(eqns=st_rat(eqns))
    set(q_d_answer, simplify_ldata(ld, open_g=st_rat(inequality))) |> ignore
    set(
      q_d_answer,
      delete_redundant_ldata(symval(q_d_answer), ignore_ldata_inequalities=t),
    )
    |> ignore
    format(t, "~%**The final answer is (stored in $answer) :", []) |> ignore
    d_ldata_disrep(symval(q_d_answer))
  } else {
    eqns
  }
}

///|
/// Find the conditions for an ELEMENT or if element is a number for the
/// general nc-polynomial in that degree to be normalized.  You may supply
/// the optional equations for the automorphism group of the algebra to
/// assist in the computation.  The current variables and dotsimps are
/// used.
fn d_normalizing_conditions(
  deg_or_element : Value,
  auto_data? : Value = Nil,
) -> Value raise {
  if numberp(deg_or_element) {
    set(
      q_gen,
      d_general_sum(
        d_mono(symval(q_d_current_variables), deg_or_element),
        coefficients=symval(q_d_bbbb),
      ).0,
    )
    |> ignore
  } else {
    set(q_gen, deg_or_element) |> ignore
  }
  let rows = Collector::new()
  for v in cdr(symval(q_d_current_variables)).iter() {
    let gen = symval(q_gen)
    let a = dim_3__ncmul2(v, gen)
    let b = dim_3__ncmul2(
      gen,
      d_scalar_sum(
        d_concat(list2(q_d_c, string_grind(v))),
        symval(q_d_current_variables),
      ).0,
    )
    rows.add(sub_star(a, b))
  }
  let mut tem = cons(list1(q_mlist), rows.result())
  sheafa__mshow("TEM", tem)
  tem = d_dotsimp(tem)
  sheafa__mshow("TEM", tem)
  let eqns = d_extract_linear_equations(d_totaldisrep(d_numerator(tem)))
  if auto_data.truthy() {
    let all = Collector::new()
    for v in cdr(auto_data).iter() {
      all.add(d_maybe_ldata_solve(d_append(list2(v, eqns)), yes=t))
    }
    d_append(all.result())
  } else {
    d_maybe_ldata_solve(eqns)
  }
}

///|
fn d_ldata_disrep(lis : Value) -> Value raise {
  if ldatap(lis).truthy() {
    cons(list1(q_mlist), mapcar(v => new_disrep(v), sheafa__ldata_eqns(lis)))
  } else if ldatap(car(lis)).truthy() {
    cons(list1(q_mlist), mapcar(x => d_ldata_disrep(x), lis))
  } else {
    fsignal(list1(Str("ldata_disrep only ldata or lists of ldata")))
  }
}

///|
fn d_linear_automorphism_group(
  relations? : Value,
  set_up_simps? : Value = Nil,
  variables? : Value,
) -> Value raise {
  let relations = match relations {
    Some(r) => r
    None => d_relations_from_dot_simps()
  }
  let variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  sheafa__mshow("RELATIONS", relations)
  if !variables.truthy() {
    funcall(dim_3__q_seta, [
      symval(q_d_current_variables),
      funcall(sym("$list_nc_variables"), [relations]),
    ])
    |> ignore
  }
  sheafa__mshow("$CURRENT_VARIABLES", symval(q_d_current_variables))
  if set_up_simps.truthy() {
    let mut deg : Value = Nil
    for r in cdr(relations).iter() {
      let d = d_nc_degree(r)
      deg = if deg is Nil { d } else { num_max(deg, d) }
    }
    if deg is Nil {
      raise LispError::SimpleError("invalid number of arguments: 0")
    }
    d_set_up_dot_simplifications(relations, check_thru_deg=deg) |> ignore
  }
  let subs = mapcar(
    v => d_scalar_sum(d_concat(list2(q_d_c, string_grind(v))), variables).0,
    cdr(variables),
  )
  sheafa__mshow("(CONS '(MLIST) SUBS)", cons(list1(q_mlist), subs))
  let mat = d_coefmatrix(cons(list1(q_mlist), subs), variables)
  let ss = Collector::new()
  for vw in dim_3__zip(cdr(variables), subs) {
    let (v, w) = vw
    ss.add(list3(list1(q_mequal), v, w))
  }
  let subs_for_sublis = cons(list1(q_mlist), ss.result())
  sheafa__mshow("SUBS-FOR-SUBLIS", subs_for_sublis)
  let image = d_dotsimp(d_expand(d_sublis(subs_for_sublis, relations)))
  let eqns = d_extract_linear_equations(d_totaldisrep(d_numerator(image)))
  d_maybe_ldata_solve(eqns, inequality=d_determinant(mat))
}

///|
/// `(defremember $dotsimp_remember (elmnt &optional ($dot_simplifications
/// $dot_simplifications)) ($dotsimp elmnt))`: the optional parameter binds
/// the special `$dot_simplifications` and is part of the hash key.
fn dim_3__dotsimp_remember(
  elmnt : Value,
  dot_simplifications? : Value,
) -> Value raise {
  let ds = match dot_simplifications {
    Some(v) => v
    None => symval(q_d_dot_simplifications)
  }
  with_special(q_d_dot_simplifications, ds, () => sheafa__remember(
    q_d_dotsimp_remember,
    list2(elmnt, symval(q_d_dot_simplifications)),
    () => d_dotsimp(elmnt),
  ))
}

///|
fn d_algebra_trace(element : Value, basis : Value) -> Value raise {
  let rbasis = st_rat(basis)
  let vs = Collector::new()
  for v in rbasis.iter() {
    if listp(v) {
      vs.add(car(v))
      dim_3__assert(
        get(car(v), q_disrep).truthy(),
        "(GET (CAR V) 'DISREP)",
      )
    }
  }
  set(q_vars, vs.result()) |> ignore
  let mut tra = int(0)
  for vrv in dim_3__zip(cdr(basis), rbasis) {
    let (v, rv) = vrv
    sheafa__show("V", v)
    sheafa__show("RV", rv)
    sheafa__show("V", v)
    let tem = dim_3__dotsimp_remember(dim_3__ncmul2(element, v))
    let den = function_denominator(tem)
    let num = function_numerator(tem)
    let cof = pcoeff(num, rv, variables_to_exclude_from_cof=symval(q_vars))
    if !pzerop(cof).truthy() {
      sheafa__mshow("NUM", num)
      sheafa__mshow("COF", cof)
    }
    tra = n_plus(tra, nred(cof, den))
  }
  new_disrep(tra)
}

///|
fn poly_scalar_p(poly : Value) -> Value raise {
  if affine_polynomialp(poly).truthy() {
    if atom(poly) {
      t
    } else {
      d_scalarp(get(car(poly), q_disrep))
    }
  } else {
    Nil
  }
}

///|
fn set_up_trace_subs(basis : Value) -> Value raise {
  check_arg(basis, d_listp(basis), list1(Str("maxima list"))) |> ignore
  let old = Collector::new()
  let new = Collector::new()
  for v in cdr(basis).iter() {
    old.add(add_newvar(v).0)
    new.add(d_algebra_trace(v, basis))
  }
  list2(old.result(), new.result())
}

///|
fn d_algebra_trace_matrix(basis : Value) -> (Value, Value, Value) raise {
  let subs = set_up_trace_subs(basis)
  set(
    dim_3__q_tr,
    make_pairing_function(cdr(basis), second(subs), test_=q_nc_equal),
  )
  |> ignore
  check_arg(basis, d_listp(basis), list1(Str("maxima list"))) |> ignore
  let basis = cdr(basis)
  let n = length(basis)
  let ar = make_array([n, n])
  let mut i = 0
  for _v in basis.iter() {
    for j in i..<n {
      let elt_ = dim_3__ncmul2(nth(i, basis), nth(j, basis))
      sheafa__show("ELT", elt_)
      let simp = new_rat(dim_3__dotsimp_remember(elt_))
      let result = new_disrep(apply_linear_function(symval(dim_3__q_tr), simp))
      aset(ar, [i, j], result) |> ignore
      aset(ar, [j, i], result) |> ignore
    }
    i += 1
  }
  (maxima_matrix_from_array(ar), subs, symval(dim_3__q_tr))
}

///|
fn d_trace_general_element(
  elt_ : Value,
  basis : Value,
  basis_trace : Value,
) -> Value raise {
  set(
    dim_3__q_tr,
    make_pairing_function(cdr(basis), cdr(basis_trace), test_=q_nc_equal),
  )
  |> ignore
  let simp = new_rat(dim_3__dotsimp_remember(elt_))
  new_disrep(apply_linear_function(symval(dim_3__q_tr), simp))
}

///|
fn maxima_matrix_from_array(ar : Value) -> Value raise {
  let dims = array_dimensions(ar)
  let rows = Collector::new()
  for i in 0..<to_int(car(dims)) {
    let row = Collector::new()
    for j in 0..<to_int(second(dims)) {
      row.add(aref(ar, [i, j]))
    }
    rows.add(cons(list1(q_mlist), row.result()))
  }
  cons(list1(q_d_matrix), rows.result())
}

///|
fn make_pairing_function(
  domain : Value,
  range : Value,
  test_? : Value = q_alike,
) -> Value raise {
  lfunc("make-pairing-function", args => {
    let u = arg(args, 0)
    let mut d = domain
    let mut r = range
    while consp(d) && consp(r) {
      if funcall(test_, [u, car(d)]).truthy() {
        return car(r)
      }
      d = cdr(d)
      r = cdr(r)
    }
    raise LispError::SimpleError(
      format_to_string("u was not in the domain ~A", [domain]),
    )
  })
}

///|
/// FN should be a function which is defined on the monomials and this
/// extends it to all.
fn apply_linear_function(fn_ : Value, expr : Value) -> Value raise {
  let mut den = int(1)
  let mut expr = expr
  if affine_polynomialp(expr).truthy() {
    den = int(1)
  } else if rational_functionp(expr).truthy() {
    den = denom(expr)
    expr = num(expr)
  } else {
    fsignal(list1(Str("expr must be a polynomial or rational function")))
    |> ignore
  }
  sheafa__show("DEN", den)
  let num_answ = if atom(expr) {
    nred(dim_3__ntimes(expr, funcall(fn_, [int(1)])), den)
  } else if d_scalarp(get(car(expr), q_disrep)).truthy() {
    sheafa__show("EXPR", expr)
    dim_3__ntimes(expr, funcall(fn_, [int(1)]))
  } else {
    dim_3__assert(
      poly_scalar_p(p__cof(expr)).truthy(),
      "(POLY-SCALAR-P (P-COF EXPR))",
    )
    let result = dim_3__ntimes(
      p__cof(expr),
      funcall(fn_, [get(car(expr), q_disrep)]),
    )
    if cdddr(expr).truthy() {
      dim_3__assert(
        eql(fourth(expr), int(0)) && nthcdr(5, expr) is Nil,
        "(AND (EQL (FOURTH EXPR) 0) (NULL (NTHCDR 5 EXPR)))",
      )
      n_plus(apply_linear_function(fn_, fifth(expr)), result)
    } else {
      result
    }
  }
  nred(num_answ, den)
}

///|
/// If TRACE-MATRIX is the <ui,uj> for an inner product, find the elt u,
/// such that <u,ui>=1 and <u,uj>=0 for i not = j, where
/// i= NUMBER-OF-ELEMENT-IN-BASIS.
fn dual_basis_element(
  number_of_element_in_basis : Value,
  trace_matrix : Value,
  basis? : Value,
) -> Value raise {
  let basis = match basis {
    Some(b) => b
    None => symval(q_d_basis)
  }
  let vari = subseq(symval(q_d_aaaa), 0, end=length(basis))
  let cond0 = d_list_matrix_entries(dim_3__ncmul2(trace_matrix, vari))
  let ac = Collector::new()
  let mut i = 1
  for v in cdr(cond0).iter() {
    if eql(int(i), number_of_element_in_basis) {
      ac.add(sub_star(v, int(1)))
    } else {
      ac.add(v)
    }
    i += 1
  }
  let actual_conditions = cons(list1(q_mlist), ac.result())
  let result = d_fast_linsolve(actual_conditions, variables=vari)
  d_sublis(
    result,
    d_general_sum(basis, coefficients=symval(q_d_aaaa)).0,
  )
}

///|
fn d_linear_variables(
  eqns : Value,
  constants? : Value = Nil,
) -> (Value, Value) raise {
  let mut constants = constants
  if constants.truthy() {
    constants = list_variables(st_rat(constants))
  }
  let eqns = st_rat(eqns)
  let mut vari = list_variables(eqns)
  let var_eqns = mapcar(x => list_variables(x), eqns)
  let mon = list3(Nil, int(1), int(1))
  for v in vari.iter() {
    for weqn in dim_3__zip(var_eqns, eqns) {
      let (w, eqn) = weqn
      if member(v, w).truthy() {
        setf_car(mon, v) |> ignore
        let tem = pcoeff(eqn, mon)
        if num_gt(pdegree(eqn, v), int(1)) {
          vari = delete(v, vari)
        } else if numberp(tem) {
          ()
        } else if constants.truthy() &&
          every(x => member(x, constants).truthy(), list_variables(tem)) {
          ()
        } else {
          vari = delete(v, vari)
        }
      }
    }
  }
  (cons(list1(q_mlist), mapcar(v => get(v, q_disrep), vari)), vari)
}

///|
fn d_fast_linsolve_inconsistent_equations(disrep? : Value = t) -> Value raise {
  let eqns = find_extra_conditions(
    sheafa__pv_the_sparse_matrix(symval(q_d_poly_vector)),
  )
  if disrep.truthy() {
    cons(list1(q_mlist), mapcar(x => new_disrep(x), eqns))
  } else {
    eqns
  }
}

///|
fn find_extra_conditions(sp_mat : Value) -> Value raise {
  // sp-column-used-in-row / sp-constants-column: slots 16 and 32
  let used = struct_ref(sp_mat, 16)
  let c = Collector::new()
  for i in 0..<array_total_size(used) {
    if aref1(struct_ref(sp_mat, 16), i) is Nil &&
      !new_zerop(aref1(struct_ref(sp_mat, 32), i)).truthy() {
      c.add(aref1(struct_ref(sp_mat, 32), i))
    }
  }
  c.result()
}

///|
fn d_my_phi(form : Value) -> Value raise {
  rota1(d_ratsimp(form, Nil))
}

///|
fn rota1(form : Value) -> Value raise {
  if atom(form) {
    form
  } else if eq(caar(form), q_mnctimes) {
    cons(car(form), cons(car(last(form)), butlast(cdr(form), n=1)))
  } else {
    cons(car(form), mapcar(v => rota1(v), cdr(form)))
  }
}

///|
fn d_central_rels(lis : Value) -> Value raise {
  let c = Collector::new()
  for v in cdr(lis).iter() {
    for w in cdr(d_append(list2(lis, symval(q_d_current_variables)))).iter() {
      c.add(new_disrep(n__(n_dot(v, w), n_dot(w, v))))
    }
  }
  cons(list1(q_mlist), c.result())
}

///|
/// Make LIS1 commute with LIS2.
fn d_centralize_rels(lis1 : Value, lis2 : Value) -> Value raise {
  let c = Collector::new()
  for v in cdr(lis1).iter() {
    for w in cdr(lis2).iter() {
      c.add(new_disrep(n__(n_dot(v, w), n_dot(w, v))))
    }
  }
  cons(list1(q_mlist), c.result())
}

///|
fn d_set_up(rels : Value, n? : Value = Nil) -> Value raise {
  set(q_ear_previously_checked_pairs, Nil) |> ignore
  d_set_up_dot_simplifications(rels) |> ignore
  set(q_d_bil, cons(list1(q_mlist), dim_3__global(dim_3__q_all_dotsimp_denoms)))
  |> ignore
  set(dim_3__q_all_dotsimp_denoms, Nil) |> ignore
  format(t, "~%Beginning check overlaps", []) |> ignore
  let r = d_check_overlaps(n, add_to_simps=t, maybe_reset=Nil)
  set(
    q_d_denoms,
    cons(list1(q_mlist), dim_3__global(dim_3__q_all_dotsimp_denoms)),
  )
  |> ignore
  r
}

///|
fn d_half_quantum_rels(rel3 : Value, m : Value) -> Value raise {
  with_special(q_d_dot_simplifications, Nil, () => {
    let vec = d_sort(d_list_variables(d_list_nc_monomials(rel3), Nil))
    let matt = d_generate_matrix(dim_3__lit_concat_u, m, m)
    let mut joe = d_sub_list(
      list2(
        list1(q_mlist),
        list3(
          list1(q_mequal),
          vec,
          d_list_matrix_entries(dim_3__ncmul2(matt, d_transpose(vec))),
        ),
      ),
      rel3,
    )
    format(t, "Using variables:", []) |> ignore
    displa(vec) |> ignore
    joe = simplifya(joe, Nil)
    displa(joe) |> ignore
    let ctls = d_centralize_rels(d_list_matrix_entries(matt), vec)
    displa(ctls) |> ignore
    d_set_up(d_append(list2(ctls, rel3)), n=int(4)) |> ignore
    let mut dotted = d_dotsimp(joe)
    let mon = d_mono(vec, int(2))
    d_set_up(
      sub_star(mon, d_firstn(symval(q_d_aaaa), d_length(mon))),
      n=int(1),
    )
    |> ignore
    d_print(list1(symval(q_d_dot_simplifications))) |> ignore
    dotted = d_dotsimp(dotted)
    d_append(cdr(d_separate_parameters(dotted, Str("aa"))))
  })
}

///|
/// Return the list of 2*n integers all less than i such that there are no
/// more than NREPEATS.
fn list_ordered_pairs_with_repeat_count(
  i : Value,
  j : Value,
  n : Value,
  nrepeats : Value,
) -> Value raise {
  with_special(q_ear_nvars, i, () => list_ordered_pairs_with_repeat_count1(
    i, j, n, nrepeats,
  ))
}

///|
/// Return t if (append (list i j) lis) has no more than nrepeats.
fn repeat_ok1(i : Value, j : Value, lis : Value, nrepeats : Value) -> Value raise {
  let mut n = int(0)
  if eql(i, j) {
    n = int(1)
  }
  if member(i, lis).truthy() {
    n = num_add(n, int(1))
  }
  if member(j, lis).truthy() {
    n = num_add(n, int(1))
  }
  if num_gt(n, nrepeats) {
    Nil
  } else {
    let mut x = lis
    while consp(x) {
      if member(car(x), cdr(x)).truthy() {
        n = num_add(n, int(1))
      }
      x = cdr(x)
    }
    if num_gt(n, nrepeats) {
      Nil
    } else {
      t
    }
  }
}

///|
fn list_ordered_pairs_with_repeat_count1(
  i : Value,
  j : Value,
  number_pairs : Value,
  number_repeats : Value,
) -> Value raise {
  if !num_gt(number_pairs, int(0)) {
    list1(Nil)
  } else {
    let c = Collector::new()
    let mut ii = int(0)
    while !num_gt(ii, i) {
      if num_lt(ii, symval(q_ear_nvars)) {
        let lim = if eql(ii, i) { j } else { symval(q_ear_nvars) }
        let mut jj = int(0)
        while num_lt(jj, lim) {
          for u in list_ordered_pairs_with_repeat_count1(
              ii,
              jj,
              num_sub(number_pairs, int(1)),
              number_repeats,
            ).iter() {
            if repeat_ok1(ii, jj, u, number_repeats).truthy() {
              c.add(append(list2(ii, jj), u))
            }
          }
          jj = num_add(jj, int(1))
        }
      }
      ii = num_add(ii, int(1))
    }
    c.result()
  }
}

///|
fn extract_cof1(f : Value, vars : Value) -> Value raise {
  let mut f = f
  if atom(f) {
    return list1(f)
  }
  if !affine_polynomialp(f).truthy() {
    f = numerator(f)
  }
  if member(car(f), vars).truthy() {
    let c = Collector::new()
    let mut l = cdr(f)
    while consp(l) {
      let cof = cadr(l)
      for x in extract_cof1(cof, vars).iter() {
        c.add(x)
      }
      l = cddr(l)
    }
    c.result()
  } else {
    list1(f)
  }
}

///|
fn d_extract_linear_from_commutative(form : Value, vars : Value) -> Value raise {
  dim_3__assert(listp(form), "(LISTP FORM)")
  let form = st_rat(form)
  let vars = list_variables(st_rat(vars))
  let c = Collector::new()
  for f in form.iter() {
    for x in extract_cof1(f, vars).iter() {
      c.add(x)
    }
  }
  cons(list1(q_mlist), mapcar(x => new_disrep(x), c.result()))
}

///|
fn init_share_dim_3() -> Unit raise {
  // $dotsimp_remember is a defremember function (not in the contract).
  defun(q_d_dotsimp_remember, args => dim_3__dotsimp_remember(
    arg(args, 0),
    dot_simplifications?=args.get(1),
  ))
}
