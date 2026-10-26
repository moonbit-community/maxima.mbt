// Port of share/affine/polyc.lisp: the masterlist of variables, $new_rat,
// representations and miscellaneous utilities of the affine package.
//
// polyc.lisp also redefines $numberp (to accept the affine package's
// rational functions) and LASTN; the redefinitions are installed in the
// function cells when the file is loaded (init_share_polyc).

///|
fn reset_vgp() -> Value raise {
  set(q_ear_genpairs, Nil) |> ignore
  set(q_ear_genvar, Nil) |> ignore
  set(q_ear_varlist, Nil) |> ignore
  let xxx = with_special(q_ear_print_radix, Nil, () => {
    let c = Collector::new()
    for i in 1..=30 {
      c.add(add_newvar(Value::Sym(intern("$x" + i.to_string()))).0)
    }
    c.result()
  })
  set(q_ear_xxx, xxx) |> ignore
  q_done
}

///|
fn show_vgp() -> Value raise {
  amacros__show("*GENPAIRS*", symval(q_ear_genpairs))
  amacros__show("GENPAIRS", symval(q_genpairs))
  amacros__show("*GENVAR*", symval(q_ear_genvar))
  amacros__show("GENVAR", symval(q_genvar))
  amacros__show("*VARLIST*", symval(q_ear_varlist))
  amacros__show("VARLIST", symval(q_varlist))
  Nil
}

///|
fn put_tellrat_property(va : Value, the_gensym : Value) -> Value raise {
  for v in symval(q_tellratlist).iter() {
    if equal(va, car(v)) {
      putprop(the_gensym, cdr(v), q_tellrat) |> ignore
    }
  }
  Nil
}

///|
fn poly_ncmul1(mon : Value, poly : Value, mon1 : Value) -> Value raise {
  let mut mon = mon
  let mut mon1 = mon1
  if mon is Nil {
    mon = Fix(1L)
  } else if mon1 is Nil {
    mon1 = Fix(1L)
  }
  if affine_polynomialp(poly) is Nil {
    amacros__break("T") |> ignore
  }
  if numberp(mon) && numberp(mon1) {
    return n_star(list2(poly, n_star(list2(mon, mon1))))
  }
  let monom : Value = if numberp(poly) { Nil } else { get(car(poly), q_disrep) }
  if numberp(poly) || d_scalarp(monom).truthy() {
    let monom = ncmul_star(list2(mon, mon1))
    let gen_sym = add_newvar(monom).0
    // (assolike monom *genpairs*) might be a long list to look in
    n_star(list2(list3(gen_sym, Fix(1L), Fix(1L)), poly))
  } else {
    let new_monom = ncmul_star(list3(mon, monom, mon1))
    if contains_a_zero_replacement(new_monom).truthy() {
      if eql(second(poly), Fix(1L)) && eql(fourth(poly), Fix(0L)) {
        poly_ncmul1(mon, fifth(poly), mon1)
      } else if eql(second(poly), Fix(1L)) {
        Fix(0L)
      } else {
        merror(Str("There is a bad order in nc polynomial ~A"), list1(poly))
      }
    } else {
      let gen_sym = add_newvar(new_monom).0
      if eql(second(poly), Fix(1L)) && eql(fourth(poly), Fix(0L)) {
        let tem = poly_ncmul1(mon, fifth(poly), mon1)
        if eql(tem, Fix(0L)) {
          list3(gen_sym, Fix(1L), third(poly))
        } else {
          list([gen_sym, Fix(1L), third(poly), Fix(0L), tem])
        }
      } else if eql(second(poly), Fix(1L)) {
        list3(gen_sym, Fix(1L), third(poly))
      } else {
        merror(Str("There is a bad order in nc polynomial ~A"), list1(poly))
      }
    }
  }
}

///|
/// "broken"
fn poly_ncmul(ll : Value) -> Value raise {
  for v in ll.iter() {
    if affine_polynomialp(v) is Nil {
      amacros__break("T") |> ignore
    }
  }
  if ll is Nil {
    Fix(1L)
  } else if length(ll) == 1 {
    car(ll)
  } else if numberp(car(ll)) {
    n_star(list2(car(ll), poly_ncmul(cdr(ll))))
  } else if affine_polynomialp(car(ll)).truthy() {
    poly_ncmul(cons(poly_ncmul1(Fix(1L), car(ll), second(ll)), nthcdr(2, ll)))
  } else if affine_polynomialp(second(ll)).truthy() {
    if affine_polynomialp(third(ll)).truthy() {
      merror(
        Str(
          "poly-ncmul can't have two 'affine-polynomialp objects in its arg yet",
        ),
        Nil,
      )
    } else {
      poly_ncmul(
        cons(poly_ncmul1(car(ll), second(ll), third(ll)), nthcdr(3, ll)),
      )
    }
  } else {
    Nil
  }
}

///|
fn reset_gen() -> Value raise {
  set(q_genvar, Nil) |> ignore
  set(q_varlist, Nil) |> ignore
  set(q_genpairs, Nil)
}

///|
fn show_vg(varl? : Value, genv? : Value) -> Value raise {
  let varl = match varl {
    Some(v) => v
    None => symval(q_ear_varlist)
  }
  let genv = match genv {
    Some(v) => v
    None => symval(q_ear_genvar)
  }
  let mut v = varl
  let mut w = genv
  while v is Cons(_) && w is Cons(_) {
    let vv = car(v)
    let ww = car(w)
    format(t, "~%~A ~A disrep ~A value ~A", [
      ww,
      vv,
      get(ww, q_disrep),
      symbol_value(ww),
    ])
    |> ignore
    if !equal(get(ww, q_disrep), vv) {
      format(t, " **** bad disrep ***", []) |> ignore
    }
    if !equal(get_genvar(vv), ww) {
      format(t, " **** bad *genpair***~A", [
        assolike(vv, symval(q_ear_genpairs)),
      ])
      |> ignore
    }
    v = cdr(v)
    w = cdr(w)
  }
  format(t, "~%~A and ~A are the lengths of genv and varl ", [
    int(length(genv)),
    int(length(varl)),
  ])
}

///|
fn last2(a_list : Value) -> Value raise {
  let mut v = a_list
  while v is Cons(_) {
    if cddr(v) is Nil {
      break
    }
    v = cdr(v)
  }
  v
}

///|
/// polyc.lisp's LASTN (n a-list), which replaces sym's LASTN (l n) in the
/// function cell when the file is loaded.
fn polyc__lastn(n : Value, a_list : Value) -> Value raise {
  let n = to_int(n)
  let mut v = a_list
  while v is Cons(_) {
    if nthcdr(n, v) is Nil {
      break
    }
    v = cdr(v)
  }
  v
}

///|
fn choose(m : Value, n : Value) -> Value raise {
  quot(
    factorial(m),
    num_mul(factorial(n), factorial(num_sub(m, n))),
  )
}

///|
fn polynomial_ring_1_1_1(deg : Value) -> Value raise {
  choose(num_add(deg, Fix(2L)), deg)
}

///|
fn three_times_n(n : Value) -> Value raise {
  num_mul(Fix(3L), n)
}

///|
/// Converts a single macsyma equation into a lisp list of conses suitable
/// for sublis.
fn list_equations1(expr : Value) -> Value raise {
  let mut expr = expr
  if listp(car(expr)) && eq(caar(expr), q_mequal) {
    expr = cdr(expr)
  } else {
    merror(Str("not a equation ~A "), list1(expr)) |> ignore
  }
  if atom(first(expr)) {
    list1(cons(first(expr), second(expr)))
  } else if memq(caar(first(expr)), list2(q_d_matrix, q_mlist)).truthy() {
    let c = Collector::new()
    let mut v = cdr(first(expr))
    let mut w = cdr(second(expr))
    while v is Cons(_) && w is Cons(_) {
      c.append_list(list_equations1(list2(car(v), car(w))))
      v = cdr(v)
      w = cdr(w)
    }
    c.result()
  } else {
    Nil
  }
}

///|
fn list_equations_macsyma1(expr : Value) -> Value raise {
  if !(listp(car(expr)) && eq(caar(expr), q_mequal)) {
    return Nil
  }
  if atom(second(expr)) {
    return list1(expr)
  }
  if memq(caar(second(expr)), list2(q_d_matrix, q_mlist)) is Nil {
    return list1(expr)
  }
  let expr = cdr(expr)
  if memq(caar(first(expr)), list2(q_d_matrix, q_mlist)) is Nil {
    return Nil
  }
  let c = Collector::new()
  if atom(second(expr)) || !eql(caar(first(expr)), caar(second(expr))) {
    for v in cdr(first(expr)).iter() {
      c.append_list(
        list_equations_macsyma1(list3(list1(q_mequal), v, second(expr))),
      )
    }
  } else {
    let mut v = cdr(first(expr))
    let mut w = cdr(second(expr))
    while v is Cons(_) && w is Cons(_) {
      c.append_list(
        list_equations_macsyma1(list3(list1(q_mequal), car(v), car(w))),
      )
      v = cdr(v)
      w = cdr(w)
    }
  }
  c.result()
}

///|
fn d_list_factors(poly : Value) -> Value raise {
  if atom(poly) {
    poly
  } else if mbagp(poly).truthy() {
    cons(car(poly), mapcar(x => d_list_factors(x), cdr(poly)))
  } else if eq(caar(poly), q_mtimes) {
    cons(list1(q_mlist), cdr(poly))
  } else {
    poly
  }
}

///|
fn d_list_equations(a_list : Value) -> Value raise {
  check_arg(a_list, q_d_listp, list1(Str("macsyma list"))) |> ignore
  let c = Collector::new()
  for v in cdr(a_list).iter() {
    c.append_list(list_equations_macsyma1(v))
  }
  cons(list1(q_mlist), c.result())
}

///|
fn d_sub_list(eqns : Value, expr : Value) -> Value raise {
  check_arg(eqns, q_d_listp, list1(Str("macsyma list"))) |> ignore
  let eqns = d_list_equations(eqns)
  d_sublis(eqns, expr)
}

///|
fn new_sublis(subs : Value, expr : Value) -> Value raise {
  let mut expr = expr
  let mut rat_form = false
  if d_ratp(expr).truthy() {
    expr = d_ratdisrep(expr)
    rat_form = true
  }
  if mbagp(expr).truthy() {
    cons(car(expr), mapcar(x => new_sublis(subs, x), cdr(expr)))
  } else {
    let answer = sublis(subs, expr)
    if rat_form {
      d_new_rat(answer)
    } else {
      meval_star(expr)
    }
  }
}

///|
fn remove_from__stargenpairs_star(expr : Value) -> Value raise {
  set(
    q_ear_genvar,
    polyc__delete_equal(get_genvar(expr), symval(q_ear_genvar)),
  )
  |> ignore
  let mut i = 0
  for v in list_to_array(symval(q_ear_genpairs)) {
    if equal(car(v), expr) {
      if i == 0 {
        set(q_ear_genpairs, cdr(symval(q_ear_genpairs))) |> ignore
      } else {
        set(q_ear_genpairs, polyc__delete_equal(v, symval(q_ear_genpairs)))
        |> ignore
      }
    }
    i += 1
  }
  set(q_ear_varlist, polyc__delete_equal(expr, symval(q_ear_varlist)))
}

///|
/// `(delete item list :test #'equal)`
fn polyc__delete_equal(item : Value, l : Value) -> Value {
  let mut l = l
  while l is Cons(_) && equal(car(l), item) {
    l = cdr(l)
  }
  if l is Nil {
    return Nil
  }
  let mut prev = l
  while cdr(prev) is Cons(_) {
    if equal(cadr(prev), item) {
      setf_cdr(prev, cddr(prev)) |> ignore
    } else {
      prev = cdr(prev)
    }
  }
  l
}

///|
fn pe() -> Value raise {
  format(t, "Enter a Macsyma expression:", []) |> ignore
  let tem = mread_noprompt(list1(symval(standard_input)))
  cdr(d_new_rat(meval_star(tem)))
}

///|
/// `(defquote $homework (a-list) ...)`: a-list is not evaluated.
fn polyc__homework(a_list : Value) -> Value raise {
  let mut work : Value = Nil
  for v in cdr(a_list).iter() {
    if symbolp(v) {
      work = meval_star(v)
      set(
        q_d_homework_done,
        append(symval(q_d_homework_done), list1(work)),
      )
      |> ignore
    } else {
      work = v
      set(
        q_d_homework_done,
        append(symval(q_d_homework_done), list1(work)),
      )
      |> ignore
    }
    format(t, "~%Working on ...", []) |> ignore
    displa(work) |> ignore
    let answer = meval_star(work)
    set(q_d_homework_done, append(symval(q_d_homework_done), list1(answer)))
    |> ignore
    displa(answer) |> ignore
  }
  symval(q_d_homework_done)
}

///|
fn d_eij(n : Value, i : Value, j : Value) -> Value raise {
  d_setelmx(Fix(1L), i, j, d_ident(n))
}

///|
/// REPRESENTATION should take two arguments a (size n1) and b (size n2)
/// where a is in GLn1 and b is a macsyma list of length n2. It returns the
/// general vector b left invariant by the upper triangular (unipotent)
/// matrices.
fn d_unipotent_invariant_vectors(
  representation : Value,
  n1 : Value,
  n2 : Value,
) -> Value raise {
  let c = Collector::new()
  let mut i : Value = Fix(1L)
  while num_lt(i, n1) {
    c.append_list(
      cdr(
        d_list_equations(
          list2(
            list1(q_mlist),
            list3(
              list1(q_mequal),
              mfuncall(
                representation,
                list2(
                  d_eij(n1, i, num_add(i, Fix(1L))),
                  d_firstn(n2, symval(q_d_aaaa)),
                ),
              ),
              d_firstn(n2, symval(q_d_aaaa)),
            ),
          ),
        ),
      ),
    )
    i = num_add(i, Fix(1L))
  }
  let eqns = cons(list1(q_mlist), c.result())
  let answer = d_fast_linsolve(
    eqns,
    variables=d_firstn(n2, symval(q_d_aaaa)),
  )
  d_separate_parameters(d_sublis(answer, d_firstn(n2, symval(q_d_aaaa))), Nil)
}

///|
fn d_matrix_from_list(a_list : Value) -> Value raise {
  let len = d_length(a_list)
  let tem = expt(len, Flo(0.5))
  let n = round1(tem)
  if eql(expt(n, Fix(2L)), d_length(a_list)) {
    ()
  } else {
    merror(Str("The length of list is not a square"), Nil) |> ignore
  }
  let mut a_list = cdr(a_list)
  let nn = to_int(n)
  let c = Collector::new()
  while a_list is Cons(_) {
    c.add(cons(list1(q_mlist), subseq(a_list, 0, end=nn)))
    a_list = nthcdr(nn, a_list)
  }
  cons(list1(q_d_matrix), c.result())
}

///|
fn kronecker_row_product(a : Value, b : Value) -> Value raise {
  let c = Collector::new()
  for v in cdr(b).iter() {
    for w in cdr(a).iter() {
      c.add(mul_star(list2(v, w)))
    }
  }
  cons(list1(q_mlist), c.result())
}

///|
fn d_kronecker_product(m : Value, n : Value) -> Value raise {
  let c = Collector::new()
  for row in cdr(n).iter() {
    for rowm in cdr(m).iter() {
      c.add(kronecker_row_product(rowm, row))
    }
  }
  cons(list1(q_d_matrix), c.result())
}

///|
fn d_standard_rep(mat : Value, v : Value) -> Value raise {
  d_list_matrix_entries(ncmul_star(list2(mat, v)))
}

///|
fn d_unlist_matrix_entries(vect : Value, size? : Value = Nil) -> Value raise {
  let size = if size.truthy() {
    size
  } else {
    round1(expt(int(length(vect)), Flo(0.5)))
  }
  let size = to_int(size)
  let mut vect = cdr(vect)
  let c = Collector::new()
  for i in 0..<size {
    ignore(i)
    c.add(cons(list1(q_mlist), subseq(vect, 0, end=size)))
    vect = nthcdr(size, vect)
  }
  cons(list1(q_d_matrix), c.result())
}

///|
fn sub_list(a_list : Value, expr : Value) -> Value raise {
  let c = Collector::new()
  let mut v = a_list
  while v is Cons(_) {
    c.add(list3(list1(q_mequal), car(v), second(v)))
    v = cddr(v)
  }
  d_sub_list(cons(list1(q_mlist), c.result()), expr)
}

///|
/// The DEFREP macro: returns the DEFUN form it expands into.
fn defrep(name : Value, argu : Value, body : Value) -> Value raise {
  let mat = first(argu)
  let v = second(argu)
  let gen_vector = sym("gen-vector")
  let gen_mat = sym("gen-mat")
  let info = sym("info")
  let image = sym("image")
  let body = sublis(list2(cons(v, gen_vector), cons(mat, gen_mat)), body)
  let qname = list2(q_quote, name)
  list([
    q_defun,
    name,
    list([mat, v, q_n_ampaux, info, gen_mat, gen_vector, image]),
    list3(q_remprop, qname, list2(q_quote, q_representation)),
    list3(
      q_cond,
      list2(
        list3(q_setq, info, list3(q_get, qname, list2(q_quote, q_representation))),
        list3(
          q_sub_list,
          list([q_list, list2(q_first, info), mat, list2(q_second, info), v]),
          list2(q_third, info),
        ),
      ),
      list([
        t,
        list3(
          q_setq,
          gen_mat,
          list3(
            q_d_general_matrix,
            list2(polyc__q_1_minus, list2(q_length, list2(q_second, mat))),
            list2(q_quote, q_d_p),
          ),
        ),
        list3(
          q_setq,
          gen_vector,
          list4(q_subseq, q_d_aaaa, Fix(0L), list2(q_length, v)),
        ),
        list3(q_setq, image, cons(q_progn, body)),
        list4(
          q_putprop,
          list2(q_quote, q_d_tensor4),
          list4(q_list, gen_mat, gen_vector, image),
          list2(q_quote, q_representation),
        ),
        list3(q_d_tensor4, sym("mat"), sym("v")),
      ]),
    ),
  ])
}

///|
fn d_tensor4(mat : Value, v : Value) -> Value raise {
  d_tensor_product_representation(q_d_tensor2, Fix(4L), q_d_tensor2, Fix(4L), mat, v)
}

///|
fn d_tensor2(mat : Value, v : Value) -> Value raise {
  d_tensor_product_representation(
    q_d_standard_rep,
    Fix(3L),
    q_d_standard_rep,
    Fix(3L),
    mat,
    v,
  )
}

///|
fn d_tensor3(mat : Value, v : Value) -> Value raise {
  d_tensor_product_representation(
    q_d_standard_rep,
    Fix(3L),
    q_d_tensor2,
    Fix(9L),
    mat,
    v,
  )
}

///|
fn d_sum5_standard_rep(mat : Value, v : Value) -> Value raise {
  let size = d_length(mat)
  let mut v = v
  let c = Collector::new()
  for i in 0..<5 {
    ignore(i)
    c.append_list(cdr(d_standard_rep(mat, d_firstn(size, v))))
    v = cons(list1(q_mlist), nthcdr(to_int(size), cdr(v)))
  }
  cons(list1(q_mlist), c.result())
}

// The representation of ei^Vej^Vek as a list is done by varying the first
// index fastest. The definitions below (the later ones in polyc.lisp,
// which are the ones in effect) are for reversed indexing, where the
// subscripts vary fastest at the right.

///|
fn list_ind_to_tensor_ind(
  dimv : Value,
  tensor_power : Value,
  ind : Value,
) -> Value raise {
  let mut ind = num_sub(ind, Fix(1L))
  let c = Collector::new()
  let n = to_int(tensor_power)
  for i in 0..<n {
    ignore(i)
    c.add(num_add(num_mod(ind, dimv), Fix(1L)))
    ind = quot(ind, dimv)
  }
  nreverse(c.result())
}

///|
fn tensor_ind_to_list_ind(dimv : Value, ll : Value) -> Value raise {
  // (loop for m in ll for i to 0 downfrom (1- (length ll)) ...)
  let mut tem : Value = Fix(0L)
  let mut i = length(ll) - 1
  for m in ll.iter() {
    if i < 0 {
      break
    }
    tem = num_add(tem, num_mul(expt(dimv, int(i)), num_sub(m, Fix(1L))))
    i -= 1
  }
  num_add(tem, Fix(1L))
}

///|
fn d_tensor_product_representation(
  rep1 : Value,
  d1 : Value,
  rep2 : Value,
  d2 : Value,
  p : Value,
  w : Value,
) -> Value raise {
  let mm1 = d_find_matrix_of_operator(
    lfunc("lambda", args => mfuncall(rep1, list2(p, arg(args, 0)))),
    d_standard_basis(d1),
  )
  let mm2 = d_find_matrix_of_operator(
    lfunc("lambda", args => mfuncall(rep2, list2(p, arg(args, 0)))),
    d_standard_basis(d2),
  )
  d_list_matrix_entries(
    ncmul_star(list2(mfuncall(q_d_kronecker_product, list2(mm1, mm2)), w)),
  )
}

///|
/// OPERATOR acts on the space spanned by BASIS.
fn d_find_matrix_of_operator(operator : Value, basis : Value) -> Value raise {
  let gen_b = d_firstn(d_length(basis), symval(q_d_bbbb))
  let gen_sum = d_general_sum(basis, coefficients=symval(q_d_bbbb)).0
  let lhs = mfuncall(operator, list1(gen_sum))
  let unknowns = subseq(symval(q_d_aaaa), 0, end=length(basis))
  let rhs = d_general_sum(basis, coefficients=unknowns).0
  let eqns = d_list_equations(
    list2(list1(q_mlist), list3(list1(q_mequal), lhs, rhs)),
  )
  let answer = d_fast_linsolve(eqns, variables=unknowns)
  let gen_a = d_sublis(answer, unknowns)
  let zero_b = mapcar(w => cons(w, Fix(0L)), cdr(gen_b))
  let c = Collector::new()
  for v in cdr(gen_b).iter() {
    c.add(meval_star(sublis(zero_b, subst(Fix(1L), v, gen_a))))
  }
  d_transpose(cons(list2(q_d_matrix, q_simp), c.result()))
}

///|
fn d_restriction_representation(
  repr : Value,
  elt_gln : Value,
  vector_ : Value,
  sub_basis : Value,
) -> Value raise {
  let repr_of_p = d_find_matrix_of_operator(
    lfunc("lambda", args => mfuncall(repr, list2(elt_gln, arg(args, 0)))),
    sub_basis,
  )
  ncmul_star(list2(repr_of_p, vector_))
}

///|
fn d_standard_basis(n : Value) -> Value raise {
  cons(list1(q_mlist), cdr(d_ident(n)))
}

///|
fn d_find_highest_weight_vectors(rep : Value, n1 : Value, n2 : Value) -> Value raise {
  let uni_vectors = d_unipotent_invariant_vectors(rep, n1, n2)
  let answer = d_diagonalize_torus(rep, n1, n2, uni_vectors)
  list3(list1(q_mlist), uni_vectors, answer)
}

///|
/// Here operator has args a and b where a is in torus and b is a sum of
/// elements of basis.
fn d_diagonalize_torus(
  representation : Value,
  n1 : Value,
  n2 : Value,
  basis : Value,
) -> Value raise {
  ignore(n2)
  let mut diag = d_ident(n1)
  let mut i : Value = Fix(1L)
  while num_le(i, n1) {
    diag = d_setelmx(
      nth(to_int(i) - 1, symval(q_ear_some_primes)),
      i,
      i,
      diag,
    )
    i = num_add(i, Fix(1L))
  }
  let dg = diag
  let tem = lfunc("lambda", args => mfuncall(representation, list2(dg, arg(args, 0))))
  let mat = d_find_matrix_of_operator(tem, basis)
  let cpoly = d_charpoly(mat, q_d_x)
  let answer = d_solve(cpoly, varl=list1(q_d_x))
  let eigen_values = mapcar(u => third(u), cdr(answer))
  let part_basis = Collector::new()
  let weight_vectors = Collector::new()
  for u in eigen_values.iter() {
    part_basis.add(d_find_eigenvectors(mat, u))
    let weight_vector = exponent_vector(u, length_vector=n1)
    weight_vectors.add(weight_vector)
    amacros__show("WEIGHT-VECTOR", weight_vector)
  }
  list3(
    list1(q_mlist),
    cons(list1(q_mlist), part_basis.result()),
    cons(list1(q_mlist), weight_vectors.result()),
  )
}

///|
fn d_find_eigenvectors(mat : Value, eigenvalue : Value) -> Value raise {
  let row_length = d_length(second(mat))
  let gen_vector = d_firstn(row_length, symval(q_d_aaaa))
  let eqns = d_list_equations(
    list2(
      list1(q_mlist),
      list3(
        list1(q_mequal),
        ncmul_star(
          list2(
            sub_star(mat, mul_star(list2(eigenvalue, d_ident(row_length)))),
            gen_vector,
          ),
        ),
        Fix(0L),
      ),
    ),
  )
  let answer = d_fast_linsolve(eqns, variables=gen_vector)
  d_separate_parameters(d_sublis(answer, gen_vector), Nil)
}

///|
fn d_rank_of_representation(
  rep : Value,
  n1 : Value,
  list_of_generators : Value,
) -> Value raise {
  let mat = d_general_matrix(n1, symval(q_d_cccc))
  let c = Collector::new()
  for v in cdr(list_of_generators).iter() {
    c.append_list(copy_list(cdr(mfuncall(rep, list2(mat, v)))))
  }
  d_find_rank_of_list_of_polynomials(cons(list1(q_mlist), c.result()))
}

///|
fn d_general_matrix(n : Value, a_list : Value) -> Value raise {
  if listp(a_list) {
    d_unlist_matrix_entries(a_list, size=n)
  } else {
    let c = Collector::new()
    let mut i : Value = Fix(1L)
    while num_le(i, n) {
      let mut j : Value = Fix(1L)
      while num_le(j, n) {
        c.add(new_concat(a_list, list2(i, j)))
        j = num_add(j, Fix(1L))
      }
      i = num_add(i, Fix(1L))
    }
    d_unlist_matrix_entries(cons(list1(q_mlist), c.result()), size=n)
  }
}

///|
fn exponent_vector(n : Value, length_vector? : Value = Fix(10L)) -> Value raise {
  if numberp(n) {
    let c = Collector::new()
    let mut j : Value = Fix(0L)
    for u in symval(q_ear_some_primes).iter() {
      if !num_lt(j, length_vector) {
        break
      }
      let mut i : Value = Fix(1L)
      while true {
        if !zerop(num_mod(n, expt(u, i))) {
          c.add(num_sub(i, Fix(1L)))
          break
        }
        i = num_add(i, Fix(1L))
      }
      j = num_add(j, Fix(1L))
    }
    c.result()
  } else if equal(caar(n), q_rat) {
    let num_ = second(n)
    let denom_ = third(n)
    let wnum = exponent_vector(num_, length_vector~)
    let wdnom = exponent_vector(denom_, length_vector~)
    mapcar2((v, w) => num_sub(v, w), wnum, wdnom)
  } else {
    Nil
  }
}

///|
fn replace_parameters_by_aa(expr : Value) -> (Value, Value) raise {
  let mut expr = expr
  let mut unknowns = d_list_variables(expr, list2(Str("aa"), Str("par")))
  let parameters = Collector::new()
  for vv in cdr(unknowns).iter() {
    if string_search("PAR", string_upcase(lstring(string(vv)))) >= 0 {
      parameters.add(vv)
    }
  }
  let mut tem1 = cdr(symval(q_d_aaaa))
  let subs = Collector::new()
  for vv in parameters.result().iter() {
    let subs1 = Collector::new()
    while tem1 is Cons(_) {
      if memq(car(tem1), unknowns) is Nil {
        subs1.add(cons(vv, car(tem1)))
        with_special(q_ear_print_level, Fix(3L), () => {
          format(t, "~%Replacing ~A by ~A in ~A.", [vv, car(tem1), expr])
        })
        |> ignore
        tem1 = cdr(tem1)
        break
      } else {
        tem1 = cdr(tem1)
      }
    }
    subs.append_list(subs1.result())
  }
  let subs = subs.result()
  amacros__show("SUBS", subs)
  expr = sublis(subs, expr)
  unknowns = sublis(subs, unknowns)
  (expr, unknowns)
}

///|
fn function_denominator(pol : Value) -> Value raise {
  if numberp(pol) {
    denominator(pol)
  } else if affine_polynomialp(pol).truthy() {
    Fix(1L)
  } else if rational_functionp(pol).truthy() {
    denom(pol)
  } else {
    denom(new_rat(pol))
  }
}

///|
fn function_numerator(pol : Value) -> Value raise {
  if rationalp(pol) {
    numerator(pol)
  } else if affine_polynomialp(pol).truthy() {
    pol
  } else if rational_functionp(pol).truthy() {
    car(pol)
  } else {
    car(new_rat(pol))
  }
}

///|
fn poly_type(x : Value) -> Value raise {
  if numberp(x) {
    q_kw_number
  } else if affine_polynomialp(x).truthy() {
    q_kw_polynomial
  } else if rational_functionp(x).truthy() {
    q_kw_rational_function
  } else if d_ratp(x).truthy() {
    polybas__kw_drat
  } else if listp(x) && eq(caar(x), q_rat) {
    q_kw_rat
  } else {
    Nil
  }
}

///|
fn check_rat_variables(expr : Value) -> Value raise {
  with_specials([(q_varlist, varlist(expr)), (q_genvar, genvar(expr))], () => {
    check_vgp_correspond()
  })
}

///|
fn check_vgp_correspond() -> Value raise {
  let mut v = symval(q_varlist)
  let mut w = symval(q_genvar)
  while v is Cons(_) && w is Cons(_) {
    if !equal(car(v), get(car(w), q_disrep)) ||
      !eq(car(w), get_genvar(car(v))) {
      merror(Str("bad ~A and ~A"), list2(car(v), car(w))) |> ignore
    }
    v = cdr(v)
    w = cdr(w)
  }
  Nil
}

///|
fn d_slow_gcdlist(ll : Value) -> Value raise {
  if ll is Nil {
    Fix(1L)
  } else if d_listp(car(ll)).truthy() {
    apply(q_d_gcdlist, cdar(ll))
  } else {
    match length(ll) {
      1 => car(ll)
      2 => d_gcd(car(ll), second(ll), Nil)
      _ => d_gcd(car(ll), apply(q_d_gcdlist, cdr(ll)), Nil)
    }
  }
}

///|
fn d_slow_projective(l : Value) -> Value raise {
  d_ratsimp(
    simplifya(list3(list1(q_mquotient), l, d_slow_gcdlist(list1(l))), Nil),
    Nil,
  )
}

// The sp- arithmetic: polyc.lisp defines these twice; the later
// definitions (on the affine polynomials) are the ones in effect.

///|
fn sp_add_star(llist : Value) -> Value raise {
  if llist is Nil {
    Fix(0L)
  } else {
    match length(llist) {
      2 => n_plus(first(llist), second(llist))
      1 => car(llist)
      _ => sp_add_star(cons(n_plus(first(llist), second(llist)), cddr(llist)))
    }
  }
}

///|
fn sp_minus_star(a : Value) -> Value raise {
  n__(Fix(0L), a)
}

///|
fn sp_sub_star(a : Value, b : Value) -> Value raise {
  n__(a, b)
}

///|
fn sp_mul_star(a_list : Value) -> Value raise {
  if a_list is Nil {
    Fix(1L)
  } else {
    match length(a_list) {
      2 => n_star(list2(first(a_list), second(a_list)))
      1 => car(a_list)
      _ =>
        sp_mul_star(
          cons(n_star(list2(first(a_list), second(a_list))), cddr(a_list)),
        )
    }
  }
}

///|
fn sp_div_star(a : Value, b : Value) -> Value raise {
  nred(a, b)
}

///|
/// polyc.lisp's $numberp ("we changed this to allow polynomial-type"),
/// which replaces the core $numberp in the function cell when the file is
/// loaded. Calls of $numberp in compiled Lisp code go to the core
/// NUMBERP-IMPL (DEFMFUN's compiler macro), so the affine files call
/// d_numberp; only calls through the symbol reach this one.
fn polyc__numberp(n : Value) -> Value raise {
  if numberp(n) {
    t
  } else if atom(n) {
    Nil
  } else if numberp(car(n)) && numberp(cdr(n)) {
    t
  } else if atom(car(n)) {
    Nil
  } else if eq(caar(n), q_rat) {
    t
  } else if eq(caar(n), q_mrat) {
    lbool(numberp(cadr(n)) && numberp(cddr(n)))
  } else {
    let v = d_floatnump(n)
    if v.truthy() {
      v
    } else {
      d_bfloatp(n)
    }
  }
}

///|
fn poly_scalarp(a : Value) -> Value raise {
  if numberp(a) {
    t
  } else if atom(a) {
    d_scalarp(a)
  } else {
    let tem = affine_polynomialp(a)
    if tem.truthy() {
      d_scalarp(tem)
    } else {
      let tem = affine_polynomialp(car(a))
      if tem.truthy() && affine_polynomialp(cdr(a)).truthy() {
        d_scalarp(tem)
      } else {
        Nil
      }
    }
  }
}

///|
fn d_coefficient_matrix(a_list : Value, variables : Value) -> Value raise {
  check_arg(a_list, q_d_listp, Nil) |> ignore
  check_arg(variables, q_d_listp, Nil) |> ignore
  let bil = Collector::new()
  for w in cdr(a_list).iter() {
    let tem = Collector::new()
    for v in cdr(variables).iter() {
      tem.add(d_nc_coeff(w, v))
    }
    bil.add(cons(list1(q_mlist), tem.result()))
  }
  cons(list1(q_d_matrix), bil.result())
}

///|
fn d_new_rat(expr : Value) -> Value raise {
  if d_ratp(expr).truthy() &&
    equal(symval(q_ear_genvar), genvar(expr)) &&
    equal(symval(q_ear_varlist), varlist(expr)) {
    expr
  } else if d_ratp(expr).truthy() {
    // what about minimize varlist here, or in new-ratf
    let mut bad = false
    let mut v = varlist(expr)
    let mut w = genvar(expr)
    while v is Cons(_) && w is Cons(_) {
      if !eq(car(w), get_genvar(car(v))) {
        bad = true
        break
      }
      v = cdr(v)
      w = cdr(w)
    }
    if bad {
      new_ratf(expr)
    } else {
      expr
    }
  } else if mbagp(expr).truthy() {
    cons(car(expr), mapcar(x => d_new_rat(x), cdr(expr))) |> ignore
    // The Lisp code then calls ($new_rat expr) on the same list again,
    // which recurses forever; signal that instead of hanging.
    merror(Str("new_rat: infinite recursion on the list ~M"), list1(expr))
  } else if !atom(expr) && !atom(car(expr)) {
    if equal(caar(expr), q_rat) {
      expr
    } else {
      new_ratf(expr)
    }
  } else {
    new_ratf(expr)
  }
}

///|
fn d_shift(expr : Value, variables? : Value) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  let c = Collector::new()
  let mut v = cdr(variables)
  while v is Cons(_) {
    let tem = if second(v).truthy() { second(v) } else { second(variables) }
    c.add(cons(car(v), tem))
    v = cdr(v)
  }
  sublis(c.result(), expr)
}

///|
fn d_spur(expr : Value, function : Value, n : Value) -> Value raise {
  let mut tem = expr
  let mut answer : Value = Fix(0L)
  let mut i : Value = Fix(0L)
  while num_lt(i, n) {
    tem = funcall(function, [tem])
    answer = add_star(list2(answer, tem))
    i = num_add(i, Fix(1L))
  }
  d_ratsimp(answer, Nil)
}

///|
fn d_basis_of_invariant_ring(n : Value, variables? : Value) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  let monoms = d_mono(variables, n)
  let c = Collector::new()
  for u in cdr(monoms).iter() {
    c.add(d_spur(u, q_d_shift, int(length(variables) - 1)))
  }
  let trace_monoms = cons(list1(q_mlist), c.result())
  ignore(trace_monoms)
  // The Lisp code then enters the debugger with (BREAK T); what follows it
  // uses flavor messages (SEND) that no longer exist.
  amacros__break("T")
}

///|
fn d_case_rep(mat : Value, vect : Value, triple : Value) -> Value raise {
  with_special(q_d_expop, Fix(100L), () => {
    let triple = cdr(triple)
    let subs = list3(
      cons(q_d__pctalpha, first(triple)),
      cons(q_d__pctbeta, second(triple)),
      cons(q_d__pctgamma, third(triple)),
    )
    let mut mmm = sublis(subs, symval(q_d_mmm))
    mmm = d_ratsimp(mmm, Nil)
    displa(mmm) |> ignore
    let tem = Collector::new()
    let ind = Collector::new()
    let mut i = 1
    for v in cdr(symval(q_d_conditions_on_q)).iter() {
      if d_zerop(d_ratsimp(sublis(subs, v), Nil)).truthy() {
        tem.add(nth(i, mmm))
        ind.add(int(i))
      }
      i += 1
    }
    let ind_used = ind.result()
    let relat_mat = tem.result()
    format(t, "~%Dimension of representation is ~A.", [int(length(ind_used))])
    |> ignore
    amacros__show("IND-USED", ind_used)
    let terms = Collector::new()
    for i in 1..=length(ind_used) {
      terms.add(mul_star(list2(nth(i, vect), nth(i - 1, relat_mat))))
    }
    let vmmm = meval_star(cons(list1(q_mplus), terms.result()))
    let xyz = list4(
      list2(q_d_matrix, q_simp),
      list2(list2(q_mlist, q_simp), q_d_x),
      list2(list2(q_mlist, q_simp), q_d_y),
      list2(list2(q_mlist, q_simp), q_d_z),
    )
    let mat_rtx = ncmul_star(list2(mat, xyz))
    let prod = ncmul_star(
      list3(
        d_transpose(mat),
        d_sub_list(
          list2(
            list2(q_mlist, q_simp),
            list3(list2(q_mequal, q_simp), copy_tree(xyz), mat_rtx),
          ),
          vmmm,
        ),
        mat,
      ),
    )
    let answer = mfuncall(polyc__q_d_cof, list1(prod))
    let res = Collector::new()
    for i in ind_used.iter() {
      res.add(nth(to_int(i), answer))
    }
    cons(list1(q_mlist), res.result())
  })
}

///|
let polyc__q_d_cof : Value = sym("$cof")

///|
let polyc__q_1_minus : Value = sym("1-")

///|
fn d_make_commutative(expr : Value) -> Value raise {
  resimplify(subst(q_mtimes, q_mnctimes, expr))
}

///|
fn init_share_polyc() -> Unit raise {
  defvar_init(
    q_d_binary_quartic_monomials,
    d_ratsimp(
      subst(
        q_mtimes,
        q_mnctimes,
        d_commutative_dot_monomials(
          list3(list1(q_mlist), q_d_x, q_d_y),
          Fix(4L),
        ),
      ),
      Nil,
    ),
  )
  register_mspec(q_d_homework, form => polyc__homework(cadr(form)))
  defun(q_d_numberp, args => polyc__numberp(arg(args, 0)), name="$numberp")
  defun(
    q_lastn,
    args => polyc__lastn(arg(args, 0), arg(args, 1)),
    name="lastn",
  )
}
