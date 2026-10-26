// Port of share/affine/polyd.lisp: central elements, checking cases of
// algebras given by relations, Hilbert functions, and some polynomial
// utilities (list-variables, npgcd, ...).
//
// polyd.lisp also defines a zero-argument TE that replaces new-rat.lisp's
// TE in the Lisp image; the contract declares TE with new-rat.lisp's
// lambda list, so that one is the port's TE.

///|
/// Checks you aren't adding a trivial product of centrals etc. It affects
/// the dot simplifications which become the dot simplifications modulo
/// ones-to-add checked thru the highest degree of ones to add.
fn which_centrals_to_add() -> Value raise {
  with_specials(
    [(q_ear_previously_checked_pairs, Nil), (q_d_dot_simplifications, Nil)],
    () => {
      let ones_to_add = Collector::new()
      let mut n = 0
      for v0 in cdr(symval(q_d_centrals_so_far)).iter() {
        if n == 3 {
          break
        }
        let mut v = v0
        if d_zerop(d_dotsimp(v)).truthy() {
          v = Fix(0L)
        } else {
          format(t, "~%Supposedly checking overlaps to deg ~a", [d_nc_degree(v)])
          |> ignore
          set(
            q_d_rank_function,
            hilbert_modulo(append(ones_to_add.result(), list1(v))),
          )
          |> ignore
          set(q_ear_previously_checked_pairs, Nil) |> ignore
          d_check_overlaps(d_nc_degree(v), add_to_simps=t, maybe_reset=Nil)
          |> ignore
        }
        if d_zerop(d_dotsimp(v)) is Nil {
          ones_to_add.add(v)
          n += 1
          d_add_relation_to_dot_simplifications(v) |> ignore
        }
      }
      ones_to_add.result()
    },
  )
}

///|
/// Finds at least n centrals if there are n thru to-degree. It also checks
/// overlaps and so affects the dot_simplifications. It stores them in
/// $centrals_so_far. If later asked it won't check below the centrals so
/// far degree.
fn find_number_of_centrals(
  n : Value,
  from_degree? : Value = Fix(2L),
  to_degree? : Value = Fix(10L),
  reset_centrals_so_far? : Value = Nil,
) -> Value raise {
  let mut from_degree = from_degree
  if reset_centrals_so_far.truthy() {
    set(q_d_centrals_so_far, list1(list1(q_mlist))) |> ignore
  }
  if 1 > length(symval(q_d_centrals_so_far)) {
    let mut m = from_degree
    for c in cdr(symval(q_d_centrals_so_far)).iter() {
      m = num_max(m, d_nc_degree(c))
    }
    from_degree = num_add(m, Fix(1L))
  }
  let mut i = num_add(from_degree, Fix(1L))
  let last = num_add(to_degree, Fix(1L))
  while num_le(i, last) {
    d_check_overlaps(
      i,
      add_to_simps=t,
      maybe_reset=Nil,
      from_degree=num_sub(i, Fix(1L)),
    )
    |> ignore
    let mut j : Value = Fix(1L)
    while num_le(j, i) {
      let rf = symval(q_d_rank_function)
      if rf.truthy() &&
        !eql(
          d_length(d_mono(symval(q_d_current_variables), j)),
          funcall(rf, [j]),
        ) {
        format(t, "~%Using Current Variables of..", []) |> ignore
        displa(symval(q_d_current_variables)) |> ignore
        format(t, "   and rank function ~A.", [rf]) |> ignore
        throw_tag(
          q_check_a_case,
          format(
            Nil,
            "In spite of checking overlaps to degree ~A the monomial dimensions were ~A and the rank functions was ~A in degree ~A.  We conclude not finite global dimension.",
            [
              i,
              d_length(d_mono(symval(q_d_current_variables), j)),
              funcall(rf, [j]),
              j,
            ],
          ),
        )
        |> ignore
      }
      j = num_add(j, Fix(1L))
    }
    set(
      q_d_centrals_so_far,
      d_append(
        list2(
          symval(q_d_centrals_so_far),
          d_fast_central_elements(
            symval(q_d_current_variables),
            num_sub(i, Fix(1L)),
          ),
        ),
      ),
    )
    |> ignore
    format(t, "~%Central elements thru degree ~A", [num_sub(i, Fix(1L))])
    |> ignore
    displa(symval(q_d_centrals_so_far)) |> ignore
    if num_ge(d_length(symval(q_d_centrals_so_far)), n) {
      return q_done
    }
    i = num_add(i, Fix(1L))
  }
  Nil
}

///|
fn monomials_and_rank_function_agree(n : Value) -> Value raise {
  let mut tem : Value = Nil
  let mut total : Value = Fix(0L)
  let mut i : Value = Fix(1L)
  while num_le(i, n) {
    let mono = d_length(d_mono(symval(q_d_current_variables), i))
    let rank = funcall(symval(q_d_rank_function), [i])
    format(
      t,
      "~%In degree ~A the monomial dimension is ~A and the rank function ~A.",
      [i, mono, rank],
    )
    |> ignore
    if !eql(mono, rank) {
      return Nil
    }
    tem = append(tem, list1(mono))
    total = num_add(total, mono)
    i = num_add(i, Fix(1L))
  }
  tem = cons(Fix(1L), tem)
  tem = cons(Str("total"), tem)
  total = num_add(total, Fix(1L))
  tem = cons(total, tem)
  format(t, "~%The total is ~A.", [total]) |> ignore
  tem
}

///|
/// Look for centrals thru degree to-degree then mod them out.
fn d_check_a_case(
  relations : Value,
  to_degree? : Value = Fix(10L),
  rank_function? : Value = q_d_global_dimension_3,
  variables? : Value = Nil,
) -> Value raise {
  let mut to_degree = to_degree
  let mut ones_to_add : Value = Nil
  let mut dims : Value = Nil
  set(q_d_centrals_so_far, list1(list1(q_mlist))) |> ignore
  if variables.truthy() {
    set(q_d_current_variables, variables) |> ignore
  } else {
    set(
      q_d_current_variables,
      d_list_variables(relations, list3(Str("X"), Str("Y"), Str("Z"))),
    )
    |> ignore
    for v in list_to_array(cdr(symval(q_d_current_variables))) {
      if d_scalarp(v).truthy() || lstring(string(v)).contains("%") {
        set(
          q_d_current_variables,
          polyc__delete_equal(v, symval(q_d_current_variables)),
        )
        |> ignore
      }
    }
  }
  amacros__show("$CURRENT_VARIABLES", symval(q_d_current_variables))
  funcall(q_d_set_up_dot_simplifications, [relations]) |> ignore
  let mut full_dot_simps = symval(q_d_dot_simplifications)
  let answer = catch_tag(q_check_a_case, () => {
    let mut i = 3
    while !(i == 6 || length(ones_to_add) == 3) {
      set(q_d_dot_simplifications, full_dot_simps) |> ignore
      set(q_d_rank_function, rank_function) |> ignore
      set(q_ear_previously_checked_pairs, Nil) |> ignore
      // gets centrals thru to-degree; may throw if not finite global dim.
      find_number_of_centrals(
        int(i),
        from_degree=Fix(2L),
        to_degree=num_add(to_degree, Fix(1L)),
      )
      |> ignore
      full_dot_simps = symval(q_d_dot_simplifications)
      ones_to_add = which_centrals_to_add()
      i += 1
    }
    if length(ones_to_add) >= 3 {
      to_degree = d_nc_degree(car(last(ones_to_add)))
    }
    set(q_d_rank_function, hilbert_modulo(ones_to_add)) |> ignore
    if ones_to_add.truthy() {
      dims = monomials_and_rank_function_agree(
        num_floor(
          num_add(
            Fix(1L),
            num_mul(Flo(2.2), d_nc_degree(car(last(ones_to_add)))),
          ),
        ).0,
      )
      if dims.truthy() {
        return Nil
      }
    } else {
      return list([
        list1(q_mlist),
        relations,
        format(Nil, "There are no centrals up to degree ~A", [to_degree]),
        d_ratsimp(symval(q_d_dot_simplifications), Nil),
      ])
    }
    // hopefully we don't get here and tessing worked.
    format(t, "~%~%HOW DID WE GET HERE?~%", []) |> ignore
    set(q_ear_previously_checked_pairs, Nil) |> ignore
    funcall(q_d_set_up_dot_simplifications, [append(relations, ones_to_add)])
    |> ignore
    d_check_overlaps(Fix(12L), add_to_simps=t, maybe_reset=Nil) |> ignore
    Nil
  })
  if answer.truthy() {
    ()
  } else {
    if dims is Nil {
      // (with-no-query (cdr ($monomial_dimensions 15)))
      dims = cdr(d_monomial_dimensions(Fix(15L)))
    }
    set(
      q_d_last_answer,
      list([
        list1(q_mlist),
        Str("Relations:"),
        relations,
        Str("Centrals added:"),
        cons(list1(q_mlist), ones_to_add),
        Str("Monomial dimensions:"),
        cons(list1(q_mlist), dims),
        format(Nil, "All Centrals to Degree ~A:", [to_degree]),
        symval(q_d_centrals_so_far),
        Str("Dot Simplifications:"),
        d_ratsimp(symval(q_d_dot_simplifications), Nil),
      ]),
    )
    |> ignore
  }
  format(
    t,
    "~%Conclusion:~%The algebra is a finite module of rank ~D over a polynomial ring.\n The polynomial ring is generated by elements in degrees ~D .  The actual generators are ",
    [
      second(nth(6, symval(q_d_last_answer))),
      mapcar(x => d_nc_degree(x), cdr(symval(q_d_centrals_so_far))),
    ],
  )
  |> ignore
  displa(symval(q_d_centrals_so_far)) |> ignore
  let tem = cdddr(
    polyc__delete_equal(Fix(0L), nth(6, symval(q_d_last_answer))),
  )
  format(
    t,
    "~%The dimension of the spaces of monomials in degrees 0 through ~D are~%",
    [int(length(tem) - 1)],
  )
  |> ignore
  format(t, "  ~A ", [tem]) |> ignore
  q_qed
}

///|
fn d_check_programs(list_relations : Value) -> Value raise {
  let tem = Collector::new()
  for v in cdr(list_relations).iter() {
    reset_vgp() |> ignore
    tem.add(d_check_a_case(v))
  }
  cons(list1(q_mlist), tem.result())
}

///|
fn new_convert_relation_to_dot_simp(
  relat : Value,
  ordering? : Value,
  then_simplify? : Value = Nil,
) -> Value raise {
  let ordering = match ordering {
    Some(o) => o
    None => symval(q_d_order_function)
  }
  let mut relat = d_dotsimp(relat)
  relat = num(cdr(relat))
  let worst = get(car(relat), q_disrep)
  let cof = third(relat)
  relat = nred(relat, cof)
  // should take cdddr etc. not subtract
  relat = n__(worst, relat)
  relat = header_poly(relat)
  format(t, "~%Adding  ", []) |> ignore
  displa(cons(list2(q_mlist, q_simp), list2(worst, relat))) |> ignore
  format(t, "    to dot_simplifications", []) |> ignore
  set(
    q_d_dot_simplifications,
    append(symval(q_d_dot_simplifications), list2(worst, relat)),
  )
  |> ignore
  d_sort_dot_simplifications(pred=ordering) |> ignore
  if then_simplify.truthy() {
    d_simplify_dot_simplifications() |> ignore
  }
  symval(q_d_dot_simplifications)
}

///|
/// This is only for $new_fast_dotsimp: tried to avoid calling itself and
/// added an unwind protect so that the dotsimps don't get screwed up if
/// you abort part way thru.
fn d_simplify_dot_simplifications(from_degree? : Value = Fix(0L)) -> Value raise {
  ignore(from_degree)
  if !eq(symval(q_d_new_fast_dotsimp), t) {
    raise LispError::SimpleError(
      "Use the old $simplify_dot_simplifications in polynomials.lisp for other dotsimps",
    )
  }
  d_sort_dot_simplifications() |> ignore
  format(t, "~%starting to resimplify dot simplifications..", []) |> ignore
  let leng = d_length(symval(q_d_dot_simplifications))
  if num_lt(leng, Fix(10L)) {
    displa(symval(q_d_dot_simplifications)) |> ignore
  } else {
    format(t, "~%There are ~A of them.", [num_truncate(leng, b=Fix(2L)).0])
    |> ignore
  }
  let mut dot_simps = symval(q_d_dot_simplifications)
  let mut resimplify = false
  let mut v = cdr(symval(q_d_dot_simplifications))
  let mut i = 1
  while v is Cons(_) {
    let mut start_over = false
    try {
      set(
        q_d_dot_simplifications,
        append(
          firstn(int(i), symval(q_d_dot_simplifications)),
          cddr(v),
        ),
      )
      |> ignore
      if d_must_replacep(car(v)).truthy() ||
        d_must_replacep(second(v)).truthy() {
        let mut relat = if symval(q_d_new_fast_dotsimp).truthy() {
          header_poly(n__(car(v), second(v)))
        } else {
          vsub_star(car(v), second(v))
        }
        relat = d_dotsimp(relat)
        if d_zerop(relat).truthy() {
          ()
        } else {
          new_convert_relation_to_dot_simp(relat) |> ignore
        }
        dot_simps = symval(q_d_dot_simplifications)
        resimplify = true
        start_over = true
      }
    } catch {
      e => {
        set(q_d_dot_simplifications, dot_simps) |> ignore
        raise e
      }
    }
    set(q_d_dot_simplifications, dot_simps) |> ignore
    if start_over {
      break
    }
    v = cddr(v)
    i += 2
  }
  if resimplify {
    d_simplify_dot_simplifications() |> ignore
  } else {
    format(t, "~%They were OK", []) |> ignore
  }
  symval(q_d_dot_simplifications)
}

///|
fn d_monomial_and_degree_lessp(x : Value, y : Value) -> Value raise {
  let x_deg = d_nc_degree(x)
  let y_deg = d_nc_degree(y)
  if num_gt(x_deg, y_deg) {
    t
  } else if eq(x_deg, y_deg) {
    d_monomial_alphalessp(x, y)
  } else {
    Nil
  }
}

///|
fn mono_dimension(n : Value) -> Value raise {
  d_length(d_mono(symval(q_d_current_variables), n))
}

///|
fn hilbert(n : Value, l : Value) -> Value raise {
  if num_lt(n, Fix(0L)) {
    Fix(0L)
  } else if eql(n, Fix(0L)) {
    Fix(1L)
  } else if l is Nil {
    d_global_dimension_3(n)
  } else {
    num_sub(hilbert(n, cdr(l)), hilbert(num_sub(n, car(l)), cdr(l)))
  }
}

///|
/// For 2 3 and 4 variables we have unique sequences so we plug them in
/// here.
fn our_dimensions(n : Value) -> Value raise {
  let ints = (xs : Array[Int]) => list(xs.map(x => int(x)))
  match length(cdr(symval(q_d_current_variables))) {
    0 => fsignal(list1(Str("no variables")))
    1 => Fix(1L)
    2 => dimension_from_sequence(ints([1, 2, 2, 1]), ints([1, 2, 1]), n, Fix(2L))
    3 => dimension_from_sequence(ints([1, 3, 3, 1]), ints([1, 1, 1]), n, Fix(3L))
    4 =>
      dimension_from_sequence(
        ints([1, 4, 6, 4, 1]),
        ints([1, 1, 1, 1]),
        n,
        Fix(4L),
      )
    _ => fsignal(list1(Str("not handled yet")))
  }
}

///|
fn d_global_dimension_3(n : Value) -> Value raise {
  our_dimensions(n)
}

///|
/// The sequences start from the right tail.
fn dimension_from_sequence(
  list_powers : Value,
  list_degree_maps : Value,
  degree : Value,
  number_variables : Value,
) -> Value raise {
  if !eql(car(list_powers), Fix(1L)) {
    raise LispError::SimpleError(
      "The value of LIST-POWERS is not first should be one",
    )
  }
  if num_lt(degree, Fix(0L)) {
    Fix(0L)
  } else if zerop(degree) {
    Fix(1L)
  } else if eql(Fix(1L), degree) {
    number_variables
  } else {
    let mut answ : Value = Fix(0L)
    let mut deg_map = list_degree_maps
    let mut u = cdr(list_powers)
    let mut i = 0
    let mut j = degree
    while deg_map is Cons(_) && u is Cons(_) && num_ge(j, Fix(0L)) {
      j = num_sub(j, car(deg_map))
      answ = num_add(
        answ,
        num_mul(
          num_mul(expt(Fix(-1L), int(i)), car(u)),
          dimension_from_sequence(list_powers, list_degree_maps, j, number_variables),
        ),
      )
      deg_map = cdr(deg_map)
      u = cdr(u)
      i += 1
    }
    num_abs(answ)
  }
}

///|
fn d_sum_hilbert(l : Value) -> Value raise {
  let mut sum : Value = Fix(0L)
  for i in 0..<100 {
    let tem = hilbert(int(i), cons(Fix(3L), l))
    if zerop(tem) {
      break
    }
    sum = num_add(sum, tem)
  }
  sum
}

///|
/// For creating a one argument function that can be funcalled.
fn d_hilbert_modulo(l : Value) -> Value raise {
  check_arg(l, q_d_listp, list1(Str("macsyma list"))) |> ignore
  hilbert_modulo(cdr(l))
}

///|
/// The lambda expression `(lambda (n) (apply 'hilbert n '<l>))`.
fn hilbert_modulo(l : Value) -> Value raise {
  if l is Nil || numberp(car(l)) {
    list3(
      q_lambda,
      list1(q_n),
      list4(q_apply, list2(q_quote, q_hilbert), q_n, list2(q_quote, copy_list(l))),
    )
  } else {
    hilbert_modulo(mapcar(x => d_nc_degree(x), l))
  }
}

///|
fn d_tes(relat : Value) -> Value raise {
  new_convert_relation_to_dot_simp(
    relat,
    ordering=symval(q_d_order_function),
    then_simplify=t,
  )
}

///|
fn d_add_relation_to_dot_simplifications(relat : Value) -> Value raise {
  new_convert_relation_to_dot_simp(
    relat,
    ordering=symval(q_d_order_function),
    then_simplify=t,
  )
}

///|
/// Does the new-rat for New_fast_dotsimp.
fn d_rat_the_dot_simplifications() -> Value raise {
  let mut res : Value = Nil
  let mut w = cdr(symval(q_d_dot_simplifications))
  while w is Cons(_) {
    res = cons(car(w), res)
    let v = cadr(w)
    res = cons(
      if d_ratp(v).truthy() {
        header_poly(new_rat(ratdisrep(v)))
      } else {
        header_poly(new_rat(v))
      },
      res,
    )
    w = cddr(w)
  }
  set(q_d_dot_simplifications, cons(list1(q_mlist), nreverse(res)))
}

///|
fn d_fast_central_elements_given_commutator(
  variables : Value,
  deg : Value,
  comut : Value,
  used_var : Value,
) -> Value raise {
  ignore(used_var)
  let f_ = symval(q_d_order_function)
  let variables = cons(
    list1(q_mlist),
    sort_list(cdr(variables), (a, b) => funcall(f_, [a, b]).truthy()),
  )
  set(q_d_commutators, Nil) |> ignore
  set(q_d_centralizers, Nil) |> ignore
  let monoms = d_mono(variables, deg)
  let f = d_general_sum(monoms, coefficients=symval(q_d_aaaa)).0
  let unknowns = d_list_variables(f, list2(Str("aa"), Str("par")))
  let tem1 = list2(list1(q_mlist), comut)
  let monoms_higher = d_list_nc_monomials(tem1)
  let eqns = d_extract_linear_equations(
    tem1,
    independent_monomials=monoms_higher,
  )
  ignore(eqns)
  amacros__show("UNKNOWNS", unknowns)
  // The Lisp code enters the debugger here with (BREAK T).
  amacros__break("T")
}

///|
fn d_read_lisp_string(a_string : Value) -> Value raise {
  lisp_eval_form(lread(string_trim("&", lstring(a_string))))
}

///|
fn d_try(u : Value) -> Value raise {
  d_add_relation_to_dot_simplifications(u) |> ignore
  let mut centrals : Value = Nil
  set(q_ear_previously_checked_pairs, Nil) |> ignore
  set(q_d_rank_function, Nil) |> ignore
  d_check_overlaps(Fix(10L), add_to_simps=t, maybe_reset=Nil) |> ignore
  for i in 1..<8 {
    let tem = cdr(d_fast_central_elements(symval(q_d_current_variables), int(i)))
    if tem.truthy() {
      for v in tem.iter() {
        d_add_relation_to_dot_simplifications(v) |> ignore
      }
      centrals = append(centrals, tem)
      d_check_overlaps(Fix(10L), add_to_simps=t, maybe_reset=Nil) |> ignore
    }
  }
  cons(list1(q_mlist), centrals)
}

///|
fn list_variables(expr : Value) -> Value raise {
  with_special(q_ear_all_vars, Nil, () => {
    list_variables1(expr) |> ignore
    symval(q_ear_all_vars)
  })
}

///|
fn list_variables1(expr : Value) -> Value raise {
  if atom(expr) {
    Nil
  } else if affine_polynomialp(expr).truthy() {
    let var_ = p__var(expr)
    if member(var_, symval(q_ear_all_vars)) is Nil {
      set(q_ear_all_vars, cons(var_, symval(q_ear_all_vars))) |> ignore
    }
    let mut r = cdr(expr)
    while r is Cons(_) {
      list_variables1(cadr(r)) |> ignore
      r = cddr(r)
    }
    Nil
  } else if rational_functionp(expr).truthy() {
    list_variables1(car(expr)) |> ignore
    list_variables1(cdr(expr))
  } else {
    for v in expr.iter() {
      list_variables1(v) |> ignore
    }
    Nil
  }
}

///|
fn reset_rat(tree : Value) -> Value raise {
  if atom(tree) {
    if symbolp(tree) {
      let tem = get(tree, q_disrep)
      if tem.truthy() {
        return add_newvar(tem).0
      }
    }
    tree
  } else {
    setf_car(tree, reset_rat(car(tree))) |> ignore
    setf_cdr(tree, reset_rat(cdr(tree)))
  }
}

///|
fn npfactor(p : Value) -> Value raise {
  let varl = list_variables(p)
  let genvar = reverse(sort_list(varl, (a, b) => pointergp(a, b).truthy()))
  with_special(q_genvar, genvar, () => pfactor(p))
}

///|
fn nplcm(x : Value, y : Value) -> Value raise {
  with_special(q_genvar, symval(q_ear_genvar), () => plcm(x, y))
}

///|
fn npgcd(f : Value, g : Value) -> Value raise {
  let varl = list_variables(list2(f, g))
  let genvar = reverse(sort_list(varl, (a, b) => pointergp(a, b).truthy()))
  with_special(q_genvar, genvar, () => pgcd(f, g))
}

///|
fn init_share_polyd() -> Unit raise {
  if memq(q_hilbert, symval(q_ear_all_rank_functions)) is Nil {
    set(
      q_ear_all_rank_functions,
      cons(q_hilbert, symval(q_ear_all_rank_functions)),
    )
    |> ignore
  }
}
