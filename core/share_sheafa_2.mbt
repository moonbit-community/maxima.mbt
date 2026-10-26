// Port of share/affine/sheafa.lisp (part 2): from UPDATE through
// LDATA-UNUSED.

// ---------------------------------------------------------------------------
// Small helpers

///|
/// `(break x)`: there is no debugger; signal an error instead.
fn sheafa__break(x : Value) -> Unit raise {
  raise LispError::SimpleError(format_to_string("break: ~A", [x]))
}

///|
/// `(get x ind)` on a non-symbol is a type error in CL.
fn sheafa__get(x : Value, ind : Value) -> Value raise {
  if !symbolp(x) {
    raise LispError::SimpleError(
      format_to_string("The value ~S is not of type SYMBOL", [x]),
    )
  }
  get(x, ind)
}

///|
/// `(check-arg place pred "msg")` with the predicate already evaluated.
fn sheafa__check_arg(ok : Bool, msg : String) -> Unit raise {
  if !ok {
    raise LispError::SimpleError(msg)
  }
}

///|
/// Case-insensitive `(search key string :test #'char-equal)`.
fn sheafa__search_ci(key : String, s : String) -> Int? {
  let kc = key.to_lower().to_array()
  let hc = s.to_lower().to_array()
  let n = kc.length()
  let m = hc.length()
  if n > m {
    return None
  }
  for i in 0..=(m - n) {
    let mut ok = true
    for j in 0..<n {
      if hc[i + j] != kc[j] {
        ok = false
        break
      }
    }
    if ok {
      return Some(i)
    }
  }
  None
}

///|
/// `(loop for (a b) on l by #'cddr ...)`: the pairs of a plist-like list.
fn sheafa__pairs(l : Value) -> Array[(Value, Value)] {
  let res : Array[(Value, Value)] = []
  let mut p = l
  while p is Cons(_) {
    res.push((car(p), cadr(p)))
    p = cddr(p)
  }
  res
}

// ---------------------------------------------------------------------------
// sheafa.lisp

///|
fn update(ldata : Value) -> Value raise {
  let n = length(ldata)
  if n < 6 {
    let pad : Array[Value] = []
    for _ in n..<6 {
      pad.push(Nil)
    }
    nconc(ldata, list(pad))
  } else {
    Nil
  }
}

///|
fn zl_pairlis(a : Value, b : Value) -> Value raise {
  let c = Collector::new()
  let mut p = a
  let mut q = b
  while p is Cons(_) && q is Cons(_) {
    c.add(cons(car(p), car(q)))
    p = cdr(p)
    q = cdr(q)
  }
  c.result()
}

///|
fn remove_common_factors(from_poly : Value, divisor : Value) -> Value raise {
  let answ = pgcdcofacts(from_poly, divisor)
  if eql(Fix(1L), car(answ)) {
    second(answ)
  } else {
    remove_common_factors(second(answ), car(answ))
  }
}

///|
fn strings_search(keys : Value, sstring : Value) -> Value raise {
  for v in keys.iter() {
    match sheafa__search_ci(lstring(string(v)), lstring(string(sstring))) {
      Some(i) => return int(i)
      None => ()
    }
  }
  Nil
}

///|
/// Replace the genvar with more readable symbols.
fn replace_genvar(strings : Value) -> Value raise {
  let answ = Collector::new()
  for v in symval(q_ear_genvar).iter() {
    let tem = get(v, q_disrep)
    let name = lstring(string(v))
    if atom(tem) &&
      name.length() > 0 &&
      name.to_array()[0] == 'G' &&
      (if strings.truthy() {
        strings_search(strings, string(tem)).truthy()
      } else {
        true
      }) {
      let hi = make_symbol(string_trim("$", lstring(string(tem))))
      set(hi, symval(v)) |> ignore
      set_symbol_plist(hi, copy_list(symbol_plist(v))) |> ignore
      answ.add(hi)
    } else {
      answ.add(v)
    }
  }
  set(q_ear_genvar, answ.result()) |> ignore
  Nil
}

///|
fn describe_components(comp : Value) -> Value raise {
  sheafa__check_arg(listp(comp) && eq(car(comp), q_components), "components")
  let mut answ : Value = Nil
  let mut i = 0
  for v in car(cdr(comp)).iter() {
    let tem = Collector::new()
    let tem2 = Collector::new()
    for w in v.iter() {
      if cdr(w).truthy() {
        tem.add(car(w))
        tem2.add(cdr(w))
      }
    }
    answ = list2(tem.result(), tem2.result())
    let opens = car(answ)
    format(t, "~%Component ~A occurs on opens ~A on ldata ~A", [
      int(i),
      opens,
      second(answ),
    ])
    |> ignore
    i += 1
  }
  if third(comp).truthy() {
    format(
      t,
      "~%There were bad components so the above must be taken with a grain of salt.  They were ~A",
      [third(comp)],
    )
  } else {
    format(t, "~%There were no bad components", [Nil])
  }
}

///|
/// STRING-LENGTH is not defined in Maxima, so this signals an undefined
/// function error as soon as it is called.
fn tableaux_lessp(a : Value, b : Value) -> Value raise {
  let _ = string(a)
  let _ = string(b)
  sheafb__undefined("STRING-LENGTH")
}

///|
/// STRING-LENGTH is not defined in Maxima (see TABLEAUX-LESSP).
fn last_string(x : Value) -> Value raise {
  let _ = x
  sheafb__undefined("STRING-LENGTH")
}

///|
/// `(defremember list-tableaux (row-length dimension) ...)`
fn sheafa__list_tableaux(row_length : Value, dimension : Value) -> Value raise {
  sheafa__remember(sheafa__q_list_tableaux, list2(row_length, dimension), () => {
    if eql(row_length, Fix(0L)) {
      Nil
    } else if eql(row_length, Fix(1L)) {
      let c = Collector::new()
      let mut i : Value = Fix(1L)
      while num_le(i, dimension) {
        c.add(list1(i))
        i = num_add(i, Fix(1L))
      }
      c.result()
    } else {
      let c = Collector::new()
      let mut j : Value = Fix(1L)
      while num_le(j, dimension) {
        for u in
          sheafa__list_tableaux(num_sub(row_length, Fix(1L)), dimension).iter() {
          if num_gt(j, car(last(u))) {
            c.add(append(u, list1(j)))
          }
        }
        j = num_add(j, Fix(1L))
      }
      c.result()
    }
  })
}

///|
fn d_list_tableaux(length_ : Value, dimension : Value) -> Value raise {
  cons(
    list1(q_mlist),
    mapcar(
      x => d_concat(cons(sym("$ta"), x)),
      sheafa__list_tableaux(length_, dimension),
    ),
  )
}

///|
fn sheafa__select_columns(row : Value, cols_to_take : Value) -> Value raise {
  let new_row = Collector::new()
  let mut i = 1
  for v in cdr(row).iter() {
    if member(int(i), cols_to_take).truthy() {
      new_row.add(v)
    }
    i += 1
  }
  cons(list1(q_mlist), new_row.result())
}

///|
fn d_sub_matrix(
  mat : Value,
  rows_to_take : Value,
  cols_to_take : Value,
) -> Value raise {
  let matrix = Collector::new()
  for ii in rows_to_take.iter() {
    let row = nth(to_int(ii), mat)
    matrix.add(sheafa__select_columns(row, cols_to_take))
  }
  cons(list2(q_d_matrix, q_simp), matrix.result())
}

///|
fn d_sub_matrix_columns(mat : Value, cols_to_take : Value) -> Value raise {
  let matrix = Collector::new()
  for row in cdr(mat).iter() {
    matrix.add(sheafa__select_columns(row, cols_to_take))
  }
  cons(list2(q_d_matrix, q_simp), matrix.result())
}

///|
fn d_plucker(vector_list : Value) -> Value raise {
  // (check-arg vector-list '$listp ...) asserts the quoted symbol: no check.
  let mat = cons(list1(q_d_matrix), cdr(vector_list))
  let c = Collector::new()
  for u in
    sheafa__list_tableaux(d_length(vector_list), d_length(second(vector_list))).iter() {
    c.add(d_determinant(d_sub_matrix_columns(mat, u)))
  }
  cons(list1(q_mlist), c.result())
}

///|
fn d_remove_number(llist : Value) -> Value raise {
  let c = Collector::new()
  for v in llist.iter() {
    if !numberp(v) {
      c.add(v)
    }
  }
  c.result()
}

///|
/// `(from-case a-list)` = `(and (listp a-list) (cdr (member '$case a-list)))`
fn from_case(a_list : Value) -> Value raise {
  if listp(a_list) {
    cdr(memq(q_d_case, a_list))
  } else {
    Nil
  }
}

///|
fn d_sort_solution_tree() -> Value raise {
  let st = symval(q_d_solution_tree)
  set(
    q_d_solution_tree,
    cons(
      list1(q_mlist),
      sort_list(cdr(st), (x, y) => {
        let fromx = from_case(x)
        let fromy = from_case(y)
        if fromx is Nil {
          true
        } else {
          d_monomial_alphalessp(fromx, fromy).truthy()
        }
      }),
    ),
  )
}

///|
/// `(type? a form &optional descrip)`: returns the macro expansion.  (FORM
/// is never a function object at expansion time.)
fn type_q(a : Value, form : Value, descrip? : Value = Nil) -> Value raise {
  let _ = a
  let mut ctrl = "not a ~A"
  let mut d = descrip
  if d is Nil {
    d = form
    ctrl = "Doesn't satisfy ~A"
  }
  list3(
    q_cond,
    list2(form, Nil),
    list2(t, list2(t, list2(q_merror, list4(q_format, Nil, Str(ctrl), d)))),
  )
}

///|
fn d_dichotomy(
  polynomials : Value,
  dich : Value,
  add_to_tree? : Value = Nil,
) -> Value raise {
  let mut polynomials = polynomials
  let mut dich = dich
  sheafa__check_arg(d_listp(polynomials).truthy(), "macsyma list")
  if symval(q_d_nonzero_factors).truthy() {
    format(t, "~%Assuming the following factors are nonzero and cancelling", [])
    |> ignore
    displa(symval(q_d_nonzero_factors)) |> ignore
    polynomials = d_eliminate_nonzero_factors(polynomials, Nil)
  }
  if d_listp(dich).truthy() {
    dich = second(dich)
  }
  if numberp(dich) {
    dich = nth(to_int(dich), polynomials)
  }
  let dc = Collector::new()
  for v in cdr(d_list_irreducible_factors(dich)).iter() {
    if !numberp(v) {
      dc.add(v)
    }
  }
  dich = dc.result()
  format(t, "We have the dichotomy among..", []) |> ignore
  displa(cons(list1(q_mlist), dich)) |> ignore
  let tem = Collector::new()
  let mut w = dich
  while w is Cons(_) {
    let v = car(w)
    let nz = append(
      cons(list1(q_mlist), cdr(symval(q_d_nonzero_factors))),
      cdr(w),
    )
    tem.add(
      with_special(q_d_nonzero_factors, nz, () => d_factor(
        d_eliminate_nonzero_factors(d_simplify_relative(polynomials, v), Nil),
      )),
    )
    w = cdr(w)
  }
  let answer = cons(list1(q_mlist), tem.result())
  if add_to_tree.truthy() {
    d_add_to_solution_tree(answer) |> ignore
  }
  answer
}

///|
fn constant_term(poly : Value) -> Value raise {
  if atom(poly) {
    poly
  } else {
    let leng = length(poly)
    constant_term(
      if eql(nth(leng - 2, poly), Fix(0L)) {
        constant_term(nth(leng - 1, poly))
      } else {
        Fix(0L)
      },
    )
  }
}

///|
fn gone_prepared(
  poly : Value,
  inequal? : Value = Fix(1L),
  linear_variables? : Value = Nil,
) -> Value raise {
  let mut linear_variables = linear_variables
  if linear_variables is Nil {
    linear_variables = degree_one_variables(poly)
  }
  if numberp(inequal) {
    one_prepared(poly, linear_variables~)
  } else if atom(poly) {
    Nil
  } else {
    for v in linear_variables.iter() {
      if eql(pdegree(poly, v), Fix(1L)) {
        let tem = zero_sublis(poly, v)
        if may_invertp(tem, inequal).truthy() {
          return v
        }
      }
    }
    Nil
  }
}

///|
fn degree_one_variables(poly : Value) -> Value raise {
  let c = Collector::new()
  for v in list_variables(poly).iter() {
    if eql(pdegree(poly, v), Fix(1L)) {
      c.add(v)
    }
  }
  c.result()
}

///|
fn one_prepared(poly : Value, linear_variables? : Value = Nil) -> Value raise {
  let mut linear_variables = linear_variables
  if linear_variables is Nil {
    linear_variables = degree_one_variables(poly)
  }
  if atom(poly) {
    Nil
  } else if zerop(constant_term(poly)) {
    Nil
  } else {
    for v in linear_variables.iter() {
      if eql(pdegree(poly, v), Fix(1L)) {
        let tem = zero_sublis(poly, v)
        if numberp(tem) {
          return v
        }
      }
    }
    Nil
  }
}

///|
fn gm_all_prepared(
  poly : Value,
  m? : Value = Nil,
  inequal? : Value = Fix(1L),
  linear_variables? : Value = Nil,
) -> Value raise {
  let mut linear_variables = linear_variables
  if linear_variables is Nil {
    linear_variables = degree_one_variables(poly)
  }
  if m.truthy() {
    if eql(m, Fix(0L)) {
      if may_invertp(poly, inequal).truthy() {
        list1(q_ok)
      } else {
        Nil
      }
    } else {
      let c = Collector::new()
      for v in list_variables(poly).iter() {
        if memq(v, linear_variables).truthy() {
          let tem = gm_all_prepared(
            zero_sublis(poly, v),
            linear_variables~,
            m=num_sub(m, Fix(1L)),
            inequal~,
          )
          for ww in tem.iter() {
            c.add(cons(v, ww))
          }
        }
      }
      c.result()
    }
  } else {
    linear_variables = degree_one_variables(poly)
    for i in 1..=length(linear_variables) {
      let tem = gm_all_prepared(poly, linear_variables~, m=int(i), inequal~)
      if tem.truthy() {
        return tem
      }
    }
    Nil
  }
}

///|
fn gm_prepared(
  poly : Value,
  m? : Value = Nil,
  inequal? : Value = Fix(1L),
  linear_variables? : Value = Nil,
) -> Value raise {
  let mut linear_variables = linear_variables
  if linear_variables is Nil {
    linear_variables = degree_one_variables(poly)
  }
  if m.truthy() {
    if atom(poly) {
      Nil
    } else if eql(Fix(1L), m) {
      let tem = gone_prepared(poly, inequal~, linear_variables~)
      if tem.truthy() {
        list1(tem)
      } else {
        Nil
      }
    } else {
      for v in list_variables(poly).iter() {
        if memq(v, linear_variables).truthy() {
          let tem = zero_sublis(poly, v)
          let answ = gm_prepared(
            tem,
            m=num_sub(m, Fix(1L)),
            inequal~,
            linear_variables~,
          )
          if answ.truthy() {
            return cons(v, answ)
          }
        }
      }
      Nil
    }
  } else {
    let mut lins = 0
    for v in linear_variables.iter() {
      if eql(pdegree(poly, v), Fix(1L)) {
        lins += 1
      }
    }
    let hi = num_min(int(lins), symval(q_ear_maximum_size_for_m_prepared))
    let mut i : Value = Fix(1L)
    while num_le(i, hi) {
      let answ = gm_prepared(poly, m=i, inequal~, linear_variables~)
      if answ.truthy() {
        return answ
      }
      i = num_add(i, Fix(1L))
    }
    Nil
  }
}

///|
fn m_prepared(
  poly : Value,
  m? : Value = Nil,
  linear_variables? : Value = Nil,
) -> Value raise {
  let mut linear_variables = linear_variables
  if linear_variables is Nil {
    linear_variables = degree_one_variables(poly)
  }
  if m.truthy() {
    if atom(poly) {
      Nil
    } else if zerop(constant_term(poly)) {
      Nil
    } else if eql(Fix(1L), m) {
      let tem = one_prepared(poly)
      if tem.truthy() {
        list1(tem)
      } else {
        Nil
      }
    } else {
      for v in linear_variables.iter() {
        let tem = zero_sublis(poly, v)
        let answ = m_prepared(tem, m=num_sub(m, Fix(1L)))
        if answ.truthy() {
          return cons(v, answ)
        }
      }
      Nil
    }
  } else {
    for i in 1..=length(linear_variables) {
      let answ = m_prepared(poly, m=int(i))
      if answ.truthy() {
        return answ
      }
    }
    Nil
  }
}

///|
fn non_constant_factors(poly : Value, invert? : Value = Nil) -> Value raise {
  // &aux (genvar *genvar*) binds the special GENVAR.
  with_special(q_genvar, symval(q_ear_genvar), () => {
    let tem = npfactor(poly)
    let c = Collector::new()
    for p in sheafa__pairs(tem) {
      let (v, deg) = p
      if !numberp(v) && (invert is Nil || may_invertp(v, invert) is Nil) {
        c.add(v)
        c.add(deg)
      }
    }
    c.result()
  })
}

///|
fn gen_ptimes(l : Value) -> Value raise {
  if l is Nil {
    Fix(1L)
  } else if length(l) == 1 {
    car(l)
  } else {
    ptimes(car(l), gen_ptimes(cdr(l)))
  }
}

///|
/// Does every factor of the factor list V = (fac deg ...) satisfy PRED?
fn sheafa__all_factors(v : Value, pred : (Value) -> Bool raise) -> Bool raise {
  for p in sheafa__pairs(v) {
    if !pred(p.0) {
      return false
    }
  }
  true
}

///|
fn find_good_dichotomy(ldata : Value, open_g? : Value = Fix(1L)) -> Value raise {
  let list_polys = sheafa__ldata_eqns(ldata)
  let gg = nplcm(sheafa__ldata_inequality(ldata), open_g)
  if memq(Nil, list_polys).truthy() {
    sheafa__break(sym("here"))
  }
  let mut list_factors : Value = Nil
  let multiple_factors = Collector::new()
  let all_factors = Collector::new()
  let terms = Collector::new()
  let mut unit = false
  for v in list_polys.iter() {
    // only collect non trivial factors
    let tem = non_constant_factors(v, invert=gg)
    if length(tem) > 2 {
      multiple_factors.add(tem)
    }
    // when have a constant factor
    if tem is Nil {
      sheafa__show("TEM", tem)
      sheafa__set_ldata_eqns(ldata, list1(Fix(1L))) |> ignore
      sheafa__set_ldata_usedup(ldata, Fix(1L)) |> ignore
      unit = true
      break
    }
    all_factors.add(tem)
    let facs = Collector::new()
    for p in sheafa__pairs(tem) {
      facs.add(p.0)
    }
    terms.add(gen_ptimes(facs.result()))
  }
  if unit {
    list_factors = q_done_unit_ideal
  } else {
    let terms = terms.result()
    if member(Fix(1L), terms) is Nil {
      sheafa__set_ldata_eqns(ldata, terms) |> ignore
    } else {
      sheafa__set_ldata_usedup(ldata, Fix(1L)) |> ignore
      sheafa__set_ldata_eqns(ldata, list1(Fix(1L))) |> ignore
    }
    set(q_ear_all_factors, all_factors.result()) |> ignore
    list_factors = multiple_factors.result()
  }
  if member_equal(list2(Nil, Fix(1L)), symval(q_ear_all_factors)).truthy() {
    sheafa__break(sym("hii"))
  }
  if eq(list_factors, q_done_unit_ideal) {
    return Nil
  }
  set(q_ear_factored_list, list_factors) |> ignore
  list_factors = sort_list(list_factors, (u, v) => if atom(u) {
    true
  } else if atom(v) {
    false
  } else {
    length(u) < length(v)
  })
  // grabs the shortest product a^2*b^3 where a,b are variables
  for v in list_factors.iter() {
    if sheafa__all_factors(v, fac => atom(fac) || length(fac) < 4) {
      return v
    }
  }
  let nvars = length(list_variables(list_polys))
  for i in 1..=nvars {
    for v in list_factors.iter() {
      if sheafa__all_factors(v, fac => atom(fac) ||
        length(fac) < 4 ||
        gm_prepared(fac, m=int(i), inequal=gg).truthy()) {
        return v
      }
    }
  }
  // grab the shortest one with a variable factor
  for v in list_factors.iter() {
    for p in sheafa__pairs(v) {
      if length(p.0) < 4 {
        return v
      }
    }
  }
  for v in list_factors.iter() {
    for p in sheafa__pairs(v) {
      let fac = p.0
      if one_prepared(fac).truthy() ||
        any_linearp(fac, sheafa__ldata_inequality(ldata)).truthy() {
        return v
      }
    }
  }
  Nil
}

///|
fn order_dichotomy(dich : Value) -> Value raise {
  let dc = Collector::new()
  for p in sheafa__pairs(dich) {
    dc.add(p.0)
  }
  let dich = dc.result()
  let all_factors = symval(q_ear_all_factors)
  let mc = Collector::new()
  for v in dich.iter() {
    let mut n = 0
    for u in all_factors.iter() {
      if member_equal(v, u).truthy() {
        n += 1
      }
    }
    mc.add(int(n))
  }
  let mult = mc.result()
  let res = Collector::new()
  let mut i = length(all_factors)
  while i >= 0 {
    if member(int(i), mult).truthy() {
      let mut mv = mult
      let mut dv = dich
      while mv is Cons(_) && dv is Cons(_) {
        if eql(car(mv), int(i)) {
          res.add(car(dv))
        }
        mv = cdr(mv)
        dv = cdr(dv)
      }
    }
    i -= 1
  }
  res.result()
}

///|
fn any_linearp(
  f : Value,
  g : Value,
  variables_to_exclude? : Value = Nil,
  among_variables? : Value = Nil,
) -> Value raise {
  let mut among_variables = among_variables
  if among_variables is Nil {
    among_variables = list_variables(f)
  }
  for v in among_variables.iter() {
    if memq(v, variables_to_exclude) is Nil && poly_linearp(f, v, g).truthy() {
      return v
    }
  }
  Nil
}

///|
fn any_invertible_leading_coefficient(f : Value, g : Value) -> Value raise {
  let mut varl = list_variables(f)
  for v in varl.iter() {
    if may_invertp(list3(v, Fix(1L), Fix(1L)), g).truthy() {
      varl = remove_equal(v, varl)
    }
  }
  let mut deg : Value = Nil
  for v in varl.iter() {
    let clear_above = symval(q_ear_clear_above)
    let ok = if clear_above is Nil {
      true
    } else {
      // (loop ... minimize (cdr w)) is 0 when nothing matches
      let mut the_min : Value? = None
      for w in clear_above.iter() {
        if eq(car(w), v) {
          the_min = Some(
            match the_min {
              None => cdr(w)
              Some(m) => num_min(m, cdr(w))
            },
          )
        }
      }
      let mn = the_min.unwrap_or(Fix(0L))
      deg = pdegree(f, v)
      !num_le(mn, deg)
    }
    if ok && may_invertp(pcoeff(f, list3(v, deg, Fix(1L))), g).truthy() {
      return v
    }
  }
  Nil
}

///|
fn invertible_leading_coefficient(
  poly : Value,
  var_ : Value,
  inequal : Value,
) -> Value raise {
  may_invertp(pcoeff(poly, list3(var_, pdegree(poly, var_), Fix(1L))), inequal)
}

///|
fn plength_order(u : Value, v : Value) -> Value raise {
  if atom(u) {
    t
  } else if atom(v) {
    Nil
  } else {
    lbool(length(u) < length(v))
  }
}

///|
fn replace_functions(
  list_to_replace : Value,
  f : Value,
  var_ : Value,
  general_leading_cof? : Value = Nil,
  invertible_g? : Value = Fix(1L),
) -> Value raise {
  let c = Collector::new()
  if general_leading_cof is Nil {
    for h in list_to_replace.iter() {
      if !eql(f, h) {
        let tem = gen_prem(h, f, var_).0
        if pzerop(tem) is Nil {
          if !eq(h, tem) {
            c.add(square_free(tem))
          } else {
            c.add(h)
          }
        }
      }
    }
  } else {
    // (multiple-value (remaind c-reqd) (gen-prem h f var)) is the Maclisp
    // MULTIPLE-VALUE-SETQ.
    let mut remaind : Value = Nil
    let mut c_reqd : Value = Nil
    for h0 in list_to_replace.iter() {
      let mut h = h0
      if eq(f, h) {
        h = Nil
      }
      if h.truthy() {
        let (r, cr) = gen_prem(h, f, var_)
        remaind = r
        c_reqd = cr
      }
      if h.truthy() {
        if eq(h, remaind) {
          c.add(h)
        } else {
          c.add(square_free(remaind))
        }
      }
      // collect h if the c-reqd is not a unit.
      if h.truthy() && may_invertp(c_reqd, invertible_g) is Nil {
        c.add(h)
      }
    }
  }
  c.result()
}

///|
fn any_gm_prepared(poly : Value, gg : Value) -> Value raise {
  gm_prepared(poly, inequal=gg)
}

///|
fn check_for_gm_prepared(list_eqns : Value, gg : Value) -> Value raise {
  for eqn in list_eqns.iter() {
    if any_linearp(eqn, gg) is Nil {
      let tem = gm_prepared(eqn, inequal=gg)
      if tem.truthy() {
        set(q_ear_stop_simplify, list2(eqn, int(length(tem)))) |> ignore
        break
      }
    }
  }
  symval(q_ear_stop_simplify)
}

///|
/// `(check-containments ldata lis-ldat &optional gg)`: returns the macro
/// expansion.
fn check_containments(
  ldata : Value,
  lis_ldat : Value,
  gg? : Value = Nil,
) -> Value raise {
  list2(
    q_cond,
    list2(
      sym("error-check-containments"),
      list4(q_check_component_containment, ldata, lis_ldat, gg),
    ),
  )
}

///|
fn ldata_simplifications(
  ldata : Value,
  open_g? : Value = Fix(1L),
  error_check_containments? : Value = Nil,
  recursive_p? : Value = Nil,
) -> Value raise {
  // &aux *clear-above* binds the special.
  let b = bind(q_ear_clear_above, Nil)
  defer unbind(b)
  let check_containments = fn(ld : Value, lis : Value, gg : Value) raise {
    if error_check_containments.truthy() {
      check_component_containment(ld, lis, open_g=gg) |> ignore
    }
  }
  sheafa__check_arg(eq(car(ldata), q_ldata), "not an ldata")
  let orig_ldata = ldata
  let ldata = copy_list(ldata)
  let mut answ : Value = Nil
  {
    let mut fns = sheafa__ldata_eqns(ldata)
    let mut gg = sheafa__ldata_inequality(ldata)
    gg = nplcm(open_g, gg)
    // note that using this gg we may produce I1 with I ^P I1R[gg-1] but
    // unless I1 is prime we will not have I ^P I1
    let c = Collector::new()
    let mut early = false
    for f in fns.iter() {
      if !(numberp(f) && zerop(f)) {
        let tem = square_free(remove_common_factors(f, gg))
        if numberp(tem) {
          sheafa__set_ldata_usedup(ldata, Fix(1L)) |> ignore
          early = true
          break
        } else {
          c.add(tem)
        }
      }
    }
    fns = if early { list1(Fix(1L)) } else { c.result() }
    let usedup = to_int(sheafa__ldata_usedup(ldata))
    let mut used_up = subseq(fns, 0, end=usedup)
    fns = nthcdr(usedup, fns)
    fns = sort_list(copy_list(fns), (a, b) => plength_order(a, b).truthy())
    set(q_vars, list_variables(fns)) |> ignore
    let mut changed = true
    while changed {
      changed = false
      let tests = [q_any_linearp, q_any_invertible_leading_coefficient]
      for test_ in tests {
        let mut found = false
        for f in fns.iter() {
          let var_ = if eq(test_, q_any_linearp) {
            any_linearp(f, gg)
          } else {
            any_invertible_leading_coefficient(f, gg)
          }
          if var_.truthy() {
            fns = replace_functions(fns, f, var_)
            used_up = replace_functions(used_up, f, var_)
            if eq(test_, q_any_linearp) ||
              variable_doesnt_occur(var_, list2(fns, used_up)).truthy() {
              used_up = cons(f, used_up)
            } else {
              // put f last so that the lower degree ones will come first.
              fns = nconc(fns, list1(f))
            }
            if eq(test_, q_any_invertible_leading_coefficient) {
              set(
                q_ear_clear_above,
                cons(cons(var_, pdegree(f, var_)), symval(q_ear_clear_above)),
              )
              |> ignore
              sheafa__show("*CLEAR-ABOVE*", symval(q_ear_clear_above))
            }
            changed = true
            found = true
            break
          }
        }
        if found {
          break
        }
      }
    }
    // if contain number 'done else try to fix leading cofs
    if error_check_containments.truthy() {
      check_containments(
        orig_ldata,
        list1(
          sheafa__make_ldata(
            eqns=zl_union(list2(fns, used_up)),
            inequality=sheafa__ldata_inequality(orig_ldata),
          ),
        ),
        Nil,
      )
    }
    let mut unused = zl_union(list1(delete(Fix(0L), fns)))
    let mut done = false
    for f in unused.iter() {
      if numberp(f) {
        used_up = list1(Fix(1L))
        unused = Nil
        done = true
        break
      }
    }
    if !done {
      let simplif = simp_lead(unused, open_g=gg)
      if !eq(simplif, q_try_dichotomy) {
        unused = zl_union(list1(simplif))
      }
    }
    sheafa__set_ldata_inequality(ldata, gg) |> ignore
    fns = append(used_up, unused)
    sheafa__set_ldata_eqns(ldata, fns) |> ignore
    sheafa__set_ldata_usedup(ldata, int(length(used_up))) |> ignore
    // the following may make *stop-simplify* and ask to refine.
    if error_check_containments.truthy() {
      check_containments(
        orig_ldata,
        list1(ldata),
        sheafa__ldata_inequality(ldata),
      )
    }
    if symval(q_ear_stop_simplify) is Nil {
      answ = make_dichotomy(ldata, open_g~)
    } else {
      answ = list1(ldata)
    }
    // should make this so it won't check for redundant ldata more than once.
    if length(answ) > 1 {
      answ = delete_redundant_ldata(answ, gg=open_g)
    }
  }
  check_containments(orig_ldata, answ, Nil)
  // this makes the divide dichotomy only apply after no more prod. dichot.
  if symval(q_ear_stop_simplify) is Nil && length(answ) == 1 {
    answ = divide_dichotomy(car(answ), open_g~)
  }
  check_containments(orig_ldata, answ, Nil)
  if symval(q_ear_stop_simplify) is Nil && length(answ) == 1 {
    answ = try_factor_irreducible_ldata(car(answ), open_g~)
  }
  if symval(q_ear_stop_simplify) is Nil && recursive_p is Nil {
    let b2 = bind(q_ear_in_linear_dich, t)
    defer unbind(b2)
    let c = Collector::new()
    for ld in answ.iter() {
      for x in linear_dichotomy(ld, open_g~).iter() {
        c.add(x)
      }
    }
    answ = c.result()
  }
  check_containments(orig_ldata, answ, Nil)
  answ = delete_redundant_ldata(answ, gg=open_g)
  check_containments(orig_ldata, answ, Nil)
  answ
}

///|
fn any_irreducible(f : Value, gg : Value) -> Value raise {
  let fac = non_constant_factors(f, invert=gg)
  if length(fac) > 2 {
    Nil
  } else {
    car(fac)
  }
}

///|
fn leading_cof(poly : Value, var_ : Value) -> Value raise {
  let deg = pdegree(poly, var_)
  if zerop(deg) {
    Fix(0L)
  } else {
    pcoeff(poly, list3(var_, pdegree(poly, var_), Fix(1L)))
  }
}

///|
fn find_variable_with_simple_lc(
  f : Value,
  fns : Value,
  gg : Value,
) -> Value raise {
  let _ = fns
  let _ = gg
  let varl = list_variables(f)
  let tem = mapcar(v => pcomplexity(leading_cof(f, v)), varl)
  if tem is Nil {
    raise LispError::SimpleError(
      "invalid number of arguments: 0 (MIN needs at least one)",
    )
  }
  let mut mn = car(tem)
  for x in cdr(tem).iter() {
    mn = num_min(mn, x)
  }
  nth(to_int(find_position_in_list(mn, tem)), varl)
}

///|
fn ldata_unused(ld : Value) -> Value raise {
  nthcdr(to_int(sheafa__ldata_usedup(ld)), sheafa__ldata_eqns(ld))
}
