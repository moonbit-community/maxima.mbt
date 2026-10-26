// Port of share/affine/polya.lisp (part 2): linear equations from
// non-commutative polynomials, fast_linsolve, monomials and central
// elements.

///|
fn d_extract_linear_equations(
  equations : Value,
  independent_monomials? : Value,
) -> Value raise {
  let independent_monomials = match independent_monomials {
    Some(v) => v
    None => d_list_nc_monomials(equations)
  }
  check_arg(equations, q_d_listp, list1(Str("A Macsyma List"))) |> ignore
  for v in cdr(equations).iter() {
    if !(atom(v) || !equal(caar(v), q_mequal)) {
      raise LispError::SimpleError(
        "The assertion (OR (ATOM V) (NOT (EQUAL (CAAR V) 'MEQUAL))) failed.",
      )
    }
  }
  cons(
    list1(q_mlist),
    mapcar(
      x => new_disrep(x),
      extract_linear_equations(
        st_rat(equations),
        tem=st_rat(independent_monomials),
      ),
    ),
  )
}

///|
fn extract_linear_equations(
  list_eqns : Value,
  tem? : Value = Nil,
  all_ind_mons? : Value = Nil,
) -> Value raise {
  ignore(tem)
  let mut ind_mons = all_ind_mons
  let c = Collector::new()
  for v0 in list_eqns.iter() {
    let mut v = v0
    if affine_polynomialp(v).truthy() {
      ()
    } else if rational_functionp(v).truthy() {
      v = function_numerator(v)
    } else {
      fsignal(
        list1(
          Str("list-eqns should be a list of polynomials or rational functions"),
        ),
      )
      |> ignore
    }
    if all_ind_mons is Nil {
      let varl = list_variables(list_eqns)
      let mon = list3(Nil, Fix(1L), Fix(1L))
      let im = Collector::new()
      for vv in varl.iter() {
        setf_car(mon, vv) |> ignore
        if poly_scalarp(mon) is Nil {
          im.add(vv)
        }
      }
      ind_mons = im.result()
    }
    for va in ind_mons.iter() {
      let tem = pcoeff(v, list3(va, Fix(1L), Fix(1L)))
      if pzerop(tem) is Nil {
        c.add(tem)
      }
    }
  }
  c.result()
}

///|
fn member_even(item : Value, a_list : Value) -> Value raise {
  let mut lis : Value = Nil
  let mut answer : Value = Nil
  if length(a_list) % 2 == 0 {
    lis = a_list
  } else {
    lis = butlast(a_list)
    if equal(car(last(a_list)), item) {
      answer = item
    }
  }
  if answer is Nil {
    while lis.truthy() {
      if equal(item, car(lis)) {
        return item
      }
      lis = cddr(lis)
    }
    Nil
  } else {
    answer
  }
}

///|
fn initial_segment_is_replaced(a_list : Value) -> Value raise {
  if atom(a_list) {
    member_even(a_list, cdr(symval(q_d_dot_simplifications)))
  } else {
    for i in 1..=length(a_list) {
      if member_even(
          subseq(a_list, 0, end=i),
          cdr(symval(q_d_dot_simplifications)),
        ).truthy() {
        return t
      }
    }
    Nil
  }
}

///|
/// Returns first value nc-part of monomial and second value the sc-part if
/// that can be obtained without consing, nil otherwise. It uses the scalar
/// property to check if a single atom is scalar or not, with things like
/// ((mexpt simp) z 2) always assumed scalar. If there are two non-scalars
/// * together it only takes the first one. If there are two ((mnctimes
/// ..)) it only takes the first one.
fn d_extract_nc_part(monomial : Value) -> (Value, Value) raise {
  let mut nc_part : Value = Nil
  let mut sc_part : Value = Nil
  if atom(monomial) {
    if d_scalarp(monomial).truthy() {
      nc_part = Fix(1L)
      sc_part = monomial
    } else {
      nc_part = monomial
      sc_part = Fix(1L)
    }
  } else {
    let op = caar(monomial)
    if eq(op, q_mtimes) {
      for u in cdr(monomial).iter() {
        if !atom(u) && eq(caar(u), q_mnctimes) {
          nc_part = u
          if length(monomial) == 3 {
            if eq(second(monomial), u) {
              sc_part = third(monomial)
            } else {
              sc_part = second(monomial)
            }
          }
          break
        }
      }
      if nc_part is Nil {
        for u in cdr(monomial).iter() {
          if atom(u) && d_scalarp(u) is Nil {
            nc_part = u
            if length(monomial) == 3 {
              if eq(second(monomial), u) {
                sc_part = third(monomial)
              } else {
                sc_part = second(monomial)
              }
            }
            break
          }
        }
      }
      if nc_part is Nil {
        nc_part = Fix(1L)
        sc_part = monomial
      }
    } else if eq(op, q_mnctimes) {
      nc_part = monomial
      sc_part = Fix(1L)
    } else if eq(op, q_mexpt) {
      nc_part = Fix(1L)
      sc_part = monomial
    } else {
      raise LispError::SimpleError(
        format_to_string("~A is not a product", [monomial]),
      )
    }
  }
  (nc_part, sc_part)
}

///|
fn extract_nc_and_sc_parts(monomial : Value) -> (Value, Value) raise {
  let (nc_part, sc_part0) = d_extract_nc_part(monomial)
  let mut sc_part = sc_part0
  if sc_part is Nil {
    let c = Collector::new()
    for u in monomial.iter() {
      if !eq(u, nc_part) {
        c.add(u)
      }
    }
    sc_part = c.result()
    if length(sc_part) == 2 {
      sc_part = cadr(sc_part)
    }
  }
  (nc_part, sc_part)
}

///|
fn d_extract_nc_and_sc_parts(monomial : Value) -> Value raise {
  let (nc_part, sc_part) = extract_nc_and_sc_parts(monomial)
  cons(list2(q_mlist, q_simp), list2(nc_part, sc_part))
}

///|
fn d_setfy(a_list : Value) -> Value raise {
  let c = Collector::new()
  let mut tem : Value = Nil
  for v in a_list.iter() {
    if member_equal(v, tem) is Nil {
      c.add(v)
      tem = c.result()
    }
  }
  c.result()
}

///|
fn d_list_nc_monomials(expr : Value) -> Value raise {
  if atom(expr) {
    list1(list2(q_mlist, q_simp))
  } else if eq(caar(expr), q_mnctimes) {
    list2(list2(q_mlist, q_simp), expr)
  } else if memq(caar(expr), list3(q_mlist, q_mequal, q_d_matrix)).truthy() {
    let c = Collector::new()
    for u in cdr(expr).iter() {
      c.append_list(copy_list(cdr(d_list_nc_monomials(u))))
    }
    cons(list2(q_mlist, q_simp), d_setfy(c.result()))
  } else {
    let expr = d_expand(expr)
    if eq(caar(expr), q_mplus) {
      let a_list = Collector::new()
      for u in cdr(expr).iter() {
        let answer = extract_nc_and_sc_parts(u).0
        if member_equal(answer, a_list.result()) is Nil {
          a_list.add(answer)
        }
      }
      cons(list2(q_mlist, q_simp), a_list.result())
    } else if eq(caar(expr), q_mtimes) {
      cons(list2(q_mlist, q_simp), list1(extract_nc_and_sc_parts(expr).0))
    } else {
      list1(list2(q_mlist, q_simp))
    }
  }
}

///|
fn d_reverse_equation(eqn : Value) -> Value raise {
  if atom(eqn) {
    eqn
  } else if eq(caar(eqn), q_mequal) {
    list3(car(eqn), third(eqn), second(eqn))
  } else {
    eqn
  }
}

///|
fn nc_monomial_table(monom : Value) -> Value raise {
  if atom(monom) {
    monom
  } else if atom(car(monom)) {
    monom
  } else if eq(caar(monom), q_mnctimes) {
    let table = symval(q_ear_monomial_table)
    let repl = gethash(monom, table)
    if repl.truthy() {
      copy_tree(repl)
    } else {
      let repl = d_rat(monom, list1(monom))
      sethash(monom, table, repl) |> ignore
      copy_tree(repl)
    }
  } else {
    monom
  }
}

///|
fn new_rat_ncmul(list_of_terms : Value) -> Value raise {
  let list_of_terms = copy_list(list_of_terms)
  let mut denom_ : Value = Fix(1L)
  let mut i = 0
  for v in list_of_terms.iter() {
    if !numberp(v) &&
      (affine_polynomialp(v).truthy() || rational_functionp(v).truthy()) {
      if rational_functionp(v).truthy() {
        denom_ = denom(v)
      }
      return cons(
        poly_ncmul1(
          ncmuln(subseq(list_of_terms, 0, end=i), Nil),
          num(v),
          ncmuln(nthcdr(i + 1, list_of_terms), Nil),
        ),
        denom_,
      )
    }
    i += 1
  }
  ncmuln(list_of_terms, Nil)
}

///|
fn rat_ncmul(list_of_terms : Value) -> Value raise {
  let list_of_terms = copy_list(list_of_terms)
  let mut i = 0
  for v in list_of_terms.iter() {
    if d_ratp(v).truthy() {
      return ncmul1(
        ncmuln(subseq(list_of_terms, 0, end=i), Nil),
        v,
        ncmuln(nthcdr(i + 1, list_of_terms), Nil),
      )
    }
    i += 1
  }
  ncmuln(list_of_terms, Nil)
}

///|
fn ncmul1(mon : Value, expr : Value, mon1 : Value) -> Value raise {
  let expr = minimize_varlist(expr)
  let tem = Collector::new()
  for v in third(car(expr)).iter() {
    if fast_scalarp(v) is Nil {
      tem.add(ncmul_star(list3(mon, v, mon1)))
    } else {
      tem.add(v)
    }
  }
  cons(list4(q_mrat, q_simp, tem.result(), fourth(car(expr))), cdr(expr))
}

///|
fn mysub(expr : Value, replacement_function : Value) -> Value raise {
  mysub1(copy_tree(expr), replacement_function)
}

///|
fn mysub1(vv : Value, h : Value) -> Value raise {
  if atom(vv) {
    funcall(h, [vv]) |> ignore
  } else {
    rplaca(vv, funcall(h, [car(vv)])) |> ignore
    rplacd(vv, funcall(h, [cdr(vv)])) |> ignore
  }
  if atom(vv) {
    vv
  } else {
    rplaca(vv, mysub1(car(vv), h)) |> ignore
    if !eq(car(vv), q_mrat) {
      rplacd(vv, mysub1(cdr(vv), h))
    } else {
      vv
    }
  }
}

///|
fn max_for_pred(a_list : Value, pred : Value) -> Value raise {
  let mut w = car(a_list)
  for v in a_list.iter() {
    if funcall(pred, [v, w]).truthy() {
      w = v
    }
  }
  w
}

///|
fn d_nc_rat(expr : Value) -> Value raise {
  let monoms = cdr(d_list_nc_monomials(expr))
  d_rat(expr, monoms)
}

///|
fn d_re_rat_the_dot_simplifications() -> Value raise {
  let c = Collector::new()
  let mut i = 1
  for v in cdr(symval(q_d_dot_simplifications)).iter() {
    if i % 2 == 0 {
      c.add(minimize_varlist(d_new_rat(new_disrep(cdr(v)))))
    } else {
      c.add(v)
    }
    i += 1
  }
  cons(list2(q_mlist, q_simp), c.result())
}

///|
fn show_genvar(a_list? : Value) -> Value raise {
  let a_list = match a_list {
    Some(v) => v
    None => symval(q_genvar)
  }
  for v in a_list.iter() {
    format(t, "~%~A disreps ~A value ~A", [
      v,
      get(v, q_disrep),
      symbol_value(v),
    ])
    |> ignore
  }
  Nil
}

///|
/// EXPR should be somewhat expanded. The result of ($multthru expr) is ok.
fn find_worst_nc_monomial(expr : Value) -> (Value, Value, Value) raise {
  let mut expr = expr
  let mut answer : Value = Nil
  let mut coefficient : Value = Nil
  let mut answeru : Value = Nil
  let mut repeat_flag : Value = Nil
  if d_ratp(expr).truthy() {
    let mut the_worst : Value = Nil
    let mut v = third(car(expr))
    let mut gv = fourth(car(expr))
    while v is Cons(_) && gv is Cons(_) {
      if d_scalarp(car(v)) is Nil &&
        appears_in(cdr(expr), car(gv)).truthy() &&
        (the_worst is Nil ||
        funcall(symval(q_d_order_function), [the_worst, car(v)]).truthy()) {
        the_worst = car(v)
      }
      v = cdr(v)
      gv = cdr(gv)
    }
    answer = the_worst
    coefficient = d_nc_coeff(expr, answer)
  } else if d_plusp(expr) is Nil && appears_in(expr, q_mplus).truthy() {
    expr = d_multthru(d_ratsimp(d_expand(expr), Nil))
    format(
      t,
      "~%find-worst-nc-monomial was applied to a non sum.  Expanding and continuing with ",
      [],
    )
    |> ignore
    displa(expr) |> ignore
  }
  if d_ratp(expr).truthy() {
    ()
  } else if atom(expr) {
    answer = expr
    coefficient = Fix(1L)
    answeru = expr
  } else if eq(caar(expr), q_mnctimes) {
    answer = expr
    coefficient = Fix(1L)
    answeru = expr
  } else if eq(caar(expr), q_mplus) {
    let mut ans1 : Value = Nil
    for u in cdr(expr).iter() {
      if answer is Nil {
        answeru = u
        let (a, c) = polya__multiple_value2("ANSWER")
        answer = a
        coefficient = c
      } else {
        let (a1, cof) = polya__multiple_value2("ANS1")
        ans1 = a1
        if funcall(symval(q_d_order_function), [answer, ans1]).truthy() {
          answer = ans1
          coefficient = cof
          answeru = u
        } else if equal(ans1, answer) {
          repeat_flag = answer
        }
      }
    }
  } else if eq(caar(expr), q_mtimes) {
    let (a, c) = polya__multiple_value2("ANSWER")
    answer = a
    coefficient = c
    answeru = expr
  }
  if equal(repeat_flag, answer) {
    coefficient = d_nc_coeff(expr, answer)
    answeru = mul_star(list2(coefficient, answer))
    if d_zerop(coefficient).truthy() {
      format(t, "~%Having to ratsimp expression of length ~A", [
        int(length(expr)),
      ])
      |> ignore
      let tem1 = d_multthru(d_ratsimp(expr, Nil))
      if fast_scalarp(tem1).truthy() {
        coefficient = tem1
        answeru = tem1
        answer = Fix(1L)
        format(t, "...it was scalar", []) |> ignore
      } else {
        format(t, "...starting to look for worst monomial again", []) |> ignore
        let (a, c, u) = polya__multiple_value3("ANSWER")
        answer = a
        coefficient = c
        answeru = u
      }
    }
  }
  amacros__show("ANSWER", answer)
  (answer, coefficient, answeru)
}

///|
fn d_my_nc_coef(expr : Value, var_ : Value) -> Value raise {
  check_arg(expr, q_d_plusp, list1(Str("macsyma sum"))) |> ignore
  let c = Collector::new()
  for v in cdr(expr).iter() {
    let (answer, coeff) = polya__multiple_value2("ANSWER")
    if equal(var_, answer) {
      c.add(coeff)
    }
  }
  d_ratsimp(cons(list1(q_mplus), c.result()), Nil)
}

///|
fn d_sump(x : Value) -> Value raise {
  lbool(consp(x) && eq(caar(x), q_mplus))
}

///|
fn d_nc_coeff(expr : Value, monom : Value, deg? : Value = Fix(1L)) -> Value raise {
  let answer : Value = if atom(expr) {
    if eq(monom, expr) {
      Fix(1L)
    } else {
      Fix(0L)
    }
  } else {
    let op = caar(expr)
    if eq(op, q_mtimes) {
      if appears_in(expr, monom).truthy() {
        let mut tem1 : Value = Nil
        let the_rest = Collector::new()
        for v in cdr(expr).iter() {
          if appears_in(v, monom).truthy() {
            tem1 = v
          } else {
            the_rest.add(v)
          }
        }
        mul_star(list2(mul_star(the_rest.result()), d_nc_coeff(tem1, monom)))
      } else {
        Fix(0L)
      }
    } else if eq(op, q_mplus) {
      let tem1 = Collector::new()
      for v in cdr(expr).iter() {
        if appears_in(v, monom).truthy() {
          tem1.add(v)
        }
      }
      let tem1 = tem1.result()
      if tem1.truthy() {
        add_star(mapcar(w => d_nc_coeff(w, monom), tem1))
      } else {
        Fix(0L)
      }
    } else if eq(op, q_mexpt) {
      Fix(0L)
    } else if eq(op, q_rat) {
      if appears_in(cdr(expr), monom).truthy() {
        div_star(d_nc_coeff(second(expr), monom), third(expr))
      } else {
        Nil
      }
    } else if eq(op, q_mnctimes) {
      if equal(cdr(monom), cdr(expr)) {
        Fix(1L)
      } else {
        Nil
      }
    } else if eq(op, q_mrat) {
      my_ratcoeff(expr, monom, deg~)
    } else {
      raise LispError::SimpleError(
        format_to_string("invalid expression~A", [expr]),
      )
    }
  }
  if answer.truthy() {
    answer
  } else {
    Fix(0L)
  }
}

///|
fn number_and_zerop(x : Value) -> Value raise {
  lbool(numberp(x) && zerop(x))
}

///|
fn ncsimp(expr : Value) -> Value raise {
  if d_scalarp(expr).truthy() {
    expr
  } else if atom(expr) {
    expr
  } else if member(q_ncsimp, car(expr)).truthy() {
    // the Lisp clause is ((member 'ncsimp (car expr)) expr :test #'eq)
    q_kw_test
  } else {
    let nc_monoms = d_list_nc_monomials(expr)
    let the_sum = Collector::new()
    for vv in cdr(nc_monoms).iter() {
      the_sum.add(mul_star(list2(vv, d_ratsimp(d_nc_coeff(expr, vv), Nil))))
    }
    let the_sum = the_sum.result()
    if length(cdr(nc_monoms)) > 1 {
      rplaca(add_star(the_sum), list3(q_mplus, q_simp, q_ncsimp))
    } else {
      car(the_sum)
    }
  }
}

///|
fn d_independent_linsolve(
  eqns : Value,
  independent_monomials : Value,
  unknowns? : Value = Nil,
) -> Value raise {
  let equations = d_extract_linear_equations(
    eqns,
    independent_monomials=independent_monomials,
  )
  if symval(q_d_fast_solve).truthy() {
    d_fast_linsolve(equations, variables=unknowns)
  } else {
    let unknowns = if unknowns is Nil {
      d_list_of_variables(equations)
    } else {
      unknowns
    }
    d_linsolve(equations, unknowns)
  }
}

///|
fn d_extr_eqns(
  eqns : Value,
  independent_monomials : Value,
  unknowns? : Value = Nil,
) -> Value raise {
  let equations = d_extract_linear_equations(
    eqns,
    independent_monomials=independent_monomials,
  )
  let unknowns = if unknowns is Nil {
    d_list_of_variables(equations)
  } else {
    unknowns
  }
  macsyma_list(list2(equations, unknowns))
}

///|
fn d_nc_coefficients(eqns : Value) -> Value raise {
  let rat_subs = d_tellrat(Nil)
  let ans = d_extr_eqns(eqns, d_list_nc_monomials(eqns))
  let mut vars = third(ans)
  for v in list_to_array(cdr(vars)) {
    if d_constantp(v).truthy() || appears_in(rat_subs, v).truthy() {
      vars = polyc__delete_equal(v, vars)
    }
  }
  list3(list2(q_mlist, q_simp), second(ans), vars)
}

///|
fn d_find_relations_in_free_ring(a_list : Value) -> Value raise {
  check_arg(a_list, q_d_listp, list1(Str("macsyma list"))) |> ignore
  let gen_sum = d_general_sum(a_list, coefficients=symval(q_d_aaaa)).0
  let eqns = d_nc_coefficients(list2(list2(q_mlist, q_simp), gen_sum))
  let answers = d_fast_linsolve(eqns)
  let temm = Collector::new()
  let n = to_int(d_length(cdr(a_list)))
  for i in 1..=n {
    temm.add(d_concat(list2(q_d_term, int(i))))
  }
  let repr = d_sublis(
    answers,
    d_general_sum(
      cons(list1(q_mlist), temm.result()),
      coefficients=symval(q_d_aaaa),
    ).0,
  )
  list3(list2(q_mlist, q_simp), repr, answers)
}

///|
fn d_list_of_variables(l : Value) -> Value raise {
  with_special(q_variables, Nil, () => {
    if atom(l) {
      raise LispError::SimpleError(format_to_string("~A is not a list", [l]))
    } else {
      aux_to_list_of_variables(l, q_variables) |> ignore
    }
    cons(list2(q_mlist, q_simp), symval(q_variables))
  })
}

///|
fn aux_to_list_of_variables(l : Value, var1 : Value) -> Value raise {
  if atom(l) {
    if l.truthy() &&
      !numberp(l) &&
      memq(
        l,
        list([
          q_simp, q_mtimes, q_mplus, q_mexpt, q_mlist, q_mrat, q_rat, q_mnctimes,
          q_mncexpt, q_mequal, q_d_matrix,
        ]),
      )
      is Nil &&
      memq(l, symbol_value(var1)) is Nil {
      set(var1, cons(l, symbol_value(var1)))
    } else {
      Nil
    }
  } else {
    for u in l.iter() {
      aux_to_list_of_variables(u, var1) |> ignore
    }
    Nil
  }
}

///|
fn create_list2(form : Value, l : Value) -> Value raise {
  cons(list1(q_mlist), create_list1(form, l))
}

///|
fn d_general_sum(terms : Value, coefficients? : Value = Nil) -> (Value, Value) raise {
  let mut coefficients = coefficients
  if coefficients is Nil {
    coefficients = create_list2(
      list3(q_d_concat, list2(q_quote, q_d_aa), q_i),
      list3(q_i, Fix(1L), int(length(terms) - 1)),
    )
    mfuncall(q_d_declare_scalar_list, list1(coefficients)) |> ignore
  }
  if length(terms) > length(coefficients) {
    raise LispError::SimpleError("not enough coefficients")
  }
  let mut sum : Value = Fix(0L)
  let mut u = cdr(terms)
  let mut v = cdr(coefficients)
  while u is Cons(_) && v is Cons(_) {
    sum = add_star(list2(sum, mul_star(list2(car(u), car(v)))))
    u = cdr(u)
    v = cdr(v)
  }
  (sum, coefficients)
}

///|
fn a_less(u : Value, v : Value) -> Value raise {
  lbool(alphalessp(u, v).truthy() || eq(u, v))
}

///|
/// The DEFREMEMBER memory: the :memory-table property of F, created on
/// first use (the first call computes without remembering, as the
/// expansion of DEFREMEMBER does).
fn polya__remember(
  f : Value,
  key : () -> Value raise,
  body : () -> Value raise,
) -> Value raise {
  if get(f, q_kw_dont_remember).truthy() {
    return body()
  }
  let hash_table = get(f, q_kw_memory_table)
  if hash_table.truthy() {
    let k = key()
    let ans = gethash(k, hash_table)
    if ans.truthy() {
      ans
    } else {
      let ans = body()
      sethash(key(), hash_table, ans) |> ignore
      ans
    }
  } else {
    putprop(f, make_hash_table(kind=Equal), q_kw_memory_table) |> ignore
    Nil
  }
}

///|
/// `(defremember commutative-monomials (a-list n &optional
/// (type-of-weight :weight) (reset nil)) ...)`
fn polya__commutative_monomials(
  a_list : Value,
  n : Value,
  type_of_weight : Value,
  reset : Value,
) -> Value raise {
  let key : () -> Value raise = () => list4(a_list, n, type_of_weight, reset)
  let body : () -> Value raise = () => {
    if reset.truthy() {
      remprop(q_commutative_monomials, q_kw_memory_table) |> ignore
    }
    if eql(n, Fix(0L)) {
      Nil
    } else if eql(n, Fix(1L)) {
      let tem = Collector::new()
      for v in a_list.iter() {
        if eql(n, degree(v, type_of_weight~)) {
          tem.add(list1(v))
        }
      }
      tem.result()
    } else {
      let tem = Collector::new()
      for v in a_list.iter() {
        if eql(n, degree(v, type_of_weight~)) {
          tem.add(list1(v))
        }
      }
      let atomic_terms = tem.result()
      let tem1 = Collector::new()
      for v in a_list.iter() {
        let ws = polya__commutative_monomials(
          a_list,
          num_sub(n, degree(v, type_of_weight~)),
          type_of_weight,
          Nil,
        )
        for w in ws.iter() {
          if a_less(v, car(w)).truthy() {
            tem1.add(cons(v, w))
          }
        }
      }
      append(atomic_terms, tem1.result())
    }
  }
  if get(q_commutative_monomials, q_kw_dont_remember).truthy() {
    return body()
  }
  if get(q_commutative_monomials, q_kw_memory_table).truthy() {
    polya__remember(q_commutative_monomials, key, body)
  } else {
    putprop(q_commutative_monomials, make_hash_table(kind=Equal), q_kw_memory_table)
    |> ignore
    polya__commutative_monomials(a_list, n, type_of_weight, reset)
  }
}

///|
fn degree(a_list : Value, type_of_weight? : Value = q_kw_weight) -> Value raise {
  if atom(a_list) {
    let tem = get(a_list, type_of_weight)
    if tem.truthy() {
      tem
    } else {
      Fix(1L)
    }
  } else {
    let mut answer : Value = Fix(0L)
    for v in a_list.iter() {
      let tem = get(v, type_of_weight)
      answer = num_add(
        answer,
        if tem.truthy() {
          tem
        } else {
          Fix(1L)
        },
      )
    }
    answer
  }
}

///|
fn d_commutative_dot_monomials(a_list : Value, degree : Value) -> Value raise {
  let answer = polya__commutative_monomials(cdr(a_list), degree, q_kw_weight, t)
  let answer = mapcar(u => cons(list1(q_mnctimes), u), answer)
  cons(list2(q_mlist, q_simp), answer)
}

///|
fn d_declare_scalar_list(l : Value) -> Value raise {
  let fn_ = get(q_d_declare, q_mfexpr_star)
  if fn_.truthy() {
    for u in cdr(l).iter() {
      funcall(fn_, [list3(Nil, u, q_d_scalar)]) |> ignore
    }
  } else {
    for u in cdr(l).iter() {
      meval(list3(list1(q_d_declare), u, q_d_scalar)) |> ignore
    }
  }
  Nil
}

///|
fn d_plusp(x : Value) -> Value raise {
  lbool(consp(x) && consp(car(x)) && eq(caar(x), q_mplus))
}

///|
fn d_list_nc_parts(f : Value) -> Value raise {
  if numberp(f) {
    Nil
  } else if atom(f) {
    if d_scalarp(f).truthy() {
      Nil
    } else {
      f
    }
  } else if eq(caar(f), q_mnctimes) {
    f
  } else if eq(caar(f), q_mtimes) {
    d_extract_nc_part(f).0
  } else {
    check_arg(f, q_d_plusp, list1(Str("Maxima sum"))) |> ignore
    let answer = mapcar(u => d_extract_nc_part(u).0, cdr(f))
    cons(list2(q_mlist, q_simp), answer)
  }
}

///|
fn d_constant_term(expr : Value, variables : Value) -> Value raise {
  if atom(expr) {
    if memq(expr, variables).truthy() {
      Fix(0L)
    } else {
      expr
    }
  } else if d_plusp(expr) is Nil {
    if appears_in(expr, q_mplus).truthy() {
      raise LispError::SimpleError("should expand expr before taking const")
    } else {
      for v in cdr(variables).iter() {
        if appears_in(expr, v).truthy() {
          return Fix(0L)
        }
      }
      expr
    }
  } else {
    let the_constants = Collector::new()
    for v in cdr(expr).iter() {
      let mut appears = false
      for w in cdr(variables).iter() {
        if appears_in(v, w).truthy() {
          appears = true
          break
        }
      }
      if !appears {
        the_constants.add(v)
      }
    }
    addn(the_constants.result(), t)
  }
}

///|
/// `(adjust-array a (max (length a) 1) :fill-pointer fp)`
fn polya__adjust_to_fill(a : Value, size : Int, fp : Int) -> Value raise {
  let a = adjust_array(a, [if size > 1 { size } else { 1 }])
  set_fill_pointer(a, fp)
  a
}

///|
fn pv_get_rows_from_macsyma_equations_and_variables(
  self_ : Value,
  equations : Value,
  the_variables : Value,
) -> Value raise {
  let mut equations = equations
  let mut eqn_no = -1
  polya__set_pv(self_, "rows", make_array([length(equations)], fill=0))
  |> ignore
  if polya__pv(self_, "table").truthy() {
    clrhash(polya__pv(self_, "table")) |> ignore
  } else {
    polya__set_pv(self_, "table", make_hash_table(kind=Equal)) |> ignore
  }
  polya__set_pv(self_, "type-of-entries", q_kw_rational) |> ignore
  let table = polya__pv(self_, "table")
  let mut constants_column : Value = Nil
  let rat_vars = mapcar(v => add_newvar(v).0, cdr(the_variables))
  if d_listp(equations).truthy() {
    equations = cdr(equations)
  }
  for eqn0 in equations.iter() {
    let mut eqn = eqn0
    if rational_functionp(eqn).truthy() || affine_polynomialp(eqn).truthy() {
      ()
    } else {
      if d_ratp(eqn).truthy() {
        eqn = d_ratdisrep(eqn)
      }
      eqn = bring_to_left_side(eqn)
    }
    if d_zerop(eqn).truthy() {
      format(t, "~%Eliminating Trivial Equation.", []) |> ignore
    } else if d_numberp(eqn).truthy() {
      raise LispError::SimpleError(
        format_to_string("~%Inconsistent equation ~A", [eqn]),
      )
    } else {
      eqn_no += 1
      let a_row = make_array([2 * to_int(equation_length(eqn))], fill=0)
      vector_push_extend(a_row, polya__pv(self_, "rows")) |> ignore
      let rat_eqn = function_numerator(st_rat(eqn))
      let mut n = 0
      let mut v = rat_vars
      let mut vv = cdr(the_variables)
      while v is Cons(_) && vv is Cons(_) {
        if car(v).truthy() {
          n += 1
        }
        let cof = pcoeff(rat_eqn, list3(car(v), Fix(1L), Fix(1L)))
        if d_zerop(cof) is Nil {
          if !numberp(cof) {
            polya__set_pv(self_, "type-of-entries", q_kw_any_macsyma) |> ignore
          }
          vector_push_extend(int(n), a_row) |> ignore
          vector_push_extend(cof, a_row) |> ignore
          sethash(car(vv), table, int(n)) |> ignore
        }
        v = cdr(v)
        vv = cdr(vv)
      }
      let const_ = pcoeff(
        rat_eqn,
        Fix(1L),
        variables_to_exclude_from_cof=rat_vars,
      )
      if d_zerop(const_) is Nil {
        if !numberp(const_) {
          polya__set_pv(self_, "type-of-entries", q_kw_any_macsyma) |> ignore
        }
        if constants_column is Nil {
          let len = length(equations)
          constants_column = make_array([len], initial=Fix(0L), fill=len)
        }
        aset1(constants_column, eqn_no, const_) |> ignore
        polya__set_pv(self_, "constants-column-number", Fix(0L)) |> ignore
      }
    }
  }
  let rows = polya__pv(self_, "rows")
  let fp = fill_pointer(rows)
  polya__set_pv(self_, "rows", polya__adjust_to_fill(rows, length(rows), fp))
  |> ignore
  if constants_column.truthy() {
    polya__set_pv(self_, "constants-column-number", Fix(0L)) |> ignore
    constants_column = polya__adjust_to_fill(
      constants_column,
      length(polya__pv(self_, "rows")),
      fill_pointer(polya__pv(self_, "rows")),
    )
  }
  pv_set_up_sparse_matrix_from_rows(self_) |> ignore
  if constants_column.truthy() {
    struct_set(
      polya__pv(self_, "the-sparse-matrix"),
      POLYA_SP_CONSTANTS_COLUMN,
      constants_column,
    )
  } else {
    Nil
  }
}

///|
/// Reports the variables of the list (mlist) VARIABLES that did not appear
/// in the equations of $poly_vector.
fn polya__report_missing_variables(variables : Value) -> Unit raise {
  if variables.truthy() {
    let table = polya__pv(symval(q_d_poly_vector), "table")
    let mut add_to_dim = 0
    for u in cdr(variables).iter() {
      if gethash(u, table) is Nil {
        add_to_dim += 1
        format(t, "~%The variable ~A did not appear.", [u]) |> ignore
      }
    }
    if add_to_dim != 0 {
      format(
        t,
        "~%Thus we should add ~D to the dimension of the solution space.",
        [int(add_to_dim)],
      )
      |> ignore
    }
  }
}

///|
fn fast_linsolve(poly_eqns : Value, variables : Value) -> Value raise {
  if get(car(variables), q_disrep) is Nil {
    fsignal(list1(Str("variables should be genvars"))) |> ignore
  }
  let variables = cons(list1(q_mlist), mapcar(v => get(v, q_disrep), variables))
  let pv = symval(q_d_poly_vector)
  pv_get_rows_from_macsyma_equations_and_variables(pv, poly_eqns, variables)
  |> ignore
  format(t, "~%Assuming entries of type ~A", [
    polya__pv(pv, "type-of-entries"),
  ])
  |> ignore
  polya__report_missing_variables(variables)
  pv_solve_suitable_to_sublis(pv)
}

///|
/// Solves list of EQUATIONS in a list of VARIABLES.
fn d_fast_linsolve(eqn : Value, variables? : Value = Nil) -> Value raise {
  if !struct_typep(symval(q_d_poly_vector), "polynomial-vectors") {
    set(q_d_poly_vector, amacros__make_polynomial_vectors()) |> ignore
  }
  let pv = symval(q_d_poly_vector)
  polya__set_pv(
    pv,
    "type-of-entries",
    symval(q_d_type_of_entries_for_poly_vector),
  )
  |> ignore
  if variables.truthy() {
    pv_get_rows_from_macsyma_equations_and_variables(pv, eqn, variables)
    |> ignore
  } else {
    pv_get_rows_from_macsyma_equations(pv, eqn) |> ignore
  }
  if symval(q_modulus).truthy() {
    polya__set_pv(pv, "type-of-entries", symval(q_modulus)) |> ignore
  }
  format(t, "~%Assuming entries of type ~A", [
    polya__pv(pv, "type-of-entries"),
  ])
  |> ignore
  polya__report_missing_variables(variables)
  pv_solve_suitable_to_sublis(pv)
}

///|
fn d_nexp(u : Value, n : Value) -> Value raise {
  let n = to_int(n)
  if atom(u) {
    let c = Collector::new()
    for i in 0..<n {
      ignore(i)
      c.add(u)
    }
    ncmuln(c.result(), t)
  } else {
    let c = Collector::new()
    for i in 0..<n {
      ignore(i)
      c.append_list(copy_list(cdr(u)))
    }
    ncmuln(c.result(), t)
  }
}

///|
fn d_collect(expr : Value) -> Value raise {
  with_special(q_d_expop, Fix(0L), () => d_ratsimp(expr, Nil))
}

///|
fn d_subtract_monomial(expr : Value, mon : Value) -> Value raise {
  sub(expr, mul(list2(d_nc_coeff(expr, mon), mon)))
}

///|
fn replace_dot_simplifications(expr : Value) -> Value raise {
  let mut dot_simps = symval(q_d_dot_simplifications)
  let mut answer = expr
  if dot_simps.truthy() && symval(q_ear_start_dot_replace).truthy() {
    dot_simps = cdr(dot_simps)
    while dot_simps.truthy() {
      answer = test_pattern(answer, car(dot_simps), second(dot_simps))
      dot_simps = cddr(dot_simps)
    }
    answer
  } else {
    answer
  }
}

///|
/// Replaces the pattern in ADP (a dot product) by replacement.
fn test_pattern(adp : Value, pattern : Value, replacement : Value) -> Value raise {
  if atom(adp) {
    adp
  } else if equal(caar(adp), q_mnctimes) {
    let tem = ordered_sublist(cdr(pattern), cdr(adp))
    if tem.truthy() {
      ncmul(list3(ncmuln(car(tem), t), replacement, ncmuln(cadr(tem), t)))
    } else {
      adp
    }
  } else {
    adp
  }
}

///|
fn d_nsdot(l : Value) -> Value raise {
  with_special(q_d_dot_simplifications, Nil, () => ncmuln(l, t))
}

///|
fn d_sort_mono(variables : Value, degree : Value) -> Value raise {
  d_sort(d_mono(variables, degree), f=symval(q_d_order_function))
}

///|
/// If x and y are lists ordering priority is based on the ends not the
/// beginning of the lists.
fn tail_alphalessp(x : Value, y : Value) -> Value raise {
  if atom(x) && atom(y) {
    alphalessp(x, y)
  } else if atom(x) {
    alphalessp(x, car(last(y)))
  } else if atom(y) {
    alphalessp(car(last(x)), y)
  } else {
    let lengx = length(x)
    let lengy = length(y)
    let mut i = lengx - 1
    let mut j = lengy - 1
    while i >= 0 && j >= 0 {
      let xi = nth(i, x)
      let yj = nth(j, y)
      if alphalessp(xi, yj).truthy() {
        return t
      } else if alphalessp(yj, xi).truthy() {
        return Nil
      }
      i -= 1
      j -= 1
    }
    lbool(lengx < lengy)
  }
}

///|
fn unreplaced_monomials_in_dot_simplifications(macsyma_list? : Value) -> Value raise {
  let macsyma_list = match macsyma_list {
    Some(v) => v
    None => symval(q_d_dot_simplifications)
  }
  check_arg(macsyma_list, q_d_listp, list1(Str("macsyma list"))) |> ignore
  let mut answer : Value = Nil
  let n = length(macsyma_list)
  let mut i = 2
  while i < n {
    let mut tem = d_list_nc_parts(nth(i, macsyma_list))
    if d_listp(tem).truthy() {
      tem = cdr(tem)
    } else {
      tem = list1(tem)
    }
    answer = zl_union(list2(answer, tem))
    i += 2
  }
  answer
}

///|
/// Returns nil unless small appears in big in which case a list of
/// alternating terms before and terms after each occurrence is returned.
fn ordered_sublist(small : Value, big : Value) -> Value raise {
  let mut answer : Value = Nil
  let mut some_of_big = big
  while some_of_big.truthy() {
    if initial_sublist(small, some_of_big).truthy() {
      answer = append(
        list2(
          subseq(big, 0, end=length(big) - length(some_of_big)),
          nthcdr(length(small), some_of_big),
        ),
        answer,
      )
    }
    some_of_big = cdr(some_of_big)
  }
  answer
}

///|
fn d_set_dot_simplifications(l : Value) -> Value raise {
  set(q_d_dot_simplifications, Nil) |> ignore
  let mut l = meval(l)
  set(q_d_dot_simplifications, copy_list(l)) |> ignore
  amacros__show("L", l)
  set(q_d_dot_simplifications, subseq(l, 0, end=3)) |> ignore
  l = cdddr(l)
  while l.truthy() {
    set(
      q_d_dot_simplifications,
      append(symval(q_d_dot_simplifications), list1(meval(car(l)))),
    )
    |> ignore
    set(
      q_d_dot_simplifications,
      append(symval(q_d_dot_simplifications), list1(meval(cadr(l)))),
    )
    |> ignore
    l = cddr(l)
  }
  Nil
}

///|
fn d_generate_array_of_relations(
  variables : Value,
  degree : Value,
  relations : Value,
) -> Value raise {
  with_specials(
    [(q_d_expop, Fix(100L)), (q_d_dot_simplifications, Nil)],
    () => {
      let answer = make_array([64], fill=0)
      for gen in cdr(relations).iter() {
        let additional_degree = num_sub(degree, d_nc_degree(gen))
        let mut j : Value = Fix(0L)
        while num_le(j, additional_degree) {
          for left_multiple in cdr(d_mono(variables, j)).iter() {
            let left_times_gen = ncmul(list2(left_multiple, gen))
            for right_multiple in cdr(
                d_mono(variables, sub(additional_degree, j)),
              ).iter() {
              vector_push_extend(
                ncmul(list2(left_times_gen, right_multiple)),
                answer,
              )
              |> ignore
            }
          }
          j = num_add(j, Fix(1L))
        }
      }
      answer
    },
  )
}

///|
fn d_find_rank(nc_polynomials : Value) -> Value raise {
  let pv = symval(q_d_poly_vector1)
  pv_get_rows_from_array_of_polynomials(
    pv,
    nc_polynomials,
    parts_of_monomial=q_sc_and_nc_parts,
  )
  |> ignore
  pv_set_up_sparse_matrix_from_rows(pv) |> ignore
  pv_reduce(pv) |> ignore
  sp_number_of_pivots(polya__pv(pv, "the-sparse-matrix"))
}

///|
fn d_find_simplifications(nc_polynomial_relations : Value) -> Value raise {
  let pv = symval(q_d_poly_vector)
  pv_get_rows_from_array_of_polynomials(
    pv,
    nc_polynomial_relations,
    parts_of_monomial=q_sc_and_nc_parts,
  )
  |> ignore
  pv_set_up_sparse_matrix_from_rows(pv) |> ignore
  pv_solve_suitable_to_sublis(pv)
}

///|
fn join_arrays(l : Value) -> Value raise {
  let answer = make_array([100], fill=0)
  for u in l.iter() {
    for i in 0..<length(u) {
      vector_push_extend(aref1(u, i), answer) |> ignore
    }
  }
  polya__adjust_to_fill(answer, length(answer), fill_pointer(answer))
}

///|
fn d_com(x : Value, y : Value, zet? : Value = Fix(1L)) -> Value raise {
  let term1 = ncmul_star(list2(x, y))
  let mut term2 = ncmul_star(list2(y, x))
  term2 = mul_star(list2(zet, term2))
  d_ratsimp(d_dotsimp(sub_star(term1, term2)), Nil)
}

///|
fn set_up_graded_relations(
  the_variables : Value,
  deg : Value,
  new_relations : Value,
) -> Value raise {
  if !arrayp(symval(q_d_graded_relations)) {
    set(q_d_graded_relations, make_array([25])) |> ignore
  }
  let gr = symval(q_d_graded_relations)
  let d = to_int(deg)
  if aref1(gr, d) is Nil {
    aset1(gr, d, amacros__make_polynomial_vectors()) |> ignore
  }
  let poly_vectors = aref1(gr, d)
  if !equal(polya__pv(poly_vectors, "relations"), new_relations) ||
    !equal(polya__pv(poly_vectors, "variables"), the_variables) {
    let mut finished = false
    try {
      format(t, "~%Calculating relations in degree ~A of", [deg]) |> ignore
      displa(new_relations) |> ignore
      polya__set_pv(poly_vectors, "relations", new_relations) |> ignore
      polya__set_pv(poly_vectors, "variables", the_variables) |> ignore
      let nc_polynomials = d_generate_array_of_relations(
        the_variables,
        deg,
        new_relations,
      )
      pv_get_rows_from_array_of_polynomials(
        poly_vectors,
        nc_polynomials,
        parts_of_monomial=q_sc_and_nc_parts,
      )
      |> ignore
      pv_set_up_sparse_matrix_from_rows(poly_vectors) |> ignore
      finished = true
    } catch {
      e => {
        if !finished {
          polya__set_pv(poly_vectors, "relations", Nil) |> ignore
        }
        raise e
      }
    }
    pv_reduce(poly_vectors)
  } else {
    Nil
  }
}

///|
/// The rows of A-ROW's nonzero entries as $rat expressions.
fn polya__rat_entries(a_row : Value) -> Value raise {
  let c = Collector::new()
  let n = length(a_row)
  let mut i = 0
  while i < n {
    if aref1(a_row, i).truthy() {
      c.add(d_rat(aref1(a_row, i + 1), Nil))
    }
    i += 2
  }
  c.result()
}

///|
/// Makes $aaaa at least as long as TERMS.
fn polya__ensure_aaaa(terms : Value) -> Unit raise {
  if length(symval(q_d_aaaa)) < length(terms) {
    let vars = Collector::new()
    for i in 0..<length(terms) {
      vars.add(d_concat(list2(q_d_aa, int(i))))
    }
    set(q_d_aaaa, cons(list2(q_mlist, q_simp), vars.result())) |> ignore
    d_declare_scalar_list(symval(q_d_aaaa)) |> ignore
  }
}

///|
/// Assumes relations homogeneous of same degree.
fn d_find_central_elements(
  variables : Value,
  degree : Value,
  relations? : Value,
) -> Value raise {
  let relations = match relations {
    Some(v) => v
    None => symval(q_d_relations)
  }
  check_arg(relations, q_d_listp, list1(Str("macsyma list"))) |> ignore
  set_up_graded_relations(variables, num_add(degree, Fix(1L)), relations)
  |> ignore
  set_up_graded_relations(variables, degree, relations) |> ignore
  let gr = symval(q_d_graded_relations)
  let basis = cons(
    list2(q_mlist, q_simp),
    pv_get_basis(aref1(gr, to_int(degree))),
  )
  let poly_vectors = aref1(gr, to_int(degree) + 1)
  let terms = basis
  polya__ensure_aaaa(terms)
  let gen_sum = d_general_sum(basis, coefficients=symval(q_d_aaaa)).0
  let eqns = Collector::new()
  for u in cdr(variables).iter() {
    let com = d_com(gen_sum, u)
    let a_row = convert_polynomial_to_vector(
      com,
      polya__pv(poly_vectors, "table"),
      parts_of_monomial=q_sc_and_nc_parts,
    ).0
    sp_set_type_of_entries(
      polya__pv(poly_vectors, "the-sparse-matrix"),
      q_kw_any_macsyma,
    )
    |> ignore
    sp_reduce_row_with_respect_to_rows(
      polya__pv(poly_vectors, "the-sparse-matrix"),
      a_row,
    )
    |> ignore
    eqns.append_list(polya__rat_entries(a_row))
  }
  let all_eqns = cons(list2(q_mlist, q_simp), eqns.result())
  let answer = d_fast_linsolve(
    all_eqns,
    variables=subseq(symval(q_d_aaaa), 0, end=length(terms)),
  )
  d_sublis(answer, gen_sum)
}

///|
/// Grabs the non-pivots.
fn pv_get_basis(self_ : Value) -> Value raise {
  set(q_ear_ans, Nil) |> ignore
  let col_used_to_pivot = struct_ref(
    polya__pv(self_, "the-sparse-matrix"),
    POLYA_SP_COLUMNS_USED_TO_PIVOT,
  )
  with_special(q_d_dot_simplifications, Nil, () => {
    let table = polya__pv(self_, "table")
    let monoms = cdr(
      d_mono(
        polya__pv(self_, "variables"),
        d_nc_degree(get_key(table, Fix(1L))),
      ),
    )
    let c = Collector::new()
    for v in monoms.iter() {
      if gethash(gethash(v, table), col_used_to_pivot) is Nil {
        c.add(v)
      }
    }
    c.result()
  })
}

///|
fn d_express_in_terms_of_basis(
  variables : Value,
  form : Value,
  relations? : Value,
) -> Value raise {
  let relations = match relations {
    Some(v) => v
    None => symval(q_d_relations)
  }
  let deg = d_nc_degree(form)
  set_up_graded_relations(variables, deg, relations) |> ignore
  let poly_vectors = aref1(symval(q_d_graded_relations), to_int(deg))
  let a_row = convert_polynomial_to_vector(
    form,
    polya__pv(poly_vectors, "table"),
    parts_of_monomial=q_sc_and_nc_parts,
  ).0
  sp_set_type_of_entries(
    polya__pv(poly_vectors, "the-sparse-matrix"),
    q_kw_any_macsyma,
  )
  |> ignore
  sp_reduce_row_with_respect_to_rows(
    polya__pv(poly_vectors, "the-sparse-matrix"),
    a_row,
  )
  |> ignore
  let tem = Collector::new()
  let n = length(a_row)
  let mut ii = 0
  while ii < n {
    if aref1(a_row, ii).truthy() {
      tem.add(
        mul_star(
          list2(
            aref1(a_row, ii + 1),
            get_key(polya__pv(poly_vectors, "table"), aref1(a_row, ii)),
          ),
        ),
      )
    }
    ii += 2
  }
  add_star(tem.result())
}

///|
fn d_test(d_generators : Value) -> Value raise {
  d_find_rank(
    d_generate_array_of_relations(
      macsyma_list(list3(q_d_w, q_d_x, q_d_y)),
      Fix(4L),
      d_generators,
    ),
  )
}

///|
fn d_find_rank_of_relations(var_ : Value, deg : Value, relat? : Value) -> Value raise {
  let relat = match relat {
    Some(v) => v
    None => symval(q_d_relations)
  }
  d_find_rank(d_generate_array_of_relations(var_, deg, relat))
}

///|
/// `(loop for v in l minimize/maximize (f v))` (0 when L is empty).
fn polya__min_max(l : Value, f : (Value) -> Value raise, max : Bool) -> Value raise {
  let mut m : Value = Nil
  for v in l.iter() {
    let x = f(v)
    if m is Nil || (if max { num_gt(x, m) } else { num_lt(x, m) }) {
      m = x
    }
  }
  if m is Nil {
    Fix(0L)
  } else {
    m
  }
}

///|
fn d_nc_degree(f : Value, type_of_weight? : Value = q_kw_weight) -> Value raise {
  if f is Nil {
    Fix(0L)
  } else if atom(f) {
    if numberp(f) || d_scalarp(f).truthy() {
      Fix(0L)
    } else {
      let tem = get(f, type_of_weight)
      if tem.truthy() {
        tem
      } else {
        Fix(1L)
      }
    }
  } else if affine_polynomialp(f).truthy() {
    num_add(d_nc_degree(get(car(f), q_disrep)), d_nc_degree(fifth(f)))
  } else if d_ratp(f).truthy() {
    d_nc_degree(num(cdr(f)))
  } else if d_plusp(f).truthy() {
    polya__min_max(
      cdr(f),
      v => d_nc_degree(v, type_of_weight~),
      symval(q_d_leading_monomial_is_lowest_degree) is Nil,
    )
  } else if eq(caar(f), q_d_power) {
    vmul_star(list2(d_nc_degree(second(f), type_of_weight~), third(f)))
  } else if d_scalarp(f).truthy() {
    Fix(0L)
  } else if eq(caar(f), q_mtimes) {
    polya__min_max(cdr(f), u => d_nc_degree(u, type_of_weight~), true)
  } else if eq(caar(f), q_rat) {
    Fix(0L)
  } else if eq(caar(f), q_mrat) {
    let c = Collector::new()
    let mut v = varlist(f)
    let mut w = genvar(f)
    while v is Cons(_) && w is Cons(_) {
      if fast_scalarp(car(v)) is Nil && appears_in(cdr(f), car(w)).truthy() {
        c.add(car(v))
      }
      v = cdr(v)
      w = cdr(w)
    }
    polya__min_max(
      c.result(),
      v => d_nc_degree(v, type_of_weight~),
      symval(q_d_leading_monomial_is_lowest_degree) is Nil,
    )
  } else if eq(caar(f), q_mnctimes) {
    let mut s : Value = Fix(0L)
    for u in cdr(f).iter() {
      s = num_add(s, d_nc_degree(u, type_of_weight~))
    }
    s
  } else {
    raise LispError::SimpleError(
      format_to_string("The degree of ~A is undefined.", [f]),
    )
  }
}

///|
fn free_ncmul(l : Value) -> Value raise {
  with_special(q_d_dot_simplifications, Nil, () => ncmuln(copy_list(l), t))
}

///|
fn d_mono(variables : Value, n : Value, reset? : Value = Nil) -> Value raise {
  if reset.truthy() {
    clear_memory_function(q_d_mono_aux) |> ignore
  }
  let repls = Collector::new()
  let mut v = cdr(symval(q_d_dot_simplifications))
  while v is Cons(_) {
    let deg = d_nc_degree(car(v))
    if num_le(deg, n) {
      repls.add(car(v))
    }
    if eql(deg, Fix(0L)) {
      return list1(q_mlist)
    }
    v = cddr(v)
  }
  polya__mono_aux(variables, n, repls.result())
}

///|
/// `(defremember $food (a b) (+ a b))`
fn polya__food(a : Value, b : Value) -> Value raise {
  let key : () -> Value raise = () => list2(a, b)
  let body : () -> Value raise = () => num_add(a, b)
  if get(q_d_food, q_kw_dont_remember).truthy() {
    return body()
  }
  if get(q_d_food, q_kw_memory_table).truthy() {
    polya__remember(q_d_food, key, body)
  } else {
    putprop(q_d_food, make_hash_table(kind=Equal), q_kw_memory_table) |> ignore
    polya__food(a, b)
  }
}

///|
/// `(defremember $mono-aux (variables n repls &aux tem) ...)`
fn polya__mono_aux(variables : Value, n : Value, repls : Value) -> Value raise {
  let key : () -> Value raise = () => list3(variables, n, repls)
  let body : () -> Value raise = () => {
    if num_lt(n, Fix(0L)) {
      Nil
    } else if eql(n, Fix(0L)) {
      list2(list1(q_mlist), Fix(1L))
    } else {
      let op = list2(q_mnctimes, q_simp)
      let c = Collector::new()
      for v in cdr(variables).iter() {
        let deg = d_nc_degree(v)
        let mut answ : Value = Nil
        for mon in cdr(polya__mono_aux(variables, num_sub(n, deg), repls)).iter() {
          if numberp(mon) {
            if d_must_replacep(v) is Nil {
              answ = cons(v, answ)
            }
          } else if symbolp(mon) {
            let tem = list3(op, v, mon)
            if d_must_replacep(tem) is Nil {
              answ = cons(tem, answ)
            }
          } else if listp(mon) {
            let tem = cons(op, cons(v, cdr(mon)))
            if d_must_replacep(tem) is Nil {
              answ = cons(tem, answ)
            }
          }
        }
        c.append_list(nreverse(answ))
      }
      cons(list1(q_mlist), c.result())
    }
  }
  if get(q_d_mono_aux, q_kw_dont_remember).truthy() {
    return body()
  }
  if get(q_d_mono_aux, q_kw_memory_table).truthy() {
    polya__remember(q_d_mono_aux, key, body)
  } else {
    putprop(q_d_mono_aux, make_hash_table(kind=Equal), q_kw_memory_table)
    |> ignore
    polya__mono_aux(variables, n, repls)
  }
}

///|
fn d_separate_parameters(expression : Value, parameters : Value) -> Value raise {
  let parameters = if parameters is Nil {
    list2(Str("aa"), Str("par"))
  } else {
    parameters
  }
  let list_parameters = d_list_variables(expression, parameters)
  let tems = Collector::new()
  for par in cdr(list_parameters).iter() {
    let answer = copy_list(expression)
    let subs = Collector::new()
    for other_par in cdr(list_parameters).iter() {
      if !eq(other_par, par) {
        subs.add(list3(list1(q_mequal), other_par, Fix(0L)))
      } else {
        subs.add(cons(list1(q_mequal), list2(other_par, Fix(1L))))
      }
    }
    tems.add(
      d_ratsimp(
        d_sublis(cons(list2(q_mlist, q_simp), subs.result()), answer),
        Nil,
      ),
    )
  }
  if cdr(list_parameters) is Nil {
    format(t, "~%Special soln:", []) |> ignore
    list2(list1(q_mlist), expression)
  } else {
    cons(list2(q_mlist, q_simp), tems.result())
  }
}

///|
fn pv_clean_up(self_ : Value) -> Value raise {
  polya__set_pv(self_, "relations", Nil) |> ignore
  polya__set_pv(self_, "variables", Nil) |> ignore
  struct_set(polya__pv(self_, "the-sparse-matrix"), POLYA_SP_ROWS, Nil)
  |> ignore
  polya__set_pv(self_, "rows", Nil) |> ignore
  clrhash(polya__pv(self_, "table"))
}

///|
/// Assumes relations homogeneous of same degree.
fn d_find_relation(
  variables : Value,
  degree : Value,
  monoms : Value,
  relations? : Value,
) -> Value raise {
  let relations = match relations {
    Some(v) => v
    None => symval(q_d_relations)
  }
  check_arg(relations, q_d_listp, list1(Str("macsyma list"))) |> ignore
  check_arg(monoms, q_d_listp, list1(Str("macsyma list"))) |> ignore
  set_up_graded_relations(variables, degree, relations) |> ignore
  let poly_vectors = aref1(symval(q_d_graded_relations), to_int(degree))
  let terms = monoms
  polya__ensure_aaaa(terms)
  let gen_sum = d_general_sum(monoms, coefficients=symval(q_d_aaaa)).0
  let a_row = convert_polynomial_to_vector(
    gen_sum,
    polya__pv(poly_vectors, "table"),
    parts_of_monomial=q_sc_and_nc_parts,
  ).0
  sp_set_type_of_entries(
    polya__pv(poly_vectors, "the-sparse-matrix"),
    q_kw_any_macsyma,
  )
  |> ignore
  sp_reduce_row_with_respect_to_rows(
    polya__pv(poly_vectors, "the-sparse-matrix"),
    a_row,
  )
  |> ignore
  let eqns = polya__rat_entries(a_row)
  let all_eqns = cons(list2(q_mlist, q_simp), eqns)
  let answer = d_fast_linsolve(
    all_eqns,
    variables=subseq(symval(q_d_aaaa), 0, end=length(monoms)),
  )
  d_sublis(answer, gen_sum)
}

///|
fn d_determinant_of_equations(eqn : Value, variables? : Value = Nil) -> Value raise {
  if !struct_typep(symval(q_d_poly_vector), "polynomial-vectors") {
    set(q_d_poly_vector, amacros__make_polynomial_vectors()) |> ignore
  }
  let pv = symval(q_d_poly_vector)
  polya__set_pv(
    pv,
    "type-of-entries",
    symval(q_d_type_of_entries_for_poly_vector),
  )
  |> ignore
  if variables.truthy() {
    pv_get_rows_from_macsyma_equations_and_variables(pv, eqn, variables)
    |> ignore
  } else {
    pv_get_rows_from_macsyma_equations(pv, eqn) |> ignore
  }
  if symval(q_ear_show_entry_type).truthy() {
    format(t, "~%Assuming entries of type ~A", [
      polya__pv(pv, "type-of-entries"),
    ])
    |> ignore
  }
  let answer = sp_determinant(polya__pv(pv, "the-sparse-matrix"))
  new_disrep(answer)
}

///|
fn d_special_find_central_elements(
  vari : Value,
  deg : Value,
  infinites : Value,
) -> Value raise {
  let mut mons = d_mono(vari, deg)
  mons = append(mons, mapcar(v => ncmul_star(list2(infinites, v)), cdr(mons)))
  displa(mons) |> ignore
  let gen_sum = d_general_sum(mons, coefficients=symval(q_d_aaaa)).0
  let mut general = gen_sum
  for v in cdr(vari).iter() {
    let comu = d_com(general, v)
    let ncmonos = d_list_nc_monomials(comu)
    let eqns = d_extract_linear_equations(
      list2(list1(q_mlist), comu),
      independent_monomials=ncmonos,
    )
    let solus = d_fast_linsolve(
      eqns,
      variables=d_list_variables(eqns, list1(Str("aa"))),
    )
    general = meval_star(d_sublis(solus, general))
    displa(general) |> ignore
    let vari_left = d_list_variables(general, list2(Str("aa"), Str("par")))
    let subs = Collector::new()
    let mut vv = cdr(vari_left)
    let mut aa = cdr(symval(q_d_aaaa))
    while vv is Cons(_) && aa is Cons(_) {
      subs.add(cons(car(vv), car(aa)))
      vv = cdr(vv)
      aa = cdr(aa)
    }
    general = sublis(subs.result(), general)
    displa(general) |> ignore
  }
  d_separate_parameters(general, Nil)
}

///|
fn d_solve_nc_coefficients(d_list_eqns : Value, variable_strings : Value) -> Value raise {
  d_fast_linsolve(
    d_extract_linear_equations(
      d_list_eqns,
      independent_monomials=d_list_nc_monomials(d_list_eqns),
    ),
    variables=d_list_variables(d_list_eqns, variable_strings),
  )
}

///|
/// Coerces to poly if possible. FORM should be a affine-polynomialp or
/// rational-functionp.
fn gencoeff(form : Value, mon : Value, vars_to_exclude? : Value) -> Value raise {
  let vars_to_exclude = match vars_to_exclude {
    Some(v) => v
    None => list_variables(mon)
  }
  if affine_polynomialp(form).truthy() {
    pcoeff(form, mon, variables_to_exclude_from_cof=vars_to_exclude)
  } else if rational_functionp(form).truthy() {
    let answ = pcoeff(
      num(form),
      mon,
      variables_to_exclude_from_cof=vars_to_exclude,
    )
    if pzerop(answ).truthy() {
      Fix(0L)
    } else {
      let answ = ratreduce(answ, denom(form))
      if eql(Fix(1L), denom(answ)) {
        num(answ)
      } else {
        answ
      }
    }
  } else {
    fsignal(
      list1(Str("unknown type.  Wants a polynomial or rational-function.")),
    )
  }
}

///|
/// Takes input like matrix([x.y+a*y.z,z.z+v,..],[...,...,..],...) and
/// returns a poly-data. pd-convert-to-maxima-format is the inverse.
fn poly_data_from_nc_matrix(nc_matrix : Value) -> Value raise {
  iassert(d_matrixp(nc_matrix)) |> ignore
  let mat_polys = mapcar(v => mapcar(vv => st_rat(vv), cdr(v)), cdr(nc_matrix))
  let monom_vector = Collector::new()
  for i in 0..<length(first(mat_polys)) {
    let mut tem : Value = Nil
    for v in mat_polys.iter() {
      tem = zl_union(list2(list_variables(nth(i, v)), tem))
      if member(Fix(1L), tem) is Nil &&
        pzerop(gencoeff(nth(i, v), Fix(1L), vars_to_exclude=tem)) is Nil {
        tem = cons(Fix(1L), tem)
      }
    }
    let c = Collector::new()
    for va in tem.iter() {
      if eql(va, Fix(1L)) {
        c.add(va)
      } else if num_gt(d_nc_degree(get(va, q_disrep)), Fix(0L)) {
        c.add(list3(va, Fix(1L), Fix(1L)))
      }
    }
    monom_vector.add(c.result())
  }
  let monom_vector = monom_vector.result()
  let monoms_in_each_column = mapcar(v => int(length(v)), monom_vector)
  let the_segment = Collector::new()
  let mut all : Value = Fix(0L)
  for v in monoms_in_each_column.iter() {
    the_segment.add(all)
    all = num_add(all, v)
  }
  let nrows = length(mat_polys)
  let rows = make_array([nrows], fill=nrows)
  let mut ii = 0
  for ro in mat_polys.iter() {
    let a_row = make_array([10], fill=0)
    aset1(rows, ii, a_row) |> ignore
    let mut tot_monoms = 0
    let mut pol = ro
    let mut monoms = monom_vector
    let mut ns = monoms_in_each_column
    while pol is Cons(_) && monoms is Cons(_) && ns is Cons(_) {
      let mut i = 0
      for mon in car(monoms).iter() {
        let cof = if eql(Fix(1L), mon) {
          gencoeff(car(pol), mon, vars_to_exclude=list_variables(car(monoms)))
        } else {
          gencoeff(car(pol), mon)
        }
        if pzerop(cof) is Nil {
          vector_push_extend(int(i + tot_monoms), a_row) |> ignore
          vector_push_extend(cof, a_row) |> ignore
        }
        i += 1
      }
      tot_monoms += to_int(car(ns))
      pol = cdr(pol)
      monoms = cdr(monoms)
      ns = cdr(ns)
    }
    ii += 1
  }
  let big = Collector::new()
  for v in monom_vector.iter() {
    big.append_list(v)
  }
  let pd = amacros__make_poly_data()
  amacros__slot_set(pd, "pd-", "segments", the_segment.result()) |> ignore
  amacros__slot_set(pd, "pd-", "rows", rows) |> ignore
  amacros__slot_set(pd, "pd-", "big-monom-list", big.result()) |> ignore
  pd
}

///|
fn segment_interval(segments : Value, spot : Value) -> Value raise {
  let mut ii = 0
  for v in segments.iter() {
    if num_gt(v, spot) {
      return int(ii - 1)
    }
    ii += 1
  }
  int(if ii > 0 { ii - 1 } else { 0 })
}

///|
fn pd_convert_to_maxima_format(pd : Value) -> Value raise {
  let rows = amacros__slot_ref(pd, "pd-", "rows")
  let segments = amacros__slot_ref(pd, "pd-", "segments")
  let big = amacros__slot_ref(pd, "pd-", "big-monom-list")
  let c = Collector::new()
  for i in 0..<fill_pointer(rows) {
    let mut lis = list(Array::make(length(segments), Fix(0L)))
    let a_row = aref1(rows, i)
    let n = fill_pointer(a_row)
    let mut k = 0
    while k < n {
      let tem = aref1(a_row, k)
      if tem.truthy() {
        let where_ = to_int(segment_interval(segments, tem))
        setf_car(
          nthcdr(where_, lis),
          n_plus(
            nth(where_, lis),
            n_star(list2(aref1(a_row, k + 1), nth(to_int(tem), big))),
          ),
        )
        |> ignore
      }
      k += 2
    }
    lis = mapcar(x => new_disrep(x), lis)
    let mut nonzero = false
    for v in lis.iter() {
      if pzerop(v) is Nil {
        nonzero = true
        break
      }
    }
    if nonzero {
      c.add(cons(list1(q_mlist), mapcar(x => new_disrep(x), lis)))
    }
  }
  cons(list1(q_d_matrix), c.result())
}

///|
fn id(mat : Value) -> Value raise {
  let pd = poly_data_from_nc_matrix(mat)
  // (describe pd)
  format(t, "~%~S", [pd]) |> ignore
  pd_convert_to_maxima_format(pd)
}

///|
fn reduce_poly_data(pd : Value) -> Value raise {
  let sp = sp_make_sparse_matrix(amacros__slot_ref(pd, "pd-", "rows"))
  sp_reduce(sp) |> ignore
  sp
}

///|
/// Does row reduction, assuming that the set of non commutative monomials
/// are linearly independent, so that matrix([x.y,0],[x,0],[1,0]) is
/// already reduced. Like most of the nc stuff it assumes that scalars
/// precede non scalars in the alphabet.
fn d_nc_matrix_row_reduce(mat : Value) -> Value raise {
  let pd = poly_data_from_nc_matrix(mat)
  reduce_poly_data(pd) |> ignore
  pd_convert_to_maxima_format(pd)
}

///|
/// Returns a matrix whose rows are a basis for the quotient row space of
/// mat1 modulo modulo-mat.
fn d_nc_matrix_quotient(mat1 : Value, modulo_mat : Value) -> Value raise {
  iassert(d_matrixp(modulo_mat)) |> ignore
  iassert(d_matrixp(mat1)) |> ignore
  let big_mat = append(modulo_mat, cdr(mat1))
  let big_pd = poly_data_from_nc_matrix(big_mat)
  let all_rows = listarray(amacros__slot_ref(big_pd, "pd-", "rows"))
  let n = to_int(d_length(modulo_mat))
  let (sp1, sp2) = sp_quotient_space_basis(
    subseq(all_rows, 0, end=n),
    nthcdr(n, all_rows),
  )
  ignore(sp2)
  amacros__slot_set(big_pd, "pd-", "rows", struct_ref(sp1, POLYA_SP_ROWS))
  |> ignore
  pd_convert_to_maxima_format(big_pd)
}

///|
/// `(return-array (prog1 ar (setq ar nil)))`: RETURN-ARRAY (a Lisp Machine
/// function) does not exist.
fn get_rid_of_array(ar : Value) -> Value raise {
  ignore(ar)
  raise LispError::SimpleError("The function RETURN-ARRAY is undefined.")
}

///|
fn init_share_polya() -> Unit raise {
  set(q_d_dotdistrib, t) |> ignore
  defvar_init(q_ear_one_dimensional_array, make_array([100], fill=0))
  defvar_init(q_ear_nonsense, list1(q_nonsense))
  defvar_init(q_ear_monomial_table, make_hash_table(kind=Equal))
  defvar_init(q_d_poly_vector, amacros__make_polynomial_vectors())
  defvar_init(q_d_poly_vector1, amacros__make_polynomial_vectors())
  // redefinitions and definitions not in the contract
  defun(
    q_d_firstn,
    args => polya__firstn(arg(args, 0), arg(args, 1)),
    name="$firstn",
  )
  defun(
    q_d_tail_alphalessp,
    args => tail_alphalessp(arg(args, 0), arg(args, 1)),
    name="$tail_alphalessp",
  )
  defun(
    q_commutative_monomials,
    args => polya__commutative_monomials(
      arg(args, 0),
      arg(args, 1),
      if args.length() > 2 {
        args[2]
      } else {
        q_kw_weight
      },
      arg(args, 3),
    ),
    name="commutative-monomials",
  )
  defun(
    q_d_mono_aux,
    args => polya__mono_aux(arg(args, 0), arg(args, 1), arg(args, 2)),
    name="$mono-aux",
  )
  defun(
    q_d_food,
    args => polya__food(arg(args, 0), arg(args, 1)),
    name="$food",
  )
  // $declare_order_weights and $declare_weights are Lisp macros: their
  // arguments are not evaluated.
  register_mspec(q_d_declare_order_weights, form => d_declare_order_weights(
    cdr(form),
  ))
  register_mspec(q_d_declare_weights, form => d_declare_weights(cdr(form)))
  // DEFREMEMBER clears the memory and :dont-remember when it is loaded.
  for f in [q_commutative_monomials, q_d_mono_aux, q_d_food] {
    if get(f, q_kw_memory_table).truthy() {
      clrhash(get(f, q_kw_memory_table)) |> ignore
    }
    remprop(f, q_kw_dont_remember) |> ignore
  }
}
