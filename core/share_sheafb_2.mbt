// Port of share/affine/sheafb.lisp (part 2): from LDATA-CODIM to the end of
// the file -- translating components between opens, matching components,
// variable orderings, the divide and linear dichotomies.
//
// Notes:
// - PUSH-NEW and INTERSECTION-EQUAL are called by sheafb.lisp but defined
//   nowhere in Maxima (polysmp.lisp has PUSH-NEW commented out), so the
//   reference signals an undefined-function error when they are reached;
//   the port calls them through `funcall` on their symbols with the same
//   effect.
// - CL BREAK (which enters the Lisp debugger) raises an error instead.

// ---------------------------------------------------------------------------
// Private helpers

///|
let sheafb2__q_push_new : Value = sym("push-new")

///|
let sheafb2__q_intersection_equal : Value = sym("intersection-equal")

///|
/// `(break x)`: the debugger is not available; signal an error.
fn sheafb2__break(x : Value) -> Unit raise {
  raise LispError::SimpleError(format_to_string("break: ~A", [x]))
}

///|
/// The expansion of `(iassert expr)` when `expr` is false.
fn sheafb2__iassert(ok : Bool) -> Unit raise {
  if !ok {
    fsignal(list1(Str("The expression ~A was not true"))) |> ignore
  }
}

///|
/// The predicate of the list-type named structure `matrix`.
fn sheafb2__matrix_p(x : Value) -> Bool {
  consp(x) && eq(car(x), q_matrix)
}

///|
/// `(push-new item place)`: an undefined function in the reference.
fn sheafb2__push_new(item : Value, place : Value) -> Value raise {
  funcall(sheafb2__q_push_new, [item, place])
}

// ---------------------------------------------------------------------------

///|
fn ldata_codim(ldata : Value) -> Value raise {
  int(length(sheafa__ldata_eqns(ldata)))
}

///|
/// To hell with the expense: use translate the correct intersection
/// inequality.
fn translate_reduced_component_and_reduce(
  from_open : Value,
  to_open : Value,
  ldata : Value,
  homogeneous_ldata_on_to_open? : Value = Nil,
) -> (Value, Value) raise {
  let mut answer : Value = Nil
  let (answ, hh) = translate_component_and_reduce(
    from_open,
    to_open,
    ldata,
    use_inverse_inequal=t,
  )
  if answ is Nil {
    ()
  } else {
    answer = if linear_solvedp(sheafa__ldata_eqns(answ)).truthy() ||
      linear_ldatap(answ, open_g=sheafa__zopen_inequality(to_open)).truthy() {
      answ
    } else {
      let contract = contract_ideal_localization(sheafa__ldata_eqns(answ), hh)
      sheafa__mshow("CONTRACT", contract)
      let mut simp_contract = simplify_ldata(
        sheafa__make_ldata(eqns=contract),
        open_g=sheafa__zopen_inequality(to_open),
      )
      if simp_contract is Nil {
        Nil
      } else if length(simp_contract) > 2 {
        let some_ld = Collector::new()
        for v in simp_contract.iter() {
          if unit_idealp(sheafa__ldata_eqns(v), may_invert=hh) is Nil &&
            equal(ldata_codim(v), ldata_codim(ldata)) {
            some_ld.add(v)
          }
        }
        let n = length(some_ld.result())
        if n > 1 {
          fsignal(list1(Str("Too many components"))) |> ignore
        }
        // The loop collects INTO a variable: its value is NIL.
        Nil
      } else {
        simp_contract = car(simp_contract)
        simp_contract
      }
    }
    if length(sheafa__ldata_eqns(answer)) !=
      length(sheafa__ldata_eqns(ldata)) {
      if symval(q_ear_query_user) is Nil {
        throw_tag(q_new_choice, Nil) |> ignore
      } else if homogeneous_ldata_on_to_open.truthy() {
        intersect_ldata(homogeneous_ldata_on_to_open, answ, open_g=hh)
        |> ignore
        fsignal(
          list1(
            Str(
              "Wrong dimension or not complete intersection ~\n\t\t\t      look at the value of int-transl ",
            ),
          ),
        )
        |> ignore
      } else {
        answer = answ
      }
    }
  }
  if symval(q_ear_query_user).truthy() && answer.truthy() {
    let ineq = sheafa__zopen_inequality(to_open)
    let mut bad = false
    for v in sheafa__ldata_eqns(answer).iter() {
      if !(any_linearp(v, ineq).truthy() ||
        gm_prepared(v, inequal=ineq).truthy()) {
        bad = true
        break
      }
    }
    if bad {
      fsignal(list1(Str("not linear or well prepared on to open"))) |> ignore
    }
  }
  (answer, hh)
}

///|
fn ldata_subset(ld : Value, ldd : Value) -> Value raise {
  grobner_subset(
    sheafa__ldata_eqns(ld),
    sheafa__ldata_eqns(ldd),
    may_invert=sheafa__ldata_inequality(ldd),
  ).0
}

///|
/// Gets the list of ldata corresponding to OPEN.
fn pls_ldata(
  pls : Value,
  open_ : Value,
  ldata_number? : Value = Nil,
) -> Value raise {
  let mut open = open_
  if numberp(open) {
    open = nth(to_int(open), pls_opens(pls))
  }
  check_arg(open, lbool(eq(car(open), q_zopen)), list1(Str("an open")))
  |> ignore
  let mut answer : Value = Nil
  let mut ops = pls_opens(pls)
  let mut data = sheafa__pls_data(pls)
  while ops is Cons(_) && data is Cons(_) {
    if equal(open, car(ops)) {
      answer = car(data)
      break
    }
    ops = cdr(ops)
    data = cdr(data)
  }
  if ldata_number.truthy() {
    nth(to_int(ldata_number), answer)
  } else {
    answer
  }
}

///|
fn union_equal(lists : Value) -> Value raise {
  let mut result : Value = Nil
  for l in lists.iter() {
    for w in l.iter() {
      if member_equal(w, result) is Nil {
        result = cons(w, result)
      }
    }
  }
  nreverse(result)
}

///|
fn intersection_equal1(l : Value) -> Value raise {
  if length(l) == 1 {
    car(l)
  } else {
    let tem = Collector::new()
    for v in car(l).iter() {
      if member_equal(v, second(l)).truthy() {
        tem.add(v)
      }
    }
    apply(sheafb2__q_intersection_equal, cons(tem.result(), cddr(l)))
  }
}

///|
fn intersectp(a : Value, b : Value, test_? : Value = Nil) -> Value raise {
  for v in a.iter() {
    for w in b.iter() {
      if funcall(test_, [v, w]).truthy() {
        return t
      }
    }
  }
  Nil
}

///|
fn build_equiv(lis : Value, test_? : Value) -> Value raise {
  let tst = match test_ {
    Some(f) => f
    None => q_equal
  }
  for v in lis.iter() {
    for w in lis.iter() {
      if !eql(v, w) && intersectp(v, w, test_=tst).truthy() {
        let lis2 = cons(
          union_equal(list2(v, w)),
          remove_equal(w, remove_equal(v, lis)),
        )
        return build_equiv(lis2, test_=tst)
      }
    }
  }
  mapcar(x => union_equal(list1(x)), lis)
}

///|
fn check_equivalence_relation(lis_equiv_classes : Value) -> Value raise {
  for v in lis_equiv_classes.iter() {
    for w in lis_equiv_classes.iter() {
      if intersectp(v, w, test_=q_equal).truthy() {
        if !eql(v, w) {
          return Nil
        }
      }
    }
  }
  t
}

///|
fn add_zopen_history(zopen : Value, n : Value) -> Value raise {
  if length(zopen) >= 5 {
    let ans = copy_list(zopen)
    sheafa__set_zopen_history(ans, cons(n, sheafa__zopen_history(zopen)))
    |> ignore
    ans
  } else {
    let zopen = nconc(zopen, copy_list(list1(Nil)))
    add_zopen_history(zopen, n)
  }
}

///|
fn final_check_contained_in(
  lis_ld : Value,
  orig_image : Value,
  hh : Value,
  current_open : Value,
  current_ld_number : Value,
  nth_open : Value,
) -> Value raise {
  let b = bind(q_ear_refine_opens, Nil)
  defer unbind(b)
  let images = ldata_simplifications(orig_image, open_g=hh)
  for image in images.iter() {
    let mut i = 0
    for v in lis_ld.iter() {
      let (cont, unit) = grobner_subset(
        sheafa__ldata_eqns(v),
        sheafa__ldata_eqns(image),
        may_invert=hh,
      )
      if unit.truthy() {
        break
      }
      if cont.truthy() {
        if length(sheafa__ldata_eqns(v)) == length(sheafa__ldata_eqns(image)) {
          return cons(current_open, int(i))
        } else {
          format(t, "image properly contains zl-SOME part", []) |> ignore
        }
      }
      i = i + 1
    }
  }
  set(
    q_ear_bad_components,
    cons(
      list3(nth_open, current_open, current_ld_number),
      symval(q_ear_bad_components),
    ),
  )
  |> ignore
  format(t, "~%Bad component ~A", [car(symval(q_ear_bad_components))])
  |> ignore
  sheafb2__break(t)
  Nil
}

///|
fn match_components(
  pls : Value,
  nth_open : Value,
  check_equal? : Value = Nil,
  break_on_bad? : Value = Nil,
  ignore_empty_opens? : Value = Nil,
  ldata_number? : Value = Nil,
) -> Value raise {
  let opens = pls_opens(pls)
  let open = nth(to_int(nth_open), opens)
  let mut lis_dat = pls_ldata(pls, open)
  if ldata_number.truthy() {
    lis_dat = list1(nth(to_int(ldata_number), lis_dat))
  }
  let mut hh : Value = Nil
  let answ = Collector::new()
  let mut ii = 0
  for ld in lis_dat.iter() {
    // str will be ( (open number . ld number) ...)
    let mut str = if ldata_number.truthy() {
      list1(cons(nth_open, ldata_number))
    } else {
      list1(cons(nth_open, int(ii)))
    }
    let mut i = 0
    let mut ops = opens
    let mut datas = sheafa__pls_data(pls)
    while ops is Cons(_) && datas is Cons(_) {
      let op = car(ops)
      let lis_ld = car(datas)
      if !eql(int(i), nth_open) &&
        (lis_ld.truthy() || ignore_empty_opens is Nil) {
        let mut found_one : Value = Nil
        let mapl = find_ring_map(open, op)
        let image = apply_rmap(mapl, ld)
        let mut gg = function_numerator(
          apply_rmap(mapl, sheafa__zopen_inequality(open)),
        )
        gg = nplcm(sheafa__rmap_denom(mapl), gg)
        let mut j = 0
        let mut last_j = 0
        for ldd in lis_ld.iter() {
          last_j = j
          let a1 = sheafa__ldata_eqns(ldd)
          let a2 = sheafa__ldata_eqns(image)
          hh = nplcm(sheafa__zopen_inequality(op), gg)
          let (cont, unit) = grobner_subset(a1, a2, may_invert=hh)
          if cont.truthy() && check_equal.truthy() && unit is Nil {
            let rev_cont = grobner_subset(
              sheafa__ldata_eqns(ldd),
              sheafa__ldata_eqns(image),
              may_invert=hh,
            ).0
            if rev_cont is Nil {
              if break_on_bad.truthy() {
                sheafb2__break(q_not_equal)
              }
            }
          }
          if unit.truthy() {
            format(t, "~%The intersection with the ~D open is empty.", [
              int(i),
            ])
            |> ignore
          }
          if unit.truthy() {
            str = cons(cons(int(i), Nil), str)
            found_one = t
          }
          if unit is Nil && cont.truthy() {
            str = cons(cons(int(i), int(j)), str)
            found_one = t
          }
          j = j + 1
        }
        if lis_ld.truthy() && found_one is Nil {
          let tem = final_check_contained_in(
            lis_ld,
            image,
            hh,
            int(i),
            int(last_j),
            nth_open,
          )
          if tem.truthy() {
            str = cons(tem, str)
          }
        }
      }
      i = i + 1
      ops = cdr(ops)
      datas = cdr(datas)
    }
    answ.add(str)
    ii = ii + 1
  }
  answ.result()
}

///|
fn list_opens1(components : Value) -> Value raise {
  let answ : Value = Nil
  for com in components.iter() {
    for v in com.iter() {
      sheafb2__push_new(car(v), answ) |> ignore
    }
  }
  answ
}

///|
fn short_list_open_numbers(
  components_to_cover : Value,
  opens_used? : Value = Nil,
) -> Value raise {
  if components_to_cover is Nil {
    opens_used
  } else {
    let ops = list_opens1(components_to_cover)
    let mut prev_min = 10000000
    let mut where_ : Value = Nil
    for op in ops.iter() {
      let tem = Collector::new()
      for com in components_to_cover.iter() {
        if assoc(op, com) is Nil {
          tem.add(com)
        }
      }
      let an_answ = short_list_open_numbers(
        tem.result(),
        opens_used=cons(op, opens_used),
      )
      if length(an_answ) < prev_min {
        prev_min = length(an_answ)
        where_ = an_answ
      }
    }
    where_
  }
}

///|
/// We assume that the pls has been reduced.
fn fast_match_components(pls : Value) -> (Value, Value) raise {
  let mut components : Value = Nil
  let mut all_codims : Value = Nil
  let mut transl : Value = Nil
  let mut hh : Value = Nil
  let mut ops_l = pls_opens(pls)
  let mut datas = sheafa__pls_data(pls)
  let mut op_num = 0
  while ops_l is Cons(_) && datas is Cons(_) {
    let op = car(ops_l)
    let lis_dat = car(datas)
    let mut components_to_cover : Value = Nil
    for ld in lis_dat.iter() {
      if !(linear_solvedp(sheafa__ldata_eqns(ld)).truthy() ||
        linear_ldatap(ld).truthy()) {
        components_to_cover = components
        break
      } else {
        let mut dl = all_codims
        let mut cl = components
        while dl is Cons(_) && cl is Cons(_) {
          if equal(car(dl), int(length(sheafa__ldata_eqns(ld)))) {
            sheafb2__push_new(car(cl), components_to_cover) |> ignore
          }
          dl = cdr(dl)
          cl = cdr(cl)
        }
      }
    }
    let mut ops = short_list_open_numbers(components_to_cover)
    ops = ml_sort(ops)
    sheafa__show("OP-NUM", int(op_num))
    sheafa__show("OPS", ops)
    let mut accounted_for : Value = Nil
    let mut to_op_num : Value = Nil
    for top in ops.iter() {
      to_op_num = top
      let to_open = nth(to_int(top), pls_opens(pls))
      let to_lis_dat = nth(to_int(top), sheafa__pls_data(pls))
      let mut lld_num = 0
      for lld in lis_dat.iter() {
        if memq(lld, accounted_for) is Nil {
          let (a, b) = translate_reduced_component_and_reduce(
            op, to_open, lld,
          )
          transl = a
          hh = b
        }
        if transl.truthy() {
          let mut ld_num = 0
          for ld in to_lis_dat.iter() {
            if unit_idealp(sheafa__ldata_eqns(ld), may_invert=hh) is Nil &&
              variety_ldata_subset(
                ld,
                transl,
                open_g=hh,
                ignore_ldata_inequalities=t,
              ).0.truthy() {
              if variety_ldata_subset(
                  transl,
                  ld,
                  open_g=hh,
                  ignore_ldata_inequalities=t,
                ).0.truthy() {
                nconc(
                  get_component(components, cons(top, int(ld_num))),
                  list1(cons(int(op_num), int(lld_num))),
                )
                |> ignore
                accounted_for = cons(lld, accounted_for)
              } else {
                fsignal(list1(Str("containment one way"))) |> ignore
              }
            }
            ld_num = ld_num + 1
          }
        }
        lld_num = lld_num + 1
      }
    }
    // finally
    let comps = Collector::new()
    let dims = Collector::new()
    let mut lld_num = 0
    for lld in lis_dat.iter() {
      if memq(lld, accounted_for) is Nil {
        sheafa__show("TO-OP-NUM", to_op_num)
        sheafa__show("LLD-NUM", int(lld_num))
        comps.add(list1(cons(int(op_num), int(lld_num))))
        dims.add(int(length(sheafa__ldata_eqns(lld))))
      }
      lld_num = lld_num + 1
    }
    components = nconc(components, comps.result())
    all_codims = append(all_codims, dims.result())
    op_num = op_num + 1
    ops_l = cdr(ops_l)
    datas = cdr(datas)
  }
  (components, all_codims)
}

///|
fn get_component(components : Value, cons_op_ld : Value) -> Value raise {
  for com in components.iter() {
    if member_equal(cons_op_ld, com).truthy() {
      return com
    }
  }
  Nil
}

///|
fn list_opens_with_component(
  pls : Value,
  open_num : Value,
  compon_num : Value,
) -> Value raise {
  let answ = nth(to_int(compon_num), match_components(pls, open_num))
  des(nth(to_int(compon_num), nth(to_int(open_num), sheafa__pls_data(pls))))
  |> ignore
  format(t, "~%is in opens: ", []) |> ignore
  let col = Collector::new()
  let mut i = 0
  for _op in pls_opens(pls).iter() {
    if eql(cdr(assoc_equal(int(i), answ)), compon_num) {
      col.add(int(i))
    }
    i = i + 1
  }
  col.result()
}

///|
fn match_all_components(
  pls : Value,
  ignore_empty_opens? : Value = t,
) -> Value raise {
  let b = bind(q_ear_bad_components, Nil)
  defer unbind(b)
  let opens = pls_opens(pls)
  let all = Collector::new()
  for i in 0..<length(opens) {
    for x in match_components(pls, int(i), ignore_empty_opens~).iter() {
      all.add(x)
    }
  }
  let mut equiv = build_equiv(
    all.result(),
    test_=lfunc("match-all-components-test", a => {
      let u = a[0]
      let v = a[1]
      if equal(u, v) {
        cdr(v)
      } else {
        Nil
      }
    }),
  )
  equiv = mapcar(
    v => sort_list(v, (u, w) => num_lt(car(u), car(w))),
    equiv,
  )
  list3(q_components, equiv, symval(q_ear_bad_components))
}

///|
fn verify_simplification(pl1 : Value, pl2simp : Value) -> Value raise {
  let mut opens = sheafa__sv_zopens(sheafa__pls_s_var(pl1))
  let mut datas = sheafa__pls_data(pl1)
  let mut i = 0
  while opens is Cons(_) && datas is Cons(_) {
    let open = car(opens)
    let lis_dat = car(datas)
    format(t, "~%**For the original ~:R open", [int(i)]) |> ignore
    let mut ops2 = sheafa__sv_zopens(sheafa__pls_s_var(pl2simp))
    let mut datas2 = sheafa__pls_data(pl2simp)
    let mut j = 0
    while ops2 is Cons(_) && datas2 is Cons(_) {
      let op2 = car(ops2)
      let lis_dat2 = car(datas2)
      // should really look at inequal	       when (equal  open  op2)
      if equal(sheafa__zopen_coord(open), sheafa__zopen_coord(op2)) {
        format(t, " whose coordinates are equal to those on open ~D", [
          int(j),
        ])
        |> ignore
        if lis_dat2.truthy() {
          check_component_containment(lis_dat, lis_dat2) |> ignore
        } else {
          format(t, "the data was empty", []) |> ignore
        }
      }
      j = j + 1
      ops2 = cdr(ops2)
      datas2 = cdr(datas2)
    }
    i = i + 1
    opens = cdr(opens)
    datas = cdr(datas)
  }
  Nil
}

///|
/// `(minimize for v in a-list quantity)`: returns the expansion.
fn minimize(
  for_ : Value,
  v : Value,
  in_ : Value,
  a_list : Value,
  quantity : Value,
) -> Value raise {
  // (iassert (and (eq for 'for) in 'in))
  sheafb2__iassert(eq(for_, q_for) && in_.truthy())
  list([
    q_loop,
    q_for,
    v,
    q_in,
    a_list,
    q_with,
    q_n_dotprev_min_dot,
    sym("="),
    int(10000000),
    q_with,
    q_n_dotwhere_dot,
    q_do,
    list3(q_setq, q_n_dottem_dot, quantity),
    q_when,
    list3(q_op_lt, q_n_dottem_dot, q_n_dotprev_min_dot),
    q_do,
    list3(q_setq, q_n_dotwhere_dot, v),
    list3(q_setq, q_n_dotprev_min_dot, q_n_dottem_dot),
    q_finally,
    list2(q_return, q_n_dotwhere_dot),
  ])
}

///|
/// `(for v in-or-on a-list [when test] operation quantity)`: operation may
/// be minimize, maximize, general-summing, or general-product; the quantity
/// will usually involve the variable v.  The result of the minimize is where
/// the minimum is.  Returns the expansion.
fn for_(v : Value, in_or_on : Value, a_list : Value, body : Value) -> Value raise {
  sheafb2__iassert(memq(in_or_on, list2(q_in, q_on)).truthy())
  let mut body = body
  let mut when_clause : Value = Nil
  if equal(car(body), q_when) {
    when_clause = subseq(body, 0, end=2)
    body = cddr(body)
  } else {
    sheafb2__iassert(length(body) == 2)
  }
  let operation = first(body)
  let quantity = second(body)
  if member_equal(operation, list2(q_minimize, q_maximize)).truthy() {
    let (pred, init) = if eq(operation, q_minimize) {
      (q_op_lt, int(10000000))
    } else {
      (q_op_gt, int(-100000000))
    }
    let head = list([
      q_loop,
      q_for,
      v,
      in_or_on,
      a_list,
      q_with,
      q_n_dotprev_min_dot,
      sym("="),
      init,
      q_with,
      q_n_dotwhere_dot,
    ])
    let tail = list([
      q_do,
      list3(q_setq, q_n_dottem_dot, quantity),
    ])
    let and_part = if when_clause.truthy() { list1(q_and) } else { Nil }
    let rest = list([
      q_when,
      list3(pred, q_n_dottem_dot, q_n_dotprev_min_dot),
      q_do,
      list3(q_setq, q_n_dotwhere_dot, v),
      list3(q_setq, q_n_dotprev_min_dot, q_n_dottem_dot),
      q_finally,
      list2(q_return, q_n_dotwhere_dot),
    ])
    append(
      head,
      append(copy_list(when_clause), append(tail, append(and_part, rest))),
    )
  } else if member_equal(operation, list2(q_general_summing, q_general_product)).truthy() {
    let (op, init) = if eq(operation, q_general_summing) {
      (q_n_plus, int(0))
    } else {
      (q_n_star, int(1))
    }
    let head = list([
      q_loop,
      q_for,
      v,
      in_or_on,
      a_list,
      q_with,
      q_n_dotanswer_dot,
      sym("="),
      init,
    ])
    let rest = list([
      q_do,
      list3(q_setq, q_n_dotanswer_dot, list3(op, quantity, q_n_dotanswer_dot)),
      q_finally,
      list2(q_return, q_n_dotanswer_dot),
    ])
    append(head, append(copy_list(when_clause), rest))
  } else {
    fsignal(
      list1(
        Str(
          "The operation was not one of minimize, maximize, general-summing, or general-product",
        ),
      ),
    )
  }
}

///|
/// This allowed me to do the troublesome ldata: it tries to order the
/// variables so that the variables belonging to simpler and less equations
/// come first.  Returns (list ordered-list variable-occurs-in).
fn good_order_variables(ldata : Value) -> Value raise {
  if ldatap(ldata).truthy() {
    if sheafa__ldata_variables(ldata).truthy() {
      list2(
        sheafa__ldata_variables(ldata),
        mapcar(x => list_variables(x), sheafa__ldata_eqns(ldata)),
      )
    } else {
      let order = good_order_variables(sheafa__ldata_eqns(ldata))
      sheafa__set_ldata_variables(ldata, car(order)) |> ignore
      order
    }
  } else {
    let eqns = ldata
    let varl = list_variables(eqns)
    let variable_occurs = mapcar(x => list_variables(x), eqns)
    let compl = mapcar(v => gen_pcomplexity(v), eqns)
    // MULT is declared special.
    set(
      q_mult,
      mapcar(
        v => {
          let mut the_mult = 0
          let mut w = variable_occurs
          let mut f = eqns
          while w is Cons(_) && f is Cons(_) {
            if memq(v, car(w)).truthy() {
              the_mult = the_mult + 1
            }
            w = cdr(w)
            f = cdr(f)
          }
          let mut min : Value = int(0)
          let mut first_val = true
          let mut cl = compl
          let mut ww = variable_occurs
          while cl is Cons(_) && ww is Cons(_) {
            if memq(v, car(ww)).truthy() {
              let com = car(cl)
              if first_val || num_lt(com, min) {
                min = com
                first_val = false
              }
            }
            cl = cdr(cl)
            ww = cdr(ww)
          }
          cons(v, num_mul(int(the_mult), min))
        },
        varl,
      ),
    )
    |> ignore
    set(q_mult, sort_list(symval(q_mult), (u, v) => num_lt(cdr(u), cdr(v))))
    |> ignore
    list2(mapcar(x => car(x), symval(q_mult)), variable_occurs)
  }
}

///|
fn charactaristic_setp(eqns : Value) -> (Value, Value, Value, Value) raise {
  let lis = good_order_variables(eqns)
  let ordered_vars = first(lis)
  let occurs = second(lis)
  let highest_vars = mapcar(
    v => {
      for u in ordered_vars.iter() {
        if memq(u, v).truthy() {
          return u
        }
      }
      Nil
    },
    occurs,
  )
  let mut answ = t
  let mut l = highest_vars
  while l is Cons(_) {
    if memq(car(l), cdr(l)).truthy() {
      answ = Nil
      break
    }
    l = cdr(l)
  }
  (answ, ordered_vars, occurs, highest_vars)
}

///|
fn order_equations(eqns : Value) -> (Value, Value) raise {
  let (ch_set, vars, _, highest_vars) = charactaristic_setp(eqns)
  let eqns = if ch_set.truthy() {
    let col = Collector::new()
    for v in vars.iter() {
      let tem = find_position_in_list(v, highest_vars)
      if tem.truthy() {
        col.add(nth(to_int(tem), eqns))
      }
    }
    col.result()
  } else {
    eqns
  }
  (eqns, ch_set)
}

///|
fn highest_variables(variables : Value, occurs : Value) -> Value raise {
  mapcar(
    oc => {
      for v in variables.iter() {
        if memq(v, oc).truthy() {
          return v
        }
      }
      Nil
    },
    occurs,
  )
}

///|
fn all_linear_variables(f : Value, g? : Value = Nil) -> Value raise {
  let varl = degree_one_variables(f)
  let col = Collector::new()
  for v in varl.iter() {
    if may_invertp(pcoeff(f, list3(v, int(1), int(1))), g).truthy() {
      col.add(v)
    }
  }
  col.result()
}

///|
fn poly_relations_from_simplifications(simps? : Value) -> Value raise {
  let simps = match simps {
    Some(s) => s
    None => symval(q_ear_poly_simplifications)
  }
  let col = Collector::new()
  let mut l = simps
  while l is Cons(_) {
    let seq = car(l)
    let repl = cadr(l)
    if numberp(seq) {
      return list1(int(1))
    }
    col.add(
      pdifference(
        ptimes(convert_deg_sequence_to_monomial(seq), cdr(repl)),
        car(repl),
      ),
    )
    l = cddr(l)
  }
  col.result()
}

///|
fn simplify_ldata(
  ldata : Value,
  open_g? : Value = Fix(1L),
  refine_opens? : Value = Nil,
  error_check_containments? : Value = Nil,
) -> Value raise {
  with_specials([(q_ear_refine_opens, refine_opens), (q_ear_stop_simplify, Nil)], fn() raise {
    let mut changed = false
    let mut result : Value = Nil
    let answ0 = ldata_simplifications(
      ldata,
      open_g~,
      error_check_containments~,
    )
    let col = Collector::new()
    for ld in answ0.iter() {
      if linear_ldatap(ld, open_g~).truthy() {
        col.add(ld)
      } else {
        let mut done = false
        for fn_ in sheafa__ldata_eqns(ld).iter() {
          if length(non_constant_factors(fn_)) > 2 {
            changed = true
            result = make_dichotomy(ld, open_g~)
            done = true
            break
          }
        }
        if !done {
          result = list1(ld)
        }
      }
      // APPENDING RESULT is unconditional: a linear ldata also gets the
      // previous RESULT appended.
      col.append_list(copy_list(result))
    }
    let mut answ = col.result()
    if changed {
      answ = delete_redundant_ldata(answ, gg=open_g)
    }
    answ
  })
}

///|
/// This is hoky. It should try much harder!!
fn try_factor_irreducible_ldata(
  ldata : Value,
  open_g? : Value = Fix(1L),
) -> Value raise {
  let ldata_r : Ref[Value] = { val: ldata }
  let eqns_r : Ref[Value] = { val: sheafa__ldata_eqns(ldata) }
  if !boundp(q_ear_already_tried) {
    set(q_ear_already_tried, Nil) |> ignore
  }
  let orig_ldata = ldata
  // should be wrt open-g
  let tem = list2(ldata, open_g)
  if member_equal(tem, symval(q_ear_already_tried)).truthy() {
    list1(ldata)
  } else if symval(q_ear_dont_try_factor_irreducible_ldata).truthy() {
    list1(ldata)
  } else {
    let answer = catch_tag(q_took_too_long, fn() raise {
      set(q_ear_already_tried, cons(tem, symval(q_ear_already_tried)))
      |> ignore
      let varl = linear_ldatap(ldata_r.val, open_g~)
      if varl.truthy() {
        eqns_r.val = reduce_linear_ldata(ldata_r.val, varl, open_g~)
        if grobner_subset(list1(int(1)), eqns_r.val, may_invert=open_g).0.truthy() {
          Nil
        } else {
          let c = copy_list(ldata_r.val)
          sheafa__set_ldata_eqns(c, eqns_r.val) |> ignore
          list1(c)
        }
      } else {
        let comp = gen_pcomplexity(sheafa__ldata_eqns(ldata_r.val))
        if num_lt(comp, int(200)) {
          let mut new_ldata : Value = Nil
          with_special(q_ear_poly_simplifications, Nil, fn() raise {
            grobner_remember(sheafa__ldata_eqns(ldata_r.val)) |> ignore
            if symval(q_ear_poly_simplifications).truthy() {
              new_ldata = sheafa__make_ldata(
                eqns=poly_relations_from_simplifications(),
                inequality=plcm(open_g, sheafa__ldata_inequality(ldata_r.val)),
              )
            }
          })
          if num_lt(
              gen_pcomplexity(sheafa__ldata_eqns(new_ldata)),
              num_mul(Flo(1.1), comp),
            ) {
            ldata_r.val = new_ldata
          }
          let eqns = eqns_r.val
          let lin_vars = mapcar(f => all_linear_variables(f, g=open_g), eqns)
          sheafa__show("LIN-VARS", lin_vars)
          let mut answ = sheafb2__try_factor_sue(
            lin_vars, eqns, ldata_r, open_g,
          )
          let mut min = 0
          let mut first_val = true
          for ld in answ.iter() {
            let n = length(sheafa__ldata_eqns(ld))
            if first_val || n < min {
              min = n
              first_val = false
            }
          }
          if min > length(sheafa__ldata_eqns(orig_ldata)) {
            answ = list1(orig_ldata)
          }
          answ
        } else {
          list1(ldata_r.val)
        }
      }
    })
    if eq(answer, q_took_too_long) {
      list1(ldata_r.val)
    } else {
      answer
    }
  }
}

///|
/// The `(block sue ...)` of TRY-FACTOR-IRREDUCIBLE-LDATA.
fn sheafb2__try_factor_sue(
  lin_vars : Value,
  eqns : Value,
  ldata_r : Ref[Value],
  open_g : Value,
) -> Value raise {
  let mut lv = lin_vars
  let mut fl = eqns
  while lv is Cons(_) && fl is Cons(_) {
    let v = car(lv)
    let f = car(fl)
    if v is Nil {
      let varl = list_variables(f)
      let mut wl = lin_vars
      let mut ffl = eqns
      while wl is Cons(_) && ffl is Cons(_) {
        let w = car(wl)
        let ff = car(ffl)
        let tem = intersection(w, varl)
        if tem.truthy() {
          for uu in tem.iter() {
            let eqn = gen_prem(f, ff, uu).0
            if length(non_constant_factors(eqn, invert=open_g)) > 2 {
              let c = copy_list(ldata_r.val)
              sheafa__set_ldata_eqns(c, subst(eqn, f, eqns)) |> ignore
              return make_dichotomy(c, open_g~)
            }
          }
        }
        wl = cdr(wl)
        ffl = cdr(ffl)
      }
    }
    lv = cdr(lv)
    fl = cdr(fl)
  }
  list1(ldata_r.val)
}

///|
fn matrix_to_sparse_matrix(
  mat : Value,
  re_use_sparse_matrix? : Value,
) -> Value raise {
  let re_use = match re_use_sparse_matrix {
    Some(x) => x
    None => symval(q_ear_sparse_matrix)
  }
  convert_to_sparse_matrix(
    sheafa__matrix_rows(mat),
    re_use_sparse_matrix=re_use,
  )
}

///|
fn matrix_rank(mat : Value) -> Value raise {
  let sp = matrix_to_sparse_matrix(mat)
  sp_reduce(sp) |> ignore
  sp_number_of_pivots(sp)
}

///|
fn show_matrix(mat : Value) -> Value raise {
  if arrayp(mat) {
    let dimensions = array_dimensions(mat)
    let number_dims = length(dimensions)
    if number_dims == 2 {
      for i in 0..<to_int(car(dimensions)) {
        format(t, "~%", []) |> ignore
        for j in 0..<to_int(second(dimensions)) {
          format(t, "~3D", [aref(mat, [i, j])]) |> ignore
        }
      }
    } else if number_dims == 3 {
      for i in 0..<to_int(car(dimensions)) {
        format(t, "~%~%Block ~D ", [int(i)]) |> ignore
        for j in 0..<to_int(second(dimensions)) {
          format(t, "~%", []) |> ignore
          for k in 0..<to_int(nth(2, dimensions)) {
            format(t, "~3D", [aref(mat, [i, j, k])]) |> ignore
          }
        }
      }
    }
    Nil
  } else if sheafb2__matrix_p(mat) {
    for v in sheafa__matrix_rows(mat).iter() {
      format(t, "~% ~A ", [v]) |> ignore
    }
    Nil
  } else {
    Nil
  }
}

///|
fn jacobian_matrix(list_eqns : Value, variables? : Value = Nil) -> Value raise {
  let variables = if variables is Nil {
    ml_sort(list_variables(list_eqns))
  } else {
    variables
  }
  let mat = mapcar(
    f => mapcar(v => pderivative(f, v), variables),
    list_eqns,
  )
  sheafa__make_matrix(rows=mat)
}

///|
/// From version 7.
fn find_repeats(highest_variables : Value, eqns : Value) -> (Value, Value) raise {
  let mut repeat_eqns : Value = Nil
  let mut first_repeat : Value = Nil
  let mut v = highest_variables
  let mut eqnss = eqns
  while v is Cons(_) && eqnss is Cons(_) {
    if memq(car(v), cdr(v)).truthy() {
      let col = Collector::new()
      let mut el = eqnss
      let mut vl = v
      while el is Cons(_) && vl is Cons(_) {
        let eqn = car(el)
        let va = car(vl)
        if eq(va, v) &&
          member_equal(eqn, symval(q_ear_used_divisors)) is Nil {
          col.add(v)
        }
        el = cdr(el)
        vl = cdr(vl)
      }
      repeat_eqns = col.result()
      if cddr(repeat_eqns).truthy() {
        first_repeat = car(v)
        break
      }
    }
    v = cdr(v)
    eqnss = cdr(eqnss)
  }
  if cddr(repeat_eqns) is Nil {
    repeat_eqns = Nil
  }
  (repeat_eqns, first_repeat)
}

///|
/// Endeavors to turn ldata into an triangular list of eqns so that each
/// equation has possibly one more variable occurring than the previous.  It
/// takes a good order for the variables and then takes the first variable
/// to be highest in two succeeding eqns, and does a division to try to
/// correct this.  If the leading variable is not invertible it does a
/// dichotomy.
fn divide_dichotomy(ldata : Value, open_g? : Value = Fix(1L)) -> Value raise {
  let eqns = sheafa__ldata_eqns(ldata)
  // ordering should take into account open-g
  let ldata = copy_list_structure(ldata)
  let vars0 = copy_tree(good_order_variables(eqns))
  let occurs = second(vars0)
  let vars = first(vars0)
  let highest_vars = mapcar(
    v => {
      for u in vars.iter() {
        if memq(u, v).truthy() {
          return u
        }
      }
      Nil
    },
    occurs,
  )
  sheafa__show("VARS", vars)
  sheafa__show("HIGHEST-VARS", highest_vars)
  let (eqns_rep0, repeat) = find_repeats(vars, eqns)
  defer {
    set(q_ear_used_divisors, Nil) |> ignore
  }
  let mut answer : Value = Nil
  if repeat.truthy() {
    let mut eqns_rep = eqns_rep0
    sheafa__show("(LENGTH EQNS-REP)", int(length(eqns_rep)))
    eqns_rep = sort_key(eqns_rep, q_op_lt, q_pdegree, list1(repeat))
    sheafa__show("(LENGTH EQNS-REP)", int(length(eqns_rep)))
    if eql(pdegree(first(eqns_rep), repeat), pdegree(second(eqns_rep), repeat)) {
      // choose the least complex leading coefficient to divide by
      eqns_rep = sort_key(
        subseq(eqns_rep, 0, end=2),
        q_op_lt,
        lfunc("divide-dichotomy-key", a => pcomplexity(
          leading_coefficient(a[0], a[1]),
        )),
        list1(repeat),
      )
    }
    let f = second(eqns_rep)
    sheafa__show("REPEAT", repeat)
    let (zl_rem, c_reqd) = gen_prem(f, first(eqns_rep), repeat)
    set(q_ear_used_divisors, cons(f, symval(q_ear_used_divisors))) |> ignore
    sheafa__mshow("F", f)
    sheafa__mshow("(FIRST EQNS-REP)", first(eqns_rep))
    let mut new_eqns = delete(f, copy_list(eqns))
    if d_zerop(zl_rem).truthy() {
      ()
    } else {
      // these have f replaced by rem
      new_eqns = append(new_eqns, list1(zl_rem))
    }
    let gg = nplcm(open_g, sheafa__ldata_inequality(ldata))
    let mut ld1 : Value = Nil
    let mut ld2 : Value = Nil
    if may_invertp(c_reqd, gg).truthy() {
      ld2 = sheafa__make_ldata(eqns=new_eqns, inequality=gg, variables=vars)
    } else {
      // make two ldata one where c-reqd is invertible  and f replaced by rem
      // and other where its zero and f is still there.
      ld2 = sheafa__make_ldata(
        eqns=new_eqns,
        inequality=nplcm(gg, c_reqd),
        variables=vars,
      )
      ld1 = sheafa__make_ldata(
        eqns=cons(c_reqd, eqns),
        inequality=gg,
        variables=vars,
      )
    }
    answer = if ld1.truthy() {
      format(t, "~%Breaking into dichotomy on:", []) |> ignore
      sh(c_reqd) |> ignore
      format(t, "%original ldata followed by consequents:", []) |> ignore
      des(ldata) |> ignore
      des(ld1) |> ignore
      des(ld2) |> ignore
      let a1 = ldata_simplifications(ld1, open_g~, recursive_p=t)
      append(a1, ldata_simplifications(ld2, open_g~, recursive_p=t))
    } else {
      format(t, "~%The c-reqd was invertible: ", []) |> ignore
      sh(c_reqd) |> ignore
      sheafb2__iassert(member_equal(f, sheafa__ldata_eqns(ld2)) is Nil)
      des(ld2) |> ignore
      ldata_simplifications(ld2, open_g~, recursive_p=t)
    }
  } else {
    answer = list1(ldata)
  }
  answer
}

///|
fn triangularp(ldata : Value) -> Value raise {
  let eqns = sheafa__ldata_eqns(ldata)
  let vars0 = good_order_variables(eqns)
  let occurs = second(vars0)
  let mut vars = first(vars0)
  for v in symval(q_ear_used_divisors).iter() {
    vars = remove_equal(v, vars)
  }
  let highest_vars = mapcar(
    v => {
      for u in vars.iter() {
        if memq(u, v).truthy() {
          return u
        }
      }
      Nil
    },
    occurs,
  )
  sheafa__show("VARS", vars)
  sheafa__show("HIGHEST-VARS", highest_vars)
  for v in vars.iter() {
    let mut w = highest_vars
    while w is Cons(_) {
      if eq(car(w), v) && memq(v, cdr(w)).truthy() {
        return v
      }
      w = cdr(w)
    }
  }
  Nil
}

///|
/// Evaluates the key function only once for each term; orders by
/// (pred (key u) (key v)) true ==> u earlier than v in sorted list.
fn sort_expensive_key(a_list : Value, pred : Value, key : Value) -> Value raise {
  // PRED is declared special.
  with_special(q_pred, pred, fn() raise {
    let mut clist = copy_list(a_list)
    let mut l = clist
    while l is Cons(_) {
      setf_car(l, cons(funcall(key, [car(l)]), car(l))) |> ignore
      l = cdr(l)
    }
    clist = sort_list(clist, (u, v) => funcall(symval(q_pred), [car(u), car(v)]).truthy())
    l = clist
    while l is Cons(_) {
      setf_car(l, cdr(car(l))) |> ignore
      l = cdr(l)
    }
    clist
  })
}

///|
fn linear_dichotomy(
  ldata : Value,
  open_g? : Value = Fix(1L),
  in_linear_dich? : Value = Nil,
) -> Value raise {
  sheafa__mshow("LDATA", ldata)
  if in_linear_dich.truthy() {
    return list1(ldata)
  }
  // The live LINEAR-SOLVEDP (the last definition in sheafc.lisp) returns a
  // single value, so MULTIPLE-VALUE-SETQ leaves FNS NIL.
  let varl = linear_solvedp(sheafa__ldata_eqns(ldata), order_functions=t)
  let fns : Value = Nil
  if varl.truthy() {
    if linear_ldatap(ldata, open_g~).truthy() {
      list1(ldata)
    } else {
      let mut answ = int(1)
      let mut vl = varl
      let mut fl = fns
      while vl is Cons(_) && fl is Cons(_) {
        answ = ptimes(answ, pcoeff(car(fl), list3(car(vl), int(1), int(1))))
        vl = cdr(vl)
        fl = cdr(fl)
      }
      if may_invertp(answ, open_g).truthy() {
        list1(ldata)
      } else {
        let mut ans1 = ldata_simplifications(
          sheafa__make_ldata(
            eqns=sheafa__ldata_eqns(ldata),
            inequality=sftimes(answ, sheafa__ldata_inequality(ldata)),
          ),
          open_g~,
          recursive_p=t,
        )
        let ans2 = ldata_simplifications(
          sheafa__make_ldata(
            eqns=cons(answ, sheafa__ldata_eqns(ldata)),
            inequality=sheafa__ldata_inequality(ldata),
          ),
          open_g~,
          recursive_p=t,
        )
        ans1 = mapcar(
          v => sheafa__make_ldata(
            eqns=contract_ideal_localization(
              sheafa__ldata_eqns(v),
              sheafa__ldata_inequality(v),
            ),
          ),
          ans1,
        )
        let mut answer = append(ans1, ans2)
        answer = delete_redundant_ldata(answer, gg=open_g)
        sheafa__mshow("ANSWER", answer)
        answer
      }
    }
  } else {
    format(t, "~%**Unchanged", []) |> ignore
    list1(ldata)
  }
}

///|
fn simplify_affine_ldata(ldata : Value, open_g? : Value = Fix(1L)) -> Value raise {
  let vari = ml_sort(list_variables(sheafa__ldata_eqns(ldata)))
  let op = with_special(q_ear_xxx, vari, fn() raise {
    make_normal_zopen(Nil, int(length(vari)), open_g)
  })
  let sheaf = construct_pre_ldata_sheaves(
    opens=list1(op),
    data=list1(list1(ldata)),
  )
  simplify_svar_ldata(sheaf)
}

///|
fn simplify_affine_ldata_write(
  ldata : Value,
  open_g? : Value = Fix(1L),
  pathname? : Value = Str("haskell:>wfs>answer.lisp"),
) -> Value raise {
  let answ = simplify_affine_ldata(ldata, open_g~)
  set(q_ear_answer, answ) |> ignore
  let text = with_output_to_string(st => with_specials(
    [(standard_output, st), (q_ear_print_radix, Nil)],
    fn() raise {
      // (for-editor (des answ))
      with_specials([(q_linel, int(75)), (q_d_display2d, Nil)], fn() raise {
        des(answ) |> ignore
      })
      format(st, "~%(setq (answ (rerat '~A)))", [answ]) |> ignore
    },
  ))
  write_file(lstring(pathname), text)
  Nil
}
