// Port of share/affine/sheafa.lisp (part 3): from MAKE-DICHOTOMY to the end
// of the file, and the file's initialization.

///|
/// If stop-simplify is true then it only works if have linear dichotomy.
/// It returns a list of ldata.  (The second definition in the file; the
/// first one is `#+old`.)
fn make_dichotomy(ldata : Value, open_g? : Value = Fix(1L)) -> Value raise {
  if symval(q_ear_stop_simplify).truthy() {
    merr("how did *stop-simplify* get  here", []) |> ignore
  }
  let mut dich = find_good_dichotomy(ldata)
  let all_facs = symval(q_ear_all_factors)
  dich = order_dichotomy(dich)
  sheafa__show("DICH", dich)
  let gg = nplcm(open_g, sheafa__ldata_inequality(ldata))
  let int_open_g = if symval(q_ear_refine_opens) is Nil { gg } else { open_g }
  let lin_dich = {
    let mut r = if dich.truthy() { t } else { Nil }
    for v in dich.iter() {
      if any_linearp(v, gg) is Nil {
        r = Nil
        break
      }
    }
    r
  }
  sheafa__show("LIN-DICH", lin_dich)
  // I think the gm-prepared business should all be done after.
  // this may not be true.  The simplifications from finding a gm-prepared
  // and performing the elimination of variables might be necessary.
  if lin_dich is Nil {
    check_for_gm_prepared(sheafa__ldata_eqns(ldata), int_open_g) |> ignore
    sheafa__show("*STOP-SIMPLIFY*", symval(q_ear_stop_simplify))
  }
  let mut answ : Value = Nil
  if symval(q_ear_refine_opens) is Nil &&
    symval(q_ear_stop_simplify).truthy() {
    let ss = symval(q_ear_stop_simplify)
    let (lds, ggs) = ldata_refinement(
      ldata,
      car(ss),
      second(ss),
      inequality=int_open_g,
    )
    set(q_ear_stop_simplify, Nil) |> ignore
    // this does not take into account the fact we should be contracting
    // the ideal back to the current open..
    let c = Collector::new()
    let mut l1 = lds
    let mut l2 = ggs
    while l1 is Cons(_) && l2 is Cons(_) {
      c.append_list(
        ldata_simplifications(
          car(l1),
          open_g=sftimes(int_open_g, car(l2)),
          recursive_p=t,
        ),
      )
      l1 = cdr(l1)
      l2 = cdr(l2)
    }
    answ = c.result()
  } else if lin_dich.truthy() || symval(q_ear_stop_simplify) is Nil {
    // priority 1 Linear-dichotomy
    //          2 gm-prepared equation
    //          3 any dichotomy
    // proceed with dich if dich is linear or if found no gm-prepared
    if dich.truthy() {
      let mut so_far : Value = Fix(1L)
      let mut list_of_ld : Value = Nil
      for v in dich.iter() {
        let ec = Collector::new()
        for facs in all_facs.iter() {
          if member_equal(v, facs) is Nil {
            let ters = Collector::new()
            for p in sheafa__pairs(facs) {
              let ter = p.0
              if may_invertp(ter, so_far) is Nil {
                ters.add(ter)
              }
            }
            ec.add(gen_ptimes(ters.result()))
          }
        }
        let eqns_modv = ec.result()
        if memq(Nil, eqns_modv).truthy() {
          merr("nil should not be here", []) |> ignore
        }
        if v is Nil {
          merr("nil should not be here", []) |> ignore
        }
        let ld = sheafa__make_ldata()
        sheafa__set_ldata_eqns(ld, cons(v, eqns_modv)) |> ignore
        sheafa__set_ldata_inequality(ld, nplcm(gg, so_far)) |> ignore
        so_far = nplcm(so_far, v)
        let part = if symval(q_ear_stop_simplify) is Nil {
          ldata_simplifications(ld, open_g~, recursive_p=t)
        } else {
          list1(ld)
        }
        list_of_ld = append(list_of_ld, part)
        sheafa__mshow("LIST-OF-LD", list_of_ld)
      }
      if list_of_ld is Nil {
        answ = list1(
          sheafa__make_ldata(eqns=list1(Fix(1L)), inequality=Fix(1L)),
        )
      } else {
        answ = list_of_ld
      }
    } else {
      answ = list1(ldata)
    }
  }
  if answ is Nil {
    answ = list1(ldata)
  }
  answ
}

///|
fn order_variables_by_occurence(list_eqns : Value) -> Value raise {
  let var_lists = mapcar(v => list_variables(v), list_eqns)
  let all_vars = zl_union(var_lists)
  let c = Collector::new()
  for v in all_vars.iter() {
    c.add(v)
    let mut n = 0
    for lis in var_lists.iter() {
      if memq(v, lis).truthy() {
        n += 1
      }
    }
    c.add(int(n))
  }
  c.result()
}

///|
/// There is an error in simp-lead: it produced some equations which did
/// not give ideal containment.
fn simp_lead(
  eqns : Value,
  open_g? : Value = Fix(1L),
  variables? : Value = Nil,
) -> Value raise {
  let eqns = copy_list(eqns)
  sheafa__show("(LENGTH EQNS)", int(length(eqns)))
  let answ = {
    let mut res : Value? = None
    let mut v = eqns
    while v is Cons(_) {
      let fac = non_constant_factors(car(v), invert=open_g)
      if numberp(car(v)) && zerop(car(v)) {
        ()
      } else if length(fac) > 2 {
        res = Some(q_try_dichotomy)
        break
      } else if fac is Nil {
        res = Some(list1(Fix(1L)))
        break
      } else {
        setf_car(v, car(fac)) |> ignore
      }
      v = cdr(v)
    }
    match res {
      Some(r) => r
      None => simp_lead1(eqns, open_g~, variables~)
    }
  }
  sheafa__show(
    "(OR (SYMBOLP ANSW) (LENGTH ANSW))",
    if symbolp(answ) {
      t
    } else {
      int(length(answ))
    },
  )
  answ
}

///|
fn test_simp_lead(eqns : Value) -> Value raise {
  shl(eqns) |> ignore
  let answ = simp_lead1(eqns)
  if atom(answ) {
    sheafa__show("ANSW", answ)
    Nil
  } else {
    if ideal_subsetp(answ, eqns) is Nil {
      sheafa__break(sym("t1"))
    } else if ideal_subsetp(eqns, answ) is Nil {
      sheafa__break(sym("t2"))
    }
    format(t, "both ok", []) |> ignore
    shl(answ) |> ignore
    answ
  }
}

///|
fn simp_lead1(
  eqns : Value,
  open_g? : Value = Fix(1L),
  variables? : Value = Nil,
) -> Value raise {
  let mut eqns = union_equal(list1(eqns))
  let mut variables = variables
  let varl = if variables.truthy() { variables } else { list_variables(eqns) }
  let mut changed = false
  let mut vari = varl
  // loop named sue: returns 'start-over after the first replacement.
  while vari is Cons(_) {
    let var_ = car(vari)
    variables = vari
    let tem = var_
    let deg_vector = mapcar(u => pdegree(u, var_), eqns)
    let degs = sort_list(zl_union(list1(delete(Fix(0L), copy_list(deg_vector)))), (
      a,
      b,
    ) => alphalessp(a, b).truthy())
    let mut start_over = false
    for i in degs.iter() {
      let mut jv = deg_vector
      let mut fv = eqns
      while jv is Cons(_) && fv is Cons(_) {
        let j = car(jv)
        let f = car(fv)
        if eql(j, i) {
          if !eq(tem, var_) {
            raise LispError::SimpleError("bad")
          }
          let cof = pcoeff(f, list3(var_, j, Fix(1L)))
          let mut ffv = eqns
          let mut jjv = deg_vector
          while ffv is Cons(_) && jjv is Cons(_) {
            let ff = car(ffv)
            let jj = car(jjv)
            // ff=a*y^i+b f=c*y^j+d
            // if j<=i  want to replace ff by
            // ff-f*a/c*y^(i-j)  (i.e. c*ff-a*f*y^i-j )
            // and this will be ok if
            //  (denom (a/c) is invertible )
            if num_ge(jj, j) && !eql(f, ff) {
              let fac = ratreduce(pcoeff(ff, list3(var_, jj, Fix(1L))), cof)
              if may_invertp(denom(fac), open_g).truthy() {
                eqns = remove_equal(ff, eqns)
                let answ = pdifference(
                  ptimes(denom(fac), ff),
                  gen_ptimes(
                    list3(
                      f,
                      pexpt(list3(var_, Fix(1L), Fix(1L)), num_sub(jj, j)),
                      num(fac),
                    ),
                  ),
                )
                if d_zerop(answ) is Nil {
                  eqns = cons(answ, eqns)
                }
                changed = true
                start_over = true
                break
              }
            }
            ffv = cdr(ffv)
            jjv = cdr(jjv)
          }
          if start_over {
            break
          }
        }
        jv = cdr(jv)
        fv = cdr(fv)
      }
      if start_over {
        break
      }
    }
    if start_over {
      break
    }
    vari = cdr(vari)
  }
  if changed {
    simp_lead1(eqns, open_g~, variables~)
  } else {
    eqns
  }
}

///|
fn affine_open(list_vars : Value, inequal? : Value = Fix(1L)) -> Value raise {
  let mut fns : Value = Nil
  if atom(car(list_vars)) {
    if sheafa__get(car(list_vars), q_disrep).truthy() {
      fns = mapcar(v => list3(v, Fix(1L), Fix(1L)), list_vars)
    }
  } else if mbagp(list_vars).truthy() {
    fns = st_rat(list_vars)
  } else {
    fns = list_vars
  }
  let coords = construct_rmap(fns)
  sheafa__make_zopen(coord=coords, inv=coords, inequality=inequal)
}

///|
fn construct_pre_ldata_sheaves(
  s_var? : Value = Nil,
  data? : Value = Nil,
  opens? : Value = Nil,
) -> Value raise {
  sheafa__check_arg(
    data is Nil || car(data) is Nil || eq(car(car(car(data))), q_ldata),
    "list of lists of ldata",
  )
  sheafa__check_arg(s_var is Nil || eq(car(s_var), q_s_var), "s-var")
  let mut s_var = s_var
  if opens.truthy() {
    s_var = sheafa__make_s_var(zopens=opens)
  }
  sheafa__make_pls(s_var~, data~)
}

///|
/// `(defremember grobner-basis-remember (basis &aux tem answ) ...)`: to
/// try to implement not checking twice and timing out.
fn sheafa__grobner_basis_remember(basis : Value) -> Value raise {
  sheafa__remember(q_grobner_basis_remember, list1(basis), () => {
    let mut tem : Value = Nil
    catch_tag(q_took_too_long, () => {
      tem = grobner_basis(basis)
      tem
    })
    |> ignore
    if tem.truthy() {
      tem
    } else {
      list3(
        q_took_too_long,
        symval(q_ear_timed_grobner_basis),
        symval(q_ear_poly_simplifications),
      )
    }
  })
}

///|
fn grobner_remember(basis : Value) -> Value raise {
  let simps = sheafa__grobner_basis_remember(basis)
  if eq(car(simps), q_took_too_long) {
    if eq(second(simps), symval(q_ear_timed_grobner_basis)) {
      set(q_ear_poly_simplifications, third(simps)) |> ignore
      throw_tag(q_took_too_long, q_took_too_long)
    } else {
      // (setf (gethash (get 'grobner-basis-remember :memory-table) basis)
      // nil): the arguments of GETHASH are swapped in the Lisp, so BASIS is
      // used as the hash table.
      sethash(get(q_grobner_basis_remember, q_kw_memory_table), basis, Nil)
      |> ignore
      grobner_remember(basis)
    }
  } else {
    set(q_ear_poly_simplifications, sheafa__grobner_basis_remember(basis))
  }
}

///|
fn variety_ldata_subset(
  ld1 : Value,
  ld2 : Value,
  open_g? : Value = Fix(1L),
  ignore_ldata_inequalities? : Value = Nil,
) -> (Value, Value) raise {
  if ignore_ldata_inequalities.truthy() {
    let (cont, unit) = grobner_subset(
      sheafa__ldata_eqns(ld2),
      sheafa__ldata_eqns(ld1),
      may_invert=open_g,
    )
    (cont, if unit.truthy() { q_empty } else { Nil })
  } else {
    let gg = nplcm(open_g, sheafa__ldata_inequality(ld1))
    if unit_idealp(
        cons(sheafa__ldata_inequality(ld2), sheafa__ldata_eqns(ld1)),
        may_invert=gg,
      ).truthy() {
      // return only one value since we don't want to test if ld1 is empty
      // on open-g
      (
        grobner_subset(
          sheafa__ldata_eqns(ld2),
          sheafa__ldata_eqns(ld1),
          may_invert=nplcm(gg, sheafa__ldata_inequality(ld2)),
        ).0,
        Nil,
      )
    } else {
      (Nil, Nil)
    }
  }
}

///|
fn delete_redundant_ldata(
  list_ld : Value,
  open_g? : Value = Fix(1L),
  gg? : Value = Fix(1L),
  ignore_ldata_inequalities? : Value = Nil,
) -> Value raise {
  let gg = sftimes(open_g, gg)
  let kept = Collector::new()
  for v in list_ld.iter() {
    if unit_idealp(
        sheafa__ldata_eqns(v),
        may_invert=nplcm(sheafa__ldata_inequality(v), gg),
      )
      is Nil {
      kept.add(v)
    } else {
      format(t, "~2%Deleting the empty ldata ", []) |> ignore
      fsh(v) |> ignore
    }
  }
  let list_ld = kept.result()
  let mut redundant : Value = Nil
  let mut vi = 0
  for v in list_ld.iter() {
    let mut wi = 0
    for w in list_ld.iter() {
      if !(member_equal(int(vi), redundant).truthy() ||
        member_equal(int(wi), redundant).truthy() ||
        vi == wi) {
        if variety_ldata_subset(
            v,
            w,
            open_g=gg,
            ignore_ldata_inequalities~,
          ).0.truthy() {
          redundant = cons(int(vi), redundant)
          format(t, "~2%Deleting redundant component", []) |> ignore
          fsh(v) |> ignore
          format(t, "~%contained in ", []) |> ignore
          fsh(w) |> ignore
        }
      }
      wi += 1
    }
    vi += 1
  }
  let c = Collector::new()
  let mut i = 0
  for v in list_ld.iter() {
    if member_equal(int(i), redundant) is Nil {
      c.add(v)
    }
    i += 1
  }
  c.result()
}

///|
fn describe_ldata(ld : Value) -> Value raise {
  if eq(car(ld), q_ldata) {
    format(t, "~%The ~A  equations are ..", [
      int(length(sheafa__ldata_eqns(ld))),
    ])
    |> ignore
    shl(sheafa__ldata_eqns(ld)) |> ignore
    format(t, "~%The inequality for the component calculation was ..", [])
    |> ignore
    sh(sheafa__ldata_inequality(ld))
  } else {
    mapcar(x => describe_ldata(x), ld)
  }
}

///|
fn d_add_to_solution_tree(a_list : Value) -> Value raise {
  sheafa__check_arg(d_listp(a_list).truthy(), "macsymya list")
  // check this case had not been done yet:
  let mut fixed = false
  for u in cdr(a_list).iter() {
    sheafa__check_arg(d_listp(u).truthy(), "macsyma list")
    let tem = from_case(u)
    for _v in symval(q_d_solution_tree).iter() {
      if equal(from_case(a_list), tem) {
        if sheafb__ask("Remove from $solution_tree case ~A", [tem], true) {
          let tempp = Collector::new()
          for v in symval(q_d_solution_tree).iter() {
            let tem1 = from_case(v)
            if !(initial_equal(tem1, tem).truthy() &&
              num_ge(int(length(tem1)), tem)) {
              tempp.add(v)
            }
          }
          set(q_d_solution_tree, tempp.result()) |> ignore
          fixed = true
          break
        }
      }
    }
    if fixed {
      break
    }
  }
  set(
    q_d_solution_tree,
    cons(list1(q_mlist), append(cdr(a_list), cdr(symval(q_d_solution_tree)))),
  )
  |> ignore
  d_sort_solution_tree()
}

///|
fn d_simplify_relative(system : Value, poly : Value) -> Value raise {
  d_grobner_basis(list2(list1(q_mlist), poly)) |> ignore
  append(delete(Fix(0L), d_totaldisrep(d_polysimp(system))), list1(poly))
}

///|
fn d_list_irreducible_factors(poly : Value) -> Value raise {
  if atom(poly) {
    list2(list1(q_mlist), poly)
  } else if mbagp(poly).truthy() {
    cons(car(poly), mapcar(x => d_list_irreducible_factors(x), cdr(poly)))
  } else if eq(caar(poly), q_mtimes) {
    if memq(q_factored, car(poly)).truthy() {
      let mut answer : Value = Nil
      for u in cdr(poly).iter() {
        if atom(u) {
          answer = cons(u, answer)
        } else if eq(caar(u), q_mplus) {
          answer = cons(u, answer)
        } else if eq(caar(u), q_mexpt) {
          answer = cons(second(u), answer)
        }
      }
      d_sort(cons(list1(q_mlist), zl_union(list1(answer))))
    } else {
      d_list_irreducible_factors(d_factor(poly))
    }
  } else if eq(caar(poly), q_mexpt) {
    d_list_irreducible_factors(d_factor(second(poly)))
  } else if eq(caar(poly), q_mplus) {
    if memq(q_irreducible, car(poly)).truthy() {
      list2(list1(q_mlist), poly)
    } else {
      d_list_irreducible_factors(d_factor(poly))
    }
  } else {
    merr("how did you get here", [])
  }
}

///|
fn d_show_solution_tree(full_format? : Value = Nil) -> Value raise {
  for v in cdr(symval(q_d_solution_tree)).iter() {
    let tem = from_case(v)
    match length(tem) {
      0 => {
        format(t, "~%Cases for the solution tree", []) |> ignore
        if full_format.truthy() {
          i__dolgrind(v) |> ignore
        }
      }
      1 => {
        format(t, "~%  Case: ~A", [string_grind(car(tem))]) |> ignore
        if full_format.truthy() {
          i__dolgrind(v) |> ignore
        }
      }
      2 =>
        format(t, "~%    Subcase ~A", [string_grind(second(tem))]) |> ignore
      3 =>
        format(t, "~%       Subsubcase ~A", [string_grind(third(tem))])
        |> ignore
      _ =>
        format(t, "~%         Sub......~A", [string_grind(nthcdr(3, tem))])
        |> ignore
    }
  }
  q_d_done
}

///|
/// rather crude see cancel below
fn d_eliminate_nonzero_factors(system : Value, l : Value) -> Value raise {
  let mut l = l
  if symval(q_d_nonzero_factors).truthy() {
    l = append(l, cdr(symval(q_d_nonzero_factors)))
  }
  if l.truthy() {
    let system = div_star(system, power(mul_star(l), Fix(10L)))
    d_numerator(system)
  } else {
    system
  }
}

///|
/// tries to return same type
fn d_cancel_factors_and_denominators(
  variety : Value,
  factors_to_elim : Value,
  homogeneous? : Value = Nil,
) -> Value raise {
  let mut factors_to_elim = factors_to_elim
  if atom(factors_to_elim) {
    factors_to_elim = list1(factors_to_elim)
  } else if d_listp(factors_to_elim).truthy() {
    factors_to_elim = cdr(factors_to_elim)
  }
  sheafa__check_arg(d_listp(variety).truthy(), "macsyma list")
  let type_ = if affine_polynomialp(second(variety)).truthy() {
    "polynomial"
  } else if rational_functionp(second(variety)).truthy() {
    "rational-function"
  } else if d_ratp(second(variety)).truthy() {
    "$rat"
  } else {
    "general"
  }
  let rat_variety = mapcar(v => new_rat(v), cdr(variety))
  let mut system = rat_variety
  if homogeneous.truthy() {
    let mut tem : Value = Fix(1L)
    for w in rat_variety.iter() {
      tem = nplcm(tem, denom(w))
    }
    let tem = cons(tem, Fix(1L))
    system = mapcar(w => num(rattimes(tem, w, t)), system)
  } else {
    system = mapcar(w => num(w), rat_variety)
  }
  sheafa__show("FACTORS-TO-ELIM", factors_to_elim)
  for v in factors_to_elim.iter() {
    let mut tem = pexpt(st_rat(v), Fix(7L))
    if homogeneous.truthy() {
      let mut done = false
      for w in system.iter() {
        tem = npgcd(tem, w)
        if numberp(tem) {
          done = true
          break
        }
      }
      if !done {
        let tem1 = tem
        system = mapcar(w => pquotient(w, tem1), system)
      }
    } else {
      let tem1 = tem
      system = mapcar(w => num(ratreduce(w, tem1)), system)
    }
  }
  match type_ {
    "general" =>
      cons(list1(q_mlist), mapcar(w => new_disrep(w), system))
    "$rat" => cons(list1(q_mlist), mapcar(w => header_poly(w), system))
    _ => system
  }
}

///|
/// Performs the substitutions of chart and cancels the exceptional divisor
/// and gets rid of denominators.  It does this homogeneously if the value
/// of homogeneous is not nil.
fn d_blowup_chart(
  chart : Value,
  variety : Value,
  homogeneous? : Value = Nil,
) -> Value raise {
  sheafa__check_arg(d_listp(chart).truthy(), "macsyma list")
  sheafa__check_arg(d_listp(variety).truthy(), "macsyma list")
  let mut tem = third(second(chart))
  for w in cdr(chart).iter() {
    sheafa__show("TEM", tem)
    tem = d_gcd(tem, third(w), Nil)
  }
  let divisor = tem
  format(t, "~%The exceptional divisor is ~A", [tem]) |> ignore
  let transform = d_sublis(chart, variety)
  d_cancel_factors_and_denominators(
    transform,
    list2(list1(q_mlist), divisor),
    homogeneous~,
  )
}

///|
fn my_minor(
  mat : Value,
  rows_to_take : Value,
  cols_to_take : Value,
) -> Value raise {
  d_determinant(d_sub_matrix(mat, rows_to_take, cols_to_take))
}

///|
fn d_wedge_matrix(mat : Value, n : Value) -> Value raise {
  let tabl = sheafa__list_tableaux(n, d_length(second(mat)))
  sheafa__show("TABL", tabl)
  let temm = Collector::new()
  for u in tabl.iter() {
    let tem = Collector::new()
    for v in tabl.iter() {
      tem.add(my_minor(mat, u, v))
    }
    temm.add(cons(list1(q_mlist), tem.result()))
  }
  cons(list1(q_d_matrix), temm.result())
}

///|
fn d_sublis_and_add(eqns : Value, expr : Value, elimin : Value) -> Value raise {
  let mut answer = d_sublis(eqns, expr)
  sheafa__show("ELIMIN", elimin)
  answer = append(answer, mapcar(x => bring_to_left_side(x), cdr(eqns)))
  answer = d_factor(d_eliminate_nonzero_factors(answer, elimin))
  answer
}

///|
/// The loop's FINALLY clause returns nothing, so this always returns NIL
/// (after the substitutions).
fn d_remove_linears(eqns : Value) -> Value raise {
  let mut eqns = eqns
  let mut subs : Value = Nil
  let mut lins : Value = Nil
  let lin_vars = Collector::new()
  let lin_eqns = Collector::new()
  for v in cdr(eqns).iter() {
    lins = cdr(d_coll_linear(eqns))
    if lins.truthy() {
      lin_vars.append_list(copy_list(lins))
      lin_eqns.add(v)
    }
  }
  let lin_vars = lin_vars.result()
  if lins.truthy() {
    subs = d_fast_linsolve(
      cons(list1(q_mlist), lin_eqns.result()),
      variables=cons(list1(q_mlist), zl_union(list1(lin_vars))),
    )
    format(t, "~%Eliminating linear variables ~A", [lin_vars]) |> ignore
  }
  if subs.truthy() {
    eqns = d_sublis(subs, eqns)
    eqns = append(
      delete(Fix(0L), d_ratsimp(eqns, Nil)),
      mapcar(v => d_numerator(sub_star(second(v), third(v))), subs),
    )
  }
  Nil
}

///|
/// `(find-minimal in-list ordering &optional such-that ind)`: returns the
/// macro expansion.  (SUCH-THAT is never a function object at expansion
/// time.)
fn find_minimal(
  in_list : Value,
  ordering : Value,
  such_that? : Value = Nil,
  ind? : Value = Nil,
) -> Value raise {
  let p_ind = sym("find-minimal-ind")
  let p_list = sym("find-minimal-in-list")
  let p_such = sym("find-minimal-such-that")
  let p_ord = sym("find-minimal-ordering")
  if such_that.truthy() {
    sheafa__check_arg(ind.truthy(), "non nil.  Must specify index")
    let tmpl = lread(
      "(loop for find-minimal-ind in find-minimal-in-list with prev-min when find-minimal-such-that do (cond (prev-min (cond ((funcall find-minimal-ordering find-minimal-ind prev-min) (setq prev-min find-minimal-ind)))) (t (setq prev-min find-minimal-ind))) finally (return prev-min))",
    )
    sublis(
      list([
        cons(p_ind, ind),
        cons(p_list, in_list),
        cons(p_such, such_that),
        cons(p_ord, ordering),
      ]),
      tmpl,
    )
  } else {
    let tmpl = lread(
      "(loop for v in find-minimal-in-list with prev-min do (cond (prev-min (cond ((funcall find-minimal-ordering v prev-min) (setq prev-min v)))) (t (setq prev-min v))) finally (return prev-min))",
    )
    sublis(list([cons(p_list, in_list), cons(p_ord, ordering)]), tmpl)
  }
}

///|
/// The counting function tests `(member v vars)` (not `(member v w)`), so
/// every count is 0 and the order is that of ALL-VARS.
fn find_good_variable_order(ideal : Value) -> Value raise {
  let vars = mapcar(x => cdr(x), mapcar(x => d_list_variables(x, Nil), cdr(ideal)))
  let all_vars = zl_union(list1(apply(sym("append"), vars)))
  let f = (v : Value) => {
    let mut tem = 0
    for _w in vars.iter() {
      if member(v, vars).truthy() {
        tem += 1
      }
    }
    tem
  }
  sort_list(all_vars, (u, v) => f(u) < f(v))
}

///|
fn may_invertp(poly : Value, invertible_poly : Value) -> Value raise {
  if d_zerop(poly).truthy() {
    Nil
  } else {
    lbool(numberp(denom(ratreduce(invertible_poly, square_free(poly)))))
  }
}

///|
fn poly_linearp(poly : Value, var_ : Value, may_invert : Value) -> Value raise {
  if numberp(poly) {
    Nil
  } else if eql(pdegree(poly, var_), Fix(1L)) {
    let cof = pcoeff(poly, list3(var_, Fix(1L), Fix(1L)))
    if atom(cof) {
      cof
    } else if may_invertp(cof, may_invert).truthy() {
      cof
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// This seems the most efficient.  If may-invert is x^2-1 then
/// u*(x+1)+h(w,v) will cause the replacement u--> -h(w,v)/(x+1) in the
/// remaining eqns, then it calls itself on the remaining equations.  (The
/// RETURN-FROM only leaves the block SUE, so the computed list is
/// discarded and EQNS is returned.)
fn remove_linears(eqns : Value, may_invert? : Value = Fix(1L)) -> Value raise {
  sheafa__check_arg(
    affine_polynomialp(car(eqns)).truthy(),
    "first term not  polynomial",
  )
  for v in eqns.iter() {
    // block sue
    for vari in list_variables(v).iter() {
      let cof = poly_linearp(v, vari, may_invert)
      if cof.truthy() {
        let sub = cons(
          vari,
          pdifference(ptimes(list3(vari, Fix(1L), Fix(1L)), cof), v),
        )
        // DENOM is a free (special) variable here.
        set(q_denom, cof) |> ignore
        let new_eqn = Collector::new()
        for uu in eqns.iter() {
          if !equal(uu, v) {
            new_eqn.add(psublis(list1(sub), symval(q_denom), uu))
          }
        }
        let _ = cons(
          num(ratreduce(v, cof)),
          remove_linears(new_eqn.result(), may_invert~),
        )
        break
      }
    }
  }
  eqns
}

///|
/// makes $char_set from an ideal-generators pushing the leading coefs into
/// *to-invert*
fn d_ritt_set(
  ideal_generators : Value,
  may_invert? : Value = Fix(1L),
) -> Value raise {
  let id = sheafa__make_ideal()
  set(q_d_ideal, id) |> ignore
  sheafa__set_ideal_variable_correspondence(
    id,
    order_variables(find_good_variable_order(ideal_generators)),
  )
  |> ignore
  let rc = Collector::new()
  for u in cdr(ideal_generators).iter() {
    let tem = st_rat(u)
    if pzerop(tem) is Nil {
      rc.add(tem)
    }
  }
  let mut rat_ideal = rc.result()
  let may_invert = st_rat(may_invert)
  rat_ideal = remove_linears(rat_ideal, may_invert~)
  set(
    q_vars,
    reverse(
      sort_list(list_variables(rat_ideal), (a, b) => pointergp(a, b).truthy()),
    ),
  )
  |> ignore
  sheafa__show("VARS", symval(q_vars))
  sheafa__show("(CAR RAT-IDEAL)", car(rat_ideal))
  set(q_ear_to_invert, list1(may_invert)) |> ignore
  rat_ideal = mapcar(v => remove_common_factors(v, may_invert), rat_ideal)
  let cs = Collector::new()
  for v in symval(q_vars).iter() {
    // (find-minimal rat-ideal #'(lambda (u v) (< (p-le u) (p-le v)))
    //               (and (listp pol) (eq (p-var pol) v)) pol)
    let mut prev_min : Value = Nil
    for pol in rat_ideal.iter() {
      if listp(pol) && eq(p__var(pol), v) {
        if prev_min.truthy() {
          if num_lt(p__le(pol), p__le(prev_min)) {
            prev_min = pol
          }
        } else {
          prev_min = pol
        }
      }
    }
    let temm = prev_min
    if temm.truthy() {
      sheafa__show("TEMM", temm)
      cs.add(temm)
    }
  }
  set(q_d_char_set, cs.result()) |> ignore
  for v in rat_ideal.iter() {
    let tem = ritt_reduce(v, symval(q_d_char_set))
    sheafa__mshow("TEM", tem)
    sheafa__show("(LENGTH $CHAR_SET)", int(length(symval(q_d_char_set))))
    if pzerop(tem) is Nil {
      set(q_d_char_set, add_to_chain(tem, symval(q_d_char_set))) |> ignore
    }
  }
  set(
    q_d_char_set,
    eliminate_factors(symval(q_d_char_set), symval(q_ear_to_invert)),
  )
  |> ignore
  sheafa__set_ideal_char_set(id, symval(q_d_char_set)) |> ignore
  sheafa__set_ideal_localization(id, symval(q_ear_to_invert)) |> ignore
  d_disrep_ideal(id)
}

///|
fn eliminate_factors(good : Value, factors_to_elim : Value) -> Value raise {
  let mut good = good
  for v in factors_to_elim.iter() {
    let mon = pexpt(v, Fix(5L))
    good = mapcar(w => num(ratreduce(w, mon)), good)
  }
  good
}

///|
fn header_fake(expr : Value) -> Value raise {
  let head = list3(q_mrat, Nil, Nil)
  if numberp(expr) || sheafa__get(car(expr), q_disrep).truthy() {
    cons(head, cons(expr, Fix(1L)))
  } else if (numberp(car(expr)) || sheafa__get(caar(expr), q_disrep).truthy()) &&
    (numberp(cdr(expr)) || sheafa__get(cadr(expr), q_disrep).truthy()) {
    cons(head, expr)
  } else {
    merr("not a rat'l fun or poly (at least no disrep prop)", [])
  }
}

///|
fn fake_disrep(pol : Value) -> Value raise {
  d_totaldisrep(header_fake(pol))
}

///|
fn d_disrep_ideal(ideal : Value) -> Value raise {
  list3(
    list1(q_mlist),
    cons(
      list1(q_mlist),
      mapcar(x => fake_disrep(x), sheafa__ideal_char_set(ideal)),
    ),
    cons(
      list1(q_mlist),
      mapcar(x => fake_disrep(x), sheafa__ideal_localization(ideal)),
    ),
  )
}

///|
fn square_free(p : Value) -> Value raise {
  let facts = psqfr(p)
  if cddr(facts).truthy() {
    let mut answer = car(facts)
    let mut v = cddr(facts)
    while v is Cons(_) {
      answer = ptimes(car(v), answer)
      v = cddr(v)
    }
    answer
  } else {
    car(facts)
  }
}

///|
fn d_square_free_numerators(expr : Value) -> Value raise {
  if atom(expr) {
    expr
  } else if affine_polynomialp(expr).truthy() {
    square_free(expr)
  } else if rational_functionp(expr).truthy() {
    square_free(num(expr))
  } else if d_ratp(expr).truthy() {
    cons(car(expr), cons(square_free(num(cdr(expr))), Fix(1L)))
  } else if mbagp(expr).truthy() {
    cons(car(expr), mapcar(x => d_square_free_numerators(x), cdr(expr)))
  } else {
    let tem = new_rat(expr)
    header_poly(cons(square_free(num(tem)), Fix(1L)))
  }
}

///|
fn add_to_chain(poly : Value, chain : Value) -> Value raise {
  let poly = square_free(poly)
  if eql(poly, Fix(0L)) {
    chain
  } else {
    let mut chain = chain
    for v in chain.iter() {
      if eq(p__var(poly), p__var(v)) {
        if num_lt(p__le(poly), p__le(v)) {
          sheafa__show("'DELETING", q_deleting)
          chain = remove_equal(v, chain)
        } else if num_ge(p__le(poly), p__le(v)) {
          sheafa__mshow("POLY", poly)
          sheafa__mshow("V", v)
          merr("not reduced", []) |> ignore
        }
      }
    }
    format(t, "~%adding ..", []) |> ignore
    sh(poly) |> ignore
    chain = sort_list(cons(poly, chain), (u, v) => pointergp(p__var(u), p__var(v)).truthy())
    chain
  }
}

///|
fn order_variables(list_of_vars : Value) -> Value raise {
  let mut list_of_vars = list_of_vars
  if d_listp(list_of_vars).truthy() {
    list_of_vars = cdr(list_of_vars)
  }
  let vc = sheafa__make_vc()
  let gen = Collector::new()
  let mut i = 1
  for v in list_of_vars.iter() {
    let w = gensym()
    gen.add(w)
    putprop(w, v, q_disrep) |> ignore
    set(w, int(i)) |> ignore
    i += 1
  }
  sheafa__set_vc_genvar(vc, gen.result()) |> ignore
  sheafa__set_vc_varlist(vc, copy_list(list_of_vars)) |> ignore
  vc
}

///|
/// `(with-vc var-corr &rest body)`: returns the macro expansion.
fn with_vc(var_corr : Value, body : Value) -> Value raise {
  let p_vc = sym("with-vc-var-corr")
  let p_progn = sym("with-vc-progn")
  let tmpl = lread(
    "(let ((*genvar* (vc-genvar with-vc-var-corr)) (*varlist* (vc-varlist with-vc-var-corr))) (unwind-protect with-vc-progn (setf (vc-genvar with-vc-var-corr) *genvar*) (setf (vc-varlist with-vc-var-corr) *varlist*)))",
  )
  sublis(list([cons(p_vc, var_corr), cons(p_progn, cons(q_progn, body))]), tmpl)
}

///|
fn must_ritt_reducep(poly : Value, ch_set : Value) -> Value raise {
  if atom(poly) {
    Nil
  } else {
    for v in ch_set.iter() {
      if eq(p__var(poly), p__var(v)) {
        if num_ge(p__le(poly), p__le(v)) {
          return t
        }
      }
    }
    Nil
  }
}

///|
/// assumes the ch-set is sorted by main variables
fn ritt_reduce(poly : Value, ch_set : Value) -> Value raise {
  let mut poly = poly
  while must_ritt_reducep(poly, ch_set).truthy() {
    for v in ch_set.iter() {
      if numberp(poly) {
        break
      }
      if eq(p__var(poly), p__var(v)) {
        if num_ge(p__le(poly), p__le(v)) {
          let tem = vdivide(poly, v)
          poly = second(tem)
          if !numberp(third(tem)) {
            set(
              q_ear_to_invert,
              list1(nplcm(third(tem), car(symval(q_ear_to_invert)))),
            )
            |> ignore
          }
          sheafa__show("*TO-INVERT*", symval(q_ear_to_invert))
        }
      }
    }
  }
  poly
}

// rational-map  will be type rmap
//   funs (f1 f2 ... fn) denom gg
// zopen set : (((p1,  pn)gp) (q1,..qn) gq),gg
// where zi=qi(x1,x2,  xn)/gp and xi=pi(z1,..,zn)/gq

///|
/// `(ignore-rat-err (pquotient x y))`
fn my_testdivide(x : Value, y : Value) -> Value raise {
  let mut result : Value = Nil
  let mut error_p = true
  catch_tag(q_rat_err, () => {
    result = pquotient(x, y)
    error_p = false
    Nil
  })
  |> ignore
  if error_p {
    Nil
  } else {
    result
  }
}

///|
fn new_testdivide(f : Value, g : Value) -> Value raise {
  let mut quot = ratreduce(f, g)
  quot = if equal(denom(quot), Fix(1L)) { num(quot) } else { Nil }
  if !equal(quot, my_testdivide(f, g)) {
    fsignal(
      list2(
        Str("The expression ~A was not true"),
        lread("(equal quot (my-testdivide f g))"),
      ),
    )
    |> ignore
  }
  quot
}

///|
fn eliminate_highest_power_dividing_homogeneously(
  list_fns : Value,
  divisor : Value,
  highest_deg? : Value = Fix(10000L),
) -> Value raise {
  if numberp(divisor) && equal(num_abs(divisor), Fix(1L)) {
    list_fns
  } else {
    let mut prev_list_quotients = list_fns
    let mut i : Value = Fix(1L)
    while true {
      let new_quotients = Collector::new()
      for v in prev_list_quotients.iter() {
        let quot = my_testdivide(v, divisor)
        if quot is Nil || num_gt(i, highest_deg) {
          return prev_list_quotients
        } else {
          new_quotients.add(quot)
        }
      }
      prev_list_quotients = new_quotients.result()
      i = num_add(i, Fix(1L))
    }
    Nil
  }
}

///|
fn sort_remember(
  list_ : Value,
  predicate : Value,
  key? : Value = Nil,
) -> (Value, Value) raise {
  let c = Collector::new()
  let mut i = 0
  for v in list_.iter() {
    c.add(cons(int(i), v))
    i += 1
  }
  // :key is #'(lambda (x) (key (cdr x))) when KEY is given: a call of the
  // (undefined) function KEY.
  let lst = sort_list(c.result(), (a, b) => {
    let (ka, kb) = if key.truthy() {
      (sheafb__undefined("KEY"), sheafb__undefined("KEY"))
    } else {
      (cdr(a), cdr(b))
    }
    funcall(predicate, [ka, kb]).truthy()
  })
  let ordering = Collector::new()
  let mut v = lst
  while v is Cons(_) {
    ordering.add(caar(v))
    setf_car(v, cdar(v)) |> ignore
    v = cdr(v)
  }
  (lst, ordering.result())
}

///|
fn un_sort(list_ : Value, ordering : Value) -> Value raise {
  let n = length(ordering)
  let cells : Array[Value] = Array::make(n, Nil)
  let newlist = list(cells)
  let mut o = ordering
  let mut l = list_
  while o is Cons(_) && l is Cons(_) {
    let cell = nthcdr(to_int(car(o)), newlist)
    if cell is Nil {
      raise LispError::SimpleError(
        format_to_string("~A is too large an index for SETF of NTH.", [car(o)]),
      )
    }
    setf_car(cell, car(l)) |> ignore
    o = cdr(o)
    l = cdr(l)
  }
  newlist
}

///|
fn sort_by_ordering(list_ : Value, ordering : Value) -> Value raise {
  mapcar(v => nth(to_int(v), list_), ordering)
}

///|
/// copies the list and sorts by predicate. If slow-key, it uses only one
/// application of the key per item.  If slow-key or remember it returns a
/// second value : the ordering so that (un-sort  result ordering) would
/// restore the list
fn copy_sort(
  list_ : Value,
  predicate : Value,
  key? : Value = Nil,
  slow_key? : Value = Nil,
  remember? : Value = Nil,
) -> (Value, Value) raise {
  if slow_key.truthy() {
    let (_, order) = sort_remember(
      mapcar(x => funcall(slow_key, [x]), list_),
      predicate,
    )
    (sort_by_ordering(list_, order), order)
  } else if remember.truthy() {
    sort_remember(list_, predicate, key~)
  } else {
    (
      sort_list(copy_list(list_), (a, b) => {
        let (ka, kb) = if key.truthy() {
          (funcall(key, [a]), funcall(key, [b]))
        } else {
          (a, b)
        }
        funcall(predicate, [ka, kb]).truthy()
      }),
      Nil,
    )
  }
}

///|
/// This works for rational functions as well; should be fixed to use
/// complexity to.  (Try to speed up by putting simple ones first.)
fn eliminate_common_factors(list_functions : Value) -> Value raise {
  let (list_fns, order) = copy_sort(
    list_functions,
    lfunc("<", args => lbool(num_lt(args[0], args[1]))),
    slow_key=lfunc("eliminate-common-factors-key", args => num_add(
      pcomplexity(function_numerator(args[0])),
      pcomplexity(function_denominator(args[0])),
    )),
  )
  let firs = car(list_fns)
  let mut num_gcd : Value = Nil
  let mut denom_gcd : Value = Nil
  if affine_polynomialp(firs).truthy() {
    num_gcd = firs
    denom_gcd = Fix(1L)
  } else if rational_functionp(firs).truthy() {
    num_gcd = num(firs)
    denom_gcd = denom(firs)
  }
  for v in cdr(list_fns).iter() {
    if affine_polynomialp(v).truthy() {
      num_gcd = pgcd(num_gcd, v)
      denom_gcd = Fix(1L)
    } else {
      // (check-arg v 'rational-functionp ...) asserts the quoted symbol.
      num_gcd = pgcd(num_gcd, num(v))
    }
  }
  un_sort(
    mapcar(
      v => st_rat(
        cons(
          pquotient(function_numerator(v), num_gcd),
          pquotient(function_denominator(v), denom_gcd),
        ),
      ),
      list_fns,
    ),
    order,
  )
}

///|
fn reduce_rational_map_old(rmap : Value) -> Value raise {
  let mut gc = sheafa__rmap_denom(rmap)
  let b1 = bind(q_genvar, symval(q_ear_genvar))
  defer unbind(b1)
  let b2 = bind(
    q_genvar,
    nreverse(
      sort_list(
        list_variables(cons(sheafa__rmap_denom(rmap), sheafa__rmap_fns(rmap))),
        (a, b) => pointergp(a, b).truthy(),
      ),
    ),
  )
  defer unbind(b2)
  for v in sheafa__rmap_fns(rmap).iter() {
    gc = pgcd(gc, v)
  }
  let answ = sheafa__make_rmap()
  let gc1 = gc
  sheafa__set_rmap_fns(
    answ,
    mapcar(v => pquotient(v, gc1), sheafa__rmap_fns(rmap)),
  )
  |> ignore
  sheafa__set_rmap_denom(answ, pquotient(sheafa__rmap_denom(rmap), gc)) |> ignore
  answ
}

///|
fn reduce_rational_map(rmap : Value) -> Value raise {
  let b1 = bind(q_genvar, symval(q_ear_genvar))
  defer unbind(b1)
  let b2 = bind(
    q_genvar,
    nreverse(
      sort_list(
        list_variables(cons(sheafa__rmap_denom(rmap), sheafa__rmap_fns(rmap))),
        (a, b) => pointergp(a, b).truthy(),
      ),
    ),
  )
  defer unbind(b2)
  let fns = cons(sheafa__rmap_denom(rmap), sheafa__rmap_fns(rmap))
  let red_fns = eliminate_common_factors(fns)
  // (zl-copy-structure rmap rmap- fns (cdr red-fns) denom (car red-fns))
  let answ = copy_list(rmap)
  sheafa__set_rmap_fns(answ, cdr(red_fns)) |> ignore
  sheafa__set_rmap_denom(answ, car(red_fns)) |> ignore
  answ
}

///|
fn convert_rmap_to_new(name : Value) -> Value raise {
  let fns = mapcar(
    v => ratreduce(v, sheafa__rmap_denom(name)),
    sheafa__rmap_fns(name),
  )
  let ans = copy_list(name)
  sheafa__set_rmap_fns(ans, fns) |> ignore
  ans
}

///|
fn new_rmap_p(rmap : Value) -> Value raise {
  if !eq(car(rmap), q_rmap) {
    return Nil
  }
  for v in sheafa__rmap_fns(rmap).iter() {
    if rational_functionp(v) is Nil {
      return Nil
    }
  }
  t
}

///|
/// `(new-rmap f)`: returns the macro expansion.
fn new_rmap(f : Value) -> Value raise {
  let p_f = sym("new-rmap-f")
  sublis(
    list1(cons(p_f, f)),
    lread(
      "(cond ((not (new-rmap-p new-rmap-f)) (format t \"~%Converting an rmap\") (setq new-rmap-f (convert-rmap-to-new new-rmap-f))))",
    ),
  )
}

///|
/// `(new-rmap f)` inline: F converted to an rmap of rational functions.
fn sheafa__new_rmap(f : Value) -> Value raise {
  if new_rmap_p(f) is Nil {
    format(t, "~%Converting an rmap", []) |> ignore
    convert_rmap_to_new(f)
  } else {
    f
  }
}

///|
fn my_pairlis(l : Value, g : Value) -> Value raise {
  zl_pairlis(l, g)
}

///|
/// `(defremember compose-rmap (f g) ...)`
fn sheafa__compose_rmap(f : Value, g : Value) -> Value raise {
  sheafa__remember(sheafa__q_compose_rmap, list2(f, g), () => {
    let f = sheafa__new_rmap(f)
    let g = sheafa__new_rmap(g)
    // (loop for gg in (rmap-fns g) for v in *xxx* collecting (cons v gg))
    let subs = zl_pairlis(symval(q_ear_xxx), sheafa__rmap_fns(g))
    let fns_f = mapcar(ff => simple_rat_sublis(subs, ff), sheafa__rmap_fns(f))
    construct_rmap(fns_f)
  })
}

///|
fn construct_rmap(list_funs : Value) -> Value raise {
  let mut list_funs = list_funs
  let mut answ : Value = Fix(1L)
  if d_listp(list_funs).truthy() {
    list_funs = cdr(list_funs)
  }
  let rat_fns = Collector::new()
  for v in list_funs.iter() {
    if affine_polynomialp(v).truthy() {
      rat_fns.add(cons(v, Fix(1L)))
    } else if rational_functionp(v).truthy() {
      rat_fns.add(v)
    } else if sheafa__get(v, q_disrep).truthy() {
      rat_fns.add(cons(list3(v, Fix(1L), Fix(1L)), Fix(1L)))
    } else {
      rat_fns.add(new_rat(v))
    }
  }
  let rat_fns = rat_fns.result()
  for w in rat_fns.iter() {
    answ = nplcm(answ, denom(w))
  }
  sheafa__make_rmap(fns=rat_fns, denom=answ)
}

///|
fn describe_rmap(rmap : Value) -> Value raise {
  if eq(car(rmap), q_rmap) {
    let tem = mapcar(v => header_poly(v), sheafa__rmap_fns(rmap))
    displa(cons(list1(q_mlist), tem)) |> ignore
    format(t, "Common denom is ..", []) |> ignore
    displa(d_factor(new_disrep(sheafa__rmap_denom(rmap)))) |> ignore
  }
  Nil
}

///|
fn describe_zopen(op : Value) -> Value raise {
  if sheafa__zopen_history(op).truthy() {
    format(t, "~%The opens history is ~A ", [sheafa__zopen_history(op)])
    |> ignore
  }
  if symval(q_ear_give_coordinates).truthy() {
    format(t, "~%Zopen with Coord and inverse", []) |> ignore
    describe_rmap(sheafa__zopen_coord(op)) |> ignore
    describe_rmap(sheafa__zopen_inv(op)) |> ignore
  }
  format(t, "~%inequality is ..", []) |> ignore
  displa(d_factor(new_disrep(sheafa__zopen_inequality(op))))
}

///|
fn xxx(i : Value) -> Value raise {
  list3(nth(to_int(i) - 1, symval(q_ear_xxx)), Fix(1L), Fix(1L))
}

///|
/// I is the index of the special slot so this will return the ith cover of
/// the blowup of the FIRSTK coordinates of DIM-affine space
fn ichart(i : Value, firstk : Value, dim : Value) -> Value raise {
  let n = to_int(dim)
  let c1 = Collector::new()
  for j in 1..=n {
    if num_le(int(j), firstk) && !eql(int(j), i) {
      c1.add(xxx(int(j)))
    } else {
      c1.add(ptimes(xxx(i), xxx(int(j))))
    }
  }
  let den = xxx(i)
  let fns = mapcar(v => ratreduce(v, den), c1.result())
  let pss = construct_rmap(fns)
  let c2 = Collector::new()
  for j in 1..=n {
    if num_le(int(j), firstk) && !eql(i, int(j)) {
      c2.add(ptimes(xxx(i), xxx(int(j))))
    } else {
      c2.add(xxx(int(j)))
    }
  }
  let qss = construct_rmap(c2.result())
  sheafa__make_zopen(coord=pss, inv=qss, inequality=Fix(1L))
}

///|
/// The second definition of DES in the file.
fn des(obj : Value, stream? : Value) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_output)
  }
  with_special(standard_output, stream, () => {
    if atom(obj) {
      format(t, "~s", [obj]) |> ignore
    } else if affine_polynomialp(obj).truthy() ||
      rational_functionp(obj).truthy() {
      sh(obj) |> ignore
    } else {
      let head = car(obj)
      if eq(head, q_zopen) {
        describe_zopen(obj) |> ignore
      } else if eq(head, q_rmap) {
        format(t, "~%Rmap with coordinate functions", []) |> ignore
        describe_rmap(obj) |> ignore
      } else if eq(head, q_ldata) {
        format(t, "~%Ldata with the comoponent equations", []) |> ignore
        describe_ldata(obj) |> ignore
      } else if eq(head, q_pre_ldata_sheaves) {
        format(t, "~%Pre Ldata sheaves", []) |> ignore
        describe_pls(obj) |> ignore
      } else if eq(head, q_components) {
        describe_components(obj) |> ignore
      } else if eq(head, q_s_var) {
        format(t, "~%S Variety with basic open sets :", []) |> ignore
        des(cdr(obj), stream=stream) |> ignore
      } else if macsyma_typep(obj).truthy() {
        string_grind(obj, stream~) |> ignore
      } else {
        let mut i = 0
        for v in obj.iter() {
          if listp(v) && (eq(car(v), q_ldata) || eq(car(v), q_zopen)) {
            format(t, "Number ~D :", [int(i)]) |> ignore
          }
          des(v, stream=stream) |> ignore
          i += 1
        }
      }
    }
    obj
  })
}

///|
/// `(pls-opens pls)` = `(sv-zopens (pls-s-var pls))`
fn pls_opens(pls : Value) -> Value raise {
  sheafa__sv_zopens(sheafa__pls_s_var(pls))
}

///|
/// The dimension list of the ldata LIS-DAT of an open of dimension DIM, and
/// (when REORDER) the ldata with their equations reordered.
/// `(multiple-value (eqns ch-set) (order-equations ..))` is the Maclisp
/// MULTIPLE-VALUE-SETQ.
fn sheafa__dimensions(
  lis_dat : Value,
  dim : Int,
  reorder : Bool,
  collect_new : Bool,
) -> (Value, Value) raise {
  let tem = Collector::new()
  let newl = Collector::new()
  for u in lis_dat.iter() {
    if reorder {
      let (eqns, ch_set) = order_equations(sheafa__ldata_eqns(u))
      if ch_set.truthy() {
        tem.add(int(dim - length(sheafa__ldata_eqns(u))))
      } else {
        tem.add(Str("?"))
      }
      if collect_new {
        newl.add(
          sheafa__make_ldata(
            eqns~,
            inequality=sheafa__ldata_inequality(u),
            usedup=sheafa__ldata_usedup(u),
          ),
        )
      }
    }
  }
  (tem.result(), newl.result())
}

///|
fn describe_pls(pls : Value) -> Value raise {
  format(t, "~%It has ~D opens having ~A components.", [
    int(length(pls_opens(pls))),
    mapcar(u => int(length(u)), sheafa__pls_data(pls)),
  ])
  |> ignore
  let mut vs = sheafa__sv_zopens(sheafa__pls_s_var(pls))
  let mut ws = sheafa__pls_data(pls)
  let mut i = 0
  while vs is Cons(_) && ws is Cons(_) {
    let v = car(vs)
    let mut w = car(ws)
    des(v) |> ignore
    let dim = length(sheafa__rmap_fns(sheafa__zopen_coord(v)))
    let reorder = symval(q_ear_reorder_eqns).truthy()
    let (tem, newl) = sheafa__dimensions(w, dim, reorder, true)
    format(t, "~%with the ~D ldata", [int(length(w))]) |> ignore
    if symval(q_ear_reorder_eqns).truthy() {
      format(t, " of dimension ~A ", [tem]) |> ignore
      w = newl
    }
    format(t, "on  open number ~D: ", [int(i)]) |> ignore
    des(w) |> ignore
    vs = cdr(vs)
    ws = cdr(ws)
    i += 1
  }
  Nil
}

///|
fn make_component_history(
  pls : Value,
  add_to_open_history? : Value = t,
) -> Value raise {
  let res = Collector::new()
  let mut ops = pls_opens(pls)
  let mut lds = sheafa__pls_data(pls)
  while ops is Cons(_) && lds is Cons(_) {
    let op = car(ops)
    let lis_dat = car(lds)
    let dim = length(sheafa__rmap_fns(sheafa__zopen_coord(op)))
    let (tem, _) = sheafa__dimensions(lis_dat, dim, true, false)
    if add_to_open_history.truthy() {
      sheafa__set_zopen_history(
        op,
        cons(cons(q_dimensions, tem), sheafa__zopen_history(op)),
      )
      |> ignore
    }
    res.add(cons(q_dimensions, tem))
    ops = cdr(ops)
    lds = cdr(lds)
  }
  res.result()
}

///|
fn zopen_dim(zop : Value) -> Value raise {
  int(length(sheafa__rmap_fns(sheafa__zopen_coord(zop))))
}

///|
fn init_share_sheafa() -> Unit raise {
  if !boundp(q_ear_xxx) {
    let c = Collector::new()
    for i in 1..=30 {
      c.add(add_newvar(sym("$x" + i.to_string())).0)
    }
    set(q_ear_xxx, c.result()) |> ignore
  }
  if !boundp(q_ear_vvv) {
    let c = Collector::new()
    let mut i = 0
    for _u in symval(q_ear_xxx).iter() {
      c.add(sym("$vv" + i.to_string()))
      i += 1
    }
    set(q_ear_vvv, c.result()) |> ignore
  }
  if !boundp(q_ear_vforx) {
    set(q_ear_vforx, zl_pairlis(symval(q_ear_xxx), symval(q_ear_vvv)))
    |> ignore
  }
  if !boundp(q_ear_xforv) {
    set(q_ear_xforv, zl_pairlis(symval(q_ear_vvv), symval(q_ear_xxx)))
    |> ignore
  }
  if !boundp(q_ear_p3) {
    set(q_ear_p3, sheafa__make_s_var()) |> ignore
  }
}
