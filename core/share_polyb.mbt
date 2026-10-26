// Port of share/affine/polyb.lisp: dot simplifications of non-commutative
// polynomials, checking overlaps, the v- arithmetic, display helpers.
//
// polyb.lisp defines several functions twice (vadd*, vmul*, vsub*,
// vdiv*, vminus*, $vrat, convert-relation-to-dot-simp,
// variables-same-divide); the later definitions are the ones in effect
// and are the ones ported. Its $te and $tes are replaced by later files
// (polysmp.lisp, polyd.lisp).

///|
fn d_circle_times(l : Value) -> Value raise {
  match length(l) {
    0 => Fix(1L)
    1 => car(l)
    2 => {
      let u = car(l)
      let v = second(l)
      let firs = sub_star(
        mul_star(list2(nth(1, u), nth(1, v))),
        mul_star(list2(nth(2, u), nth(2, v))),
      )
      let sec = add_star(
        list2(
          mul_star(list2(nth(1, u), nth(2, v))),
          mul_star(list2(nth(2, u), nth(1, v))),
        ),
      )
      list3(list2(q_mlist, q_simp), firs, sec)
    }
    _ => d_circle_times(list2(car(l), d_circle_times(cdr(l))))
  }
}

///|
fn sort_grouped_list(a_list : Value, group_size : Value, pred : Value) -> Value raise {
  let gs = to_int(group_size)
  let mut if_necessary = false
  let mut prev = car(a_list)
  let mut i = 0
  for v in a_list.iter() {
    if i % gs == 0 {
      if funcall(pred, [v, prev]).truthy() {
        if_necessary = true
        break
      }
      prev = v
    }
    i += 1
  }
  if if_necessary {
    let all = Collector::new()
    let mut v = a_list
    while v.truthy() {
      all.add(v)
      v = nthcdr(gs, v)
    }
    let all = sort_list(all.result(), (a, b) => funcall(pred, [car(a), car(b)]).truthy())
    let c = Collector::new()
    for v in all.iter() {
      let mut w = v
      let mut k = 0
      while w is Cons(_) && k < gs {
        c.add(car(w))
        w = cdr(w)
        k += 1
      }
    }
    c.result()
  } else {
    a_list
  }
}

///|
fn d_sort_dot_simplifications(pred? : Value) -> Value raise {
  let pred = match pred {
    Some(p) => p
    None => symval(q_d_order_function)
  }
  let rev_pred = if eq(pred, q_d_monomial_alphalessp) {
    q_d_monomial_alphagreatp
  } else {
    lfunc("lambda", args => {
      let x = arg(args, 0)
      let y = arg(args, 1)
      lbool(funcall(pred, [x, y]) is Nil && !equal(x, y))
    })
  }
  rplacd(
    symval(q_d_dot_simplifications),
    sort_grouped_list(cdr(symval(q_d_dot_simplifications)), Fix(2L), rev_pred),
  )
}

///|
fn ncmul2_star(x : Value, y : Value) -> Value raise {
  simplifya(list3(list1(q_mnctimes), x, y), Nil)
}

///|
fn contains_a_zero_replacement(form : Value) -> Value raise {
  let r = in_nth_power_radical(
    form,
    symval(q_d_radical_nilpotent_of_order),
  )
  if r.truthy() {
    return r
  }
  if atom(form) {
    let mut v = cdr(symval(q_d_dot_simplifications))
    while v is Cons(_) {
      if eql(Fix(0L), second(v)) && eq(car(v), form) {
        return t
      }
      v = cddr(v)
    }
    Nil
  } else {
    let mut v = cdr(symval(q_d_dot_simplifications))
    while v is Cons(_) {
      if eql(Fix(0L), second(v)) {
        let u = car(v)
        if atom(u) {
          if member_equal(u, form).truthy() {
            return t
          }
        } else if ordered_sublist(cdr(u), form).truthy() {
          return t
        }
      }
      v = cddr(v)
    }
    Nil
  }
}

///|
/// Returns t if (ncmuln form nil) would cause a replacement when
/// simplified (form is not a product).
fn contains_a_replacement(form : Value) -> Value raise {
  let mut tem1 = cdr(symval(q_d_dot_simplifications))
  if atom(form) {
    let mut i = 1
    for u in tem1.iter() {
      if i % 2 == 1 && eq(u, form) {
        return t
      }
      i += 1
    }
    Nil
  } else {
    while tem1.truthy() {
      let u = car(tem1)
      tem1 = cddr(tem1)
      if atom(u) {
        if member_equal(u, form).truthy() {
          return t
        }
      } else if ordered_sublist(cdr(u), form).truthy() {
        return t
      }
    }
    Nil
  }
}

///|
fn d_must_replacep(expression : Value) -> Value raise {
  let ptype = poly_type(expression)
  set(q_ear_already_found, Nil) |> ignore
  let mut poly : Value = Nil
  if eq(ptype, q_kw_rational_function) {
    poly = num(expression)
  } else if eq(ptype, q_kw_polynomial) {
    poly = expression
  } else if eq(ptype, polybas__kw_drat) {
    if symval(q_d_new_fast_dotsimp).truthy() {
      poly = num(cdr(expression))
    }
  }
  if poly.truthy() {
    if numberp(poly) {
      Nil
    } else {
      while poly.truthy() {
        if d_must_replacep(get(car(poly), q_disrep)).truthy() {
          return t
        }
        poly = fifth(poly)
        if numberp(poly) {
          return Nil
        }
      }
      Nil
    }
  } else if d_ratp(expression).truthy() {
    if memq(caadr(expression), symval(q_ear_genvar)).truthy() {
      d_must_replacep(cadr(expression))
    } else {
      fsignal(
        list1(
          Str(
            "this cre form should not be here, since its leading monom is not in *genvar*",
          ),
        ),
      )
    }
  } else {
    catch_tag(q_must_replace, () => must_replacep1(expression))
  }
}

///|
fn must_replacep1_by_zero(expression : Value) -> Value raise {
  if symval(q_ear_already_found).truthy() {
    Nil
  } else if atom(expression) {
    if contains_a_zero_replacement(expression).truthy() {
      throw_tag(q_must_replace, t)
    } else {
      Nil
    }
  } else if atom(car(expression)) {
    must_replacep1_by_zero(cdr(expression))
  } else if eq(caar(expression), q_mnctimes) {
    if contains_a_zero_replacement(cdr(expression)).truthy() {
      set(q_ear_already_found, t) |> ignore
      throw_tag(q_must_replace, t)
    } else {
      Nil
    }
  } else {
    must_replacep1_by_zero(car(expression)) |> ignore
    must_replacep1_by_zero(cdr(expression))
  }
}

///|
fn must_replacep1(expression : Value) -> Value raise {
  if symval(q_ear_already_found).truthy() {
    Nil
  } else if atom(expression) {
    if contains_a_replacement(expression).truthy() {
      throw_tag(q_must_replace, t)
    } else {
      Nil
    }
  } else if atom(car(expression)) {
    must_replacep1(cdr(expression))
  } else if eq(caar(expression), q_mnctimes) {
    if contains_a_replacement(cdr(expression)).truthy() {
      set(q_ear_already_found, t) |> ignore
      throw_tag(q_must_replace, t)
    } else {
      Nil
    }
  } else {
    must_replacep1(car(expression)) |> ignore
    must_replacep1(cdr(expression))
  }
}

///|
fn remove_header(x : Value) -> Value raise {
  if numberp(x) {
    x
  } else {
    cdr(x)
  }
}

///|
fn new_rat_ncmul1(a : Value, b : Value, c : Value) -> Value raise {
  if numberp(b) {
    let tem = ncmul_star(list3(a, b, c))
    if d_zerop(tem).truthy() {
      Fix(0L)
    } else {
      new_rat(tem)
    }
  } else if affine_polynomialp(b).truthy() {
    poly_ncmul1(a, b, c)
  } else if rational_functionp(b).truthy() {
    cons(poly_ncmul1(a, num(b), c), denom(b))
  } else if d_ratp(b).truthy() {
    new_rat_ncmul1(a, cdr(b), c)
  } else {
    new_rat_ncmul(list3(a, new_rat(b), c))
  }
}

///|
fn two_times_n(n : Value) -> Value raise {
  if num_gt(n, Fix(4L)) {
    num_mul(Fix(2L), n)
  } else {
    Fix(0L)
  }
}

///|
fn rank_dimension_three_modulo_cubic(n : Value) -> Value raise {
  if num_lt(n, Fix(4L)) {
    Fix(0L)
  } else {
    num_sub(
      rank_dimension_three(n),
      rank_dimension_three(num_sub(n, Fix(3L))),
    )
  }
}

///|
fn rank_1_1_1_9(n : Value) -> Value raise {
  if num_lt(n, Fix(9L)) {
    polynomial_ring_1_1_1(n)
  } else {
    num_sub(num_mul(n, Fix(9L)), Fix(27L))
  }
}

///|
/// Reads a Lisp form from the standard input (`(read)`).
fn polyb__read() -> Value raise {
  match read_line(stream=symval(standard_input)) {
    Some(s) => lread(s)
    None => raise LispError::SimpleError("end of file on *STANDARD-INPUT*")
  }
}

///|
fn d_check_overlaps(
  up_to_degree : Value,
  add_to_simps? : Value = Nil,
  maybe_reset? : Value = t,
  from_degree? : Value = Nil,
) -> Value raise {
  let mut up_to_degree = up_to_degree
  let mut reset_monomials : Value = Nil
  if symval(q_ear_previously_checked_pairs) is Nil {
    set(q_ear_previously_checked_pairs, make_hash_table(kind=Equal)) |> ignore
  }
  if maybe_reset.truthy() {
    if amacros__y_or_n_p("Reset *previously-checked-pairs* ?") {
      if symval(q_ear_previously_checked_pairs) is Nil {
        set(q_ear_previously_checked_pairs, make_hash_table(kind=Equal))
        |> ignore
      }
      clrhash(symval(q_ear_previously_checked_pairs)) |> ignore
    }
    if amacros__y_or_n_p("use Hilbert for rank function") {
      // (user-supply list-of-degrees-to-mod-out)
      let list_of_degrees_to_mod_out = user_supply1(
        sym("list-of-degrees-to-mod-out"),
        Nil,
      )
      set(q_d_rank_function, hilbert_modulo(list_of_degrees_to_mod_out))
      |> ignore
    } else if amacros__y_or_n_p("Set the $Rank_function to a non nil value?") {
      let mut chosen = false
      for v in symval(q_ear_all_rank_functions).iter() {
        format(t, "~%Use ~A ?", [v]) |> ignore
        if amacros__y_or_n_p("") {
          set(q_d_rank_function, v) |> ignore
          chosen = true
          break
        }
      }
      if !chosen {
        format(t, "~%Enter a value for $rank_function:", []) |> ignore
        set(q_d_rank_function, polyb__read()) |> ignore
      }
    } else {
      set(q_d_rank_function, Nil) |> ignore
    }
    format(t, "~%~%The current variables are:", []) |> ignore
    displa(symval(q_d_current_variables)) |> ignore
    if !amacros__y_or_n_p("Keep the current variables?") {
      reset_monomials = t
      format(t, "~%Enter a Macsyma list:", []) |> ignore
      set(
        q_d_current_variables,
        mread_noprompt(list1(symval(standard_input))),
      )
      |> ignore
    }
  } else {
    format(
      t,
      "\n~%Starting to check overlaps without resetting *previously-checked-pairs*",
      [],
    )
    |> ignore
  }
  amacros__show("$RANK_FUNCTION", symval(q_d_rank_function))
  let to_replace = Collector::new()
  let mut i = 0
  for mon in symval(q_d_dot_simplifications).iter() {
    if i % 2 == 1 && !atom(mon) {
      to_replace.add(mon)
    }
    i += 1
  }
  let to_replace = to_replace.result()
  let mut the_min : Value = Nil
  let mut the_max : Value = Nil
  for mon in to_replace.iter() {
    let deg = d_nc_degree(mon)
    if the_min is Nil || num_lt(deg, the_min) {
      the_min = deg
    }
    if the_max is Nil || num_gt(deg, the_max) {
      the_max = deg
    }
  }
  if the_min is Nil {
    the_min = Fix(0L)
  }
  if the_max is Nil {
    the_max = Fix(0L)
  }
  let mut lowest_degree = the_min
  if !numberp(up_to_degree) {
    up_to_degree = num_sub(num_mul(Fix(2L), the_max), Fix(1L))
  }
  if from_degree.truthy() {
    lowest_degree = from_degree
  }
  // (loop named angela while (<= deg up-to-degree)
  //       for deg from (1+ lowest-degree) to up-to-degree do ...)
  let mut deg = num_add(lowest_degree, Fix(1L))
  let table = symval(q_ear_previously_checked_pairs)
  if num_le(deg, up_to_degree) {
    while true {
      if symval(q_d_rank_function).truthy() {
        format(t, "~%current variables are", []) |> ignore
        displa(symval(q_d_current_variables)) |> ignore
        while num_lt(deg, num_add(up_to_degree, Fix(1L))) {
          let dim = length(
              d_mono(symval(q_d_current_variables), deg, reset=reset_monomials),
            ) -
            1
          format(
            t,
            "~%There are ~A independent monomials in degree ~A and rank function is ~A",
            [int(dim), deg, funcall(symval(q_d_rank_function), [deg])],
          )
          |> ignore
          if num_le(int(dim), funcall(symval(q_d_rank_function), [deg])) {
            lowest_degree = num_min(up_to_degree, deg)
            deg = num_add(deg, Fix(1L))
          } else {
            break
          }
        }
      }
      if num_le(deg, up_to_degree) {
        for right1 in to_replace.iter() {
          let bef_overlap = num_sub(deg, d_nc_degree(right1))
          for left in to_replace.iter() {
            // (loop while (< deg-so-far bef-overlap) for v in (cdr left)
            //       for ii from 2 summing ($nc_degree v) into deg-so-far do ...)
            let mut deg_so_far : Value = Fix(0L)
            let mut vs = cdr(left)
            let mut ii = 2
            while num_lt(deg_so_far, bef_overlap) && vs is Cons(_) {
              deg_so_far = num_add(deg_so_far, d_nc_degree(car(vs)))
              if num_eq(deg_so_far, bef_overlap) {
                let tem2 = nthcdr(ii, left)
                if tem2.truthy() && initial_equal(tem2, cdr(right1)).truthy() {
                  let tem = nthcdr(length(left) - ii, cdr(right1))
                  let test_list = append(cddr(left), tem)
                  if contains_a_replacement(cddr(butlast(test_list))).truthy() ||
                    ordered_pair_in_list(left, right1, table).truthy() {
                    ()
                  } else {
                    sethash(list2(left, right1), table, t) |> ignore
                    let assoc_list = list3(
                      ncmuln(cdr(subseq(left, 0, end=ii)), t),
                      ncmuln(nthcdr(ii, left), t),
                      ncmuln(tem, t),
                    )
                    format(t, "~%Checking the overlap for", []) |> ignore
                    displa(list3(list2(q_mlist, q_simp), left, right1)) |> ignore
                    let tem1 = d_check_associative(
                      first(assoc_list),
                      second(assoc_list),
                      third(assoc_list),
                    )
                    if d_zerop(tem1).truthy() {
                      format(t, "~%The overlap was associative.", []) |> ignore
                    } else {
                      format(t, "~%The overlap was not associative.", [])
                      |> ignore
                      displa(cons(list2(q_mlist, q_simp), assoc_list)) |> ignore
                      if add_to_simps.truthy() {
                        convert_relation_to_dot_simp(tem1) |> ignore
                      }
                      if symval(q_d_fast_dotsimp).truthy() {
                        d_rat_the_dot_simplifications() |> ignore
                      }
                      d_check_overlaps(
                        up_to_degree,
                        add_to_simps~,
                        maybe_reset=Nil,
                        from_degree=lowest_degree,
                      )
                      |> ignore
                      return symval(q_d_dot_simplifications)
                    }
                  }
                }
              }
              vs = cdr(vs)
              ii += 1
            }
          }
        }
      }
      if !num_le(deg, up_to_degree) {
        break
      }
      deg = num_add(deg, Fix(1L))
      if num_gt(deg, up_to_degree) {
        break
      }
    }
  }
  symval(q_d_dot_simplifications)
}

///|
fn rank_dimension_three(n : Value) -> Value raise {
  if oddp(n) {
    div_star(
      num_mul(num_add(n, Fix(1L)), num_add(n, Fix(3L))),
      Fix(4L),
    )
  } else {
    div_star(
      num_mul(num_add(Fix(2L), n), num_add(Fix(2L), n)),
      Fix(4L),
    )
  }
}

///|
fn ordered_pair_in_list(a : Value, b : Value, a_list_of_pairs : Value) -> Value raise {
  let lis = symval(q_ear_temp_pair)
  setf_car(lis, a) |> ignore
  setf_car(cdr(lis), b) |> ignore
  gethash(lis, a_list_of_pairs)
}

///|
/// The SPSAFE macro: reports whether the symbols LL are special.
fn spsafe(ll : Value) -> Value raise {
  for u in ll.iter() {
    if get(u, q_special).truthy() {
      format(t, "~%Warning: ~A is a special", [u]) |> ignore
    } else {
      format(t, "~%~A is not special", [u]) |> ignore
    }
  }
  Nil
}

///|
fn d_set_up_dot_simplifications(
  relations : Value,
  check_thru_deg? : Value = Nil,
  ordering? : Value,
) -> Value raise {
  let ordering = match ordering {
    Some(o) => o
    None => symval(q_d_order_function)
  }
  set(q_d_dot_simplifications, list1(list2(q_mlist, q_simp))) |> ignore
  amacros__show("$ORDER_FUNCTION", symval(q_d_order_function))
  let mut relations = meval_star(relations)
  if d_listp(relations).truthy() {
    relations = cdr(relations)
  }
  for relat in relations.iter() {
    convert_relation_to_dot_simp(relat, ordering~) |> ignore
  }
  format(t, "~%The new dot simplifications are set up", []) |> ignore
  if check_thru_deg.truthy() {
    displa(symval(q_d_dot_simplifications)) |> ignore
    d_check_overlaps(check_thru_deg, add_to_simps=t) |> ignore
  }
  symval(q_d_dot_simplifications)
}

///|
fn convert_relation_to_dot_simp(relat : Value, ordering? : Value) -> Value raise {
  ignore(ordering)
  if symval(q_d_fast_dotsimp) is Nil || symval(q_d_free_dot) is Nil {
    fsignal(list1(Str("old code"))) |> ignore
  }
  let mut relat = d_dotsimp(relat)
  if d_zerop(relat).truthy() {
    Nil
  } else {
    relat = cdr(relat)
    if consp(num(relat)) {
      let tem = third(num(relat))
      if consp(tem) {
        format(t, "~%Denom : ", []) |> ignore
        let tem1 = new_disrep(tem)
        displa(tem1) |> ignore
        if symval(q_d_all_dotsimp_denoms).truthy() {
          nconc(symval(q_d_all_dotsimp_denoms), list1(tem1)) |> ignore
        }
      }
    }
    let tem = make_simp(num(relat))
    d_add_to_simps(tem) |> ignore
    format(t, "~%Adding to simps: ", []) |> ignore
    displa(cons(list1(q_mlist), tem))
  }
}

///|
fn vadd_star(a_list : Value) -> Value raise {
  with_special(q_varlist, Nil, () => {
    if length(a_list) < 3 {
      add_star(a_list)
    } else {
      vadd_star(list2(car(a_list), vadd_star(cdr(a_list))))
    }
  })
}

///|
fn vmul_star(a_list : Value) -> Value raise {
  with_special(q_varlist, Nil, () => {
    if length(a_list) < 3 {
      mul_star(a_list)
    } else {
      vmul_star(list2(car(a_list), vmul_star(cdr(a_list))))
    }
  })
}

///|
fn vsub_star(a : Value, b : Value) -> Value raise {
  with_special(q_varlist, Nil, () => sub_star(a, b))
}

///|
/// "This needs to be fixed. It still allows ratdisrep"
fn vdiv_star(a : Value, b : Value) -> Value raise {
  with_special(q_varlist, Nil, () => {
    simplifya(list3(list1(q_mquotient), a, b), Nil)
  })
}

///|
fn vminus_star(a : Value) -> Value raise {
  with_special(q_varlist, Nil, () => {
    simplifya(list2(list1(q_mminus), a), Nil)
  })
}

///|
fn d_vrat(a_list : Value) -> Value raise {
  with_special(q_varlist, Nil, () => d_rat(car(a_list), cdr(a_list)))
}

///|
fn d_add_to_simps(a_list : Value, ordering? : Value) -> Value raise {
  let ordering = match ordering {
    Some(o) => o
    None => symval(q_d_order_function)
  }
  let mut a_list = a_list
  if d_listp(a_list).truthy() {
    a_list = cdr(a_list)
  }
  if zerop(symval(q_d_expop)) && symval(q_d_fast_dotsimp) is Nil {
    setf_car(cdr(a_list), d_multthru(second(a_list))) |> ignore
  }
  let ds = symval(q_d_dot_simplifications)
  let mut i = 0
  let mut inserted = false
  for u in ds.iter() {
    if i % 2 == 1 && funcall(ordering, [car(a_list), u]) is Nil {
      set(
        q_d_dot_simplifications,
        append(subseq(ds, 0, end=i), append(a_list, nthcdr(i, ds))),
      )
      |> ignore
      inserted = true
      break
    }
    i += 1
  }
  if !inserted {
    set(q_d_dot_simplifications, append(ds, a_list)) |> ignore
  }
  d_simplify_dot_simplifications(from_degree=d_nc_degree(car(a_list)))
}

///|
/// The $WITH_NO_SIMP macro: FORM (unevaluated) is evaluated with
/// $dot_simplifications bound to false.
fn d_with_no_simp(form : Value) -> Value raise {
  with_special(q_d_dot_simplifications, Nil, () => meval_star(form))
}

///|
/// The inverse of any number n modulo-p. Ok if n negative, but n=0 gives 0
/// and modulo-p not prime gives false answer.
fn d_inverse_modulo(n : Value, modulo_p : Value) -> Value raise {
  num_mod(expt(n, num_sub(modulo_p, Fix(2L))), modulo_p)
}

///|
fn d_nu(i : Value, llist : Value) -> Value raise {
  let p1 = int(length(llist))
  let fact = d_inverse_modulo(i, p1)
  let tem = Collector::new()
  let mut ii : Value = Fix(1L)
  while num_lt(ii, p1) {
    tem.add(nth(to_int(num_mod(num_mul(ii, fact), p1)), llist))
    amacros__show("TEM", tem.result())
    amacros__show("II", ii)
    ii = num_add(ii, Fix(1L))
  }
  cons(list2(q_mlist, q_simp), tem.result())
}

///|
fn d_phi(l : Value) -> Value raise {
  check_arg(l, q_d_listp, list1(Str("macsyma list"))) |> ignore
  let l = cdr(l)
  let p0 = length(l)
  amacros__show("P0", int(p0))
  let tem = Collector::new()
  for i in 1..<p0 {
    tem.add(
      mul_star(
        list2(
          nth(i, l),
          power(q_d_sig, num_mod(int(-i), int(p0))),
        ),
      ),
    )
  }
  let s1 = meval_star(cons(list1(q_mplus), tem.result()))
  let tem2 = Collector::new()
  for i in 1..<p0 {
    tem2.add(nth(i, l))
  }
  let s2 = meval_star(cons(list1(q_mplus), tem2.result()))
  add_star(
    list1(
      mul_star(list4(int(p0), s1, car(l), mul_star(list2(int(-p0), s2)))),
    ),
  )
}

///|
fn d_sig(n : Value, p0? : Value) -> Value raise {
  let p0 = match p0 {
    Some(p) => p
    None => symval(q_d_prime_order)
  }
  power(q_d_sig, num_mod(n, p0))
}

///|
fn d_nu_poly(i : Value, poly : Value) -> Value raise {
  d_ratsimp(
    subst(d_sig(i, p0=symval(q_d_prime_order)), q_d_sig, poly),
    Nil,
  )
}

///|
fn d_scalar_concat(l : Value) -> Value raise {
  let tem = d_concat(l)
  putprop(tem, list3(Nil, q_d_scalar, t), q_mprops) |> ignore
  tem
}

///|
fn d_rel(i : Value, j : Value) -> Value raise {
  let ii = num_max(i, j)
  let jj = num_min(i, j)
  let ans = if !equal(i, j) {
    list2(
      ncmul_star(
        list2(d_concat(list2(q_d_e, ii)), d_concat(list2(q_d_e, jj))),
      ),
      sub_star(
        d_scalar_concat(list3(q_d_a, jj, ii)),
        ncmul_star(
          list2(d_concat(list2(q_d_e, jj)), d_concat(list2(q_d_e, ii))),
        ),
      ),
    )
  } else {
    list2(
      ncmul_star(
        list2(d_concat(list2(q_d_e, ii)), d_concat(list2(q_d_e, jj))),
      ),
      d_scalar_concat(list3(q_d_a, jj, ii)),
    )
  }
  cons(list2(q_mlist, q_simp), ans)
}

///|
fn d_clifford_dot_simplifications(n : Value) -> Value raise {
  let tem = Collector::new()
  let mut i : Value = Fix(1L)
  while num_le(i, n) {
    let mut j : Value = Fix(1L)
    while num_le(j, i) {
      tem.append_list(copy_list(cdr(d_rel(i, j))))
      j = num_add(j, Fix(1L))
    }
    i = num_add(i, Fix(1L))
  }
  cons(list2(q_mlist, q_simp), tem.result())
}

///|
fn d_replacements() -> Value raise {
  let a_list = Collector::new()
  let mut tem = cdr(symval(q_d_dot_simplifications))
  while tem.truthy() {
    a_list.add(car(tem))
    tem = cddr(tem)
  }
  cons(list2(q_mlist, q_simp), a_list.result())
}

///|
fn d_earlier_mono(monom : Value, variables? : Value) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  let answer = d_mono(variables, d_nc_degree(monom))
  let tem = Collector::new()
  for v in cdr(answer).iter() {
    if funcall(symval(q_d_order_function), [v, monom]).truthy() {
      tem.add(v)
    }
  }
  let f = symval(q_d_order_function)
  cons(
    list2(q_mlist, q_simp),
    sort_list(tem.result(), (a, b) => funcall(f, [a, b]).truthy()),
  )
}

///|
/// polyb.lisp's PARSE-STRING (which replaces the one of stringproc's
/// eval_string.lisp in the function cell when the file is loaded).
fn polyb__parse_string(a_string : Value) -> Value raise {
  let mut s = lstring(a_string)
  if !(s.contains("$") || s.contains(";")) {
    s = s + "$"
  }
  let stream = make_string_input_stream(s)
  with_special(standard_input, stream, () => caddr(mread(list1(stream))))
}

///|
/// The MAC macro: parses a Macsyma string but does not call meval*.
fn mac(a_string : Value) -> Value raise {
  polyb__parse_string(a_string)
}

///|
/// The MAC-EVAL-AFTER macro: the form (meval* <parsed string>).
fn mac_eval_after(a_string : Value) -> Value raise {
  list2(q_meval_star, polyb__parse_string(a_string))
}

///|
/// The MAC-EVAL macro: reads a macsyma string and evaluates it.
fn mac_eval(a_string : Value) -> Value raise {
  meval_star(polyb__parse_string(a_string))
}

///|
fn d_hh(a : Value) -> Value raise {
  if atom(a) {
    Nil
  } else {
    lbool(equal(caar(a), q_mtimes))
  }
}

///|
fn d_monomial_dimensions(n : Value, order_weight? : Value = Nil) -> Value raise {
  if symval(q_d_current_variables).truthy() {
    format(t, "~%The current variables are", []) |> ignore
    displa(symval(q_d_current_variables)) |> ignore
    if !amacros__y_or_n_p("Use them?") {
      set(q_d_current_variables, Nil) |> ignore
    }
  }
  if symval(q_d_current_variables) is Nil {
    format(t, "~%Enter Macsyma list of variables to use:", []) |> ignore
    set(
      q_d_current_variables,
      caddr(mread_raw(symval(standard_input))),
    )
    |> ignore
  }
  if order_weight.truthy() {
    let mut tem : Value = Fix(0L)
    let mut j : Value = Fix(1L)
    while num_le(j, n) {
      let mut the_count = 0
      let mut i : Value = Fix(1L)
      while num_le(i, n) {
        for v in cdr(d_mono(symval(q_d_current_variables), i)).iter() {
          if eql(
              d_nc_degree(v, type_of_weight=amacros__q_kw_order_weight),
              j,
            ) {
            the_count += 1
          }
        }
        i = num_add(i, Fix(1L))
      }
      format(
        t,
        "~%There are ~A monomials of order weight ~A and of degree less than ~A",
        [int(the_count), j, n],
      )
      |> ignore
      tem = num_add(tem, int(the_count))
      j = num_add(j, Fix(1L))
    }
    format(
      t,
      "~%The total number of monomials of weight and degree less than ~A is ~A.",
      [n, num_add(tem, Fix(1L))],
    )
    |> ignore
  }
  let tem = Collector::new()
  let mut the_sum : Value = Fix(0L)
  let mut i : Value = Fix(1L)
  while num_le(i, n) {
    let j = int(length(cdr(d_mono(symval(q_d_current_variables), i))))
    format(t, "~%There are ~A independent monomials in degree ~A.", [j, i])
    |> ignore
    tem.add(list3(list1(q_mlist), i, j))
    the_sum = num_add(the_sum, j)
    i = num_add(i, Fix(1L))
  }
  format(
    t,
    "~%The sum of the dimensions from dimension 0 through dimension ~A is ~A",
    [n, num_add(the_sum, Fix(1L))],
  )
  |> ignore
  cons(list2(q_mlist, q_simp), tem.result())
}

///|
fn d_mono_weighted(n : Value) -> Value raise {
  let mut the_list : Value = Nil
  let mut i : Value = Fix(1L)
  while num_le(i, n) {
    for v in cdr(d_mono(symval(q_d_current_variables), i)).iter() {
      if eql(d_nc_degree(v, type_of_weight=amacros__q_kw_order_weight), n) {
        the_list = cons(v, the_list)
      }
    }
    i = num_add(i, Fix(1L))
  }
  cons(list1(q_mlist), the_list)
}

///|
/// The SUBSCRIPT macro: `((d :array) i)`.
fn subscript(d : Value, i : Value) -> Value raise {
  list2(list2(d, q_kw_array), i)
}

///|
fn d_find_relations_among(
  a_list : Value,
  dotsimp_first? : Value = Nil,
  term_names? : Value = Nil,
) -> Value raise {
  check_arg(a_list, q_d_listp, list1(Str("macsyma list"))) |> ignore
  let mut a_list = a_list
  let mut term_names = term_names
  if dotsimp_first.truthy() {
    a_list = cons(list1(q_mlist), mapcar(v => d_dotsimp(v), cdr(a_list)))
  }
  let mut gen_sum = d_general_sum(a_list, coefficients=symval(q_d_aaaa)).0
  if dotsimp_first is Nil {
    gen_sum = d_dotsimp(gen_sum)
  }
  let eqns = d_nc_coefficients(
    d_ratsimp(list2(list1(q_mlist), gen_sum), Nil),
  )
  set(q_d_last_equations, eqns) |> ignore
  let answers = d_fast_linsolve(second(eqns), variables=third(eqns))
  set(q_d_last_solutions, answers) |> ignore
  if term_names is Nil {
    let tem = Collector::new()
    for i in 1..=length(cdr(a_list)) {
      tem.add(d_concat(list2(q_d_term, int(i))))
    }
    term_names = cons(list1(q_mlist), tem.result())
  }
  d_sublis(
    answers,
    d_general_sum(term_names, coefficients=symval(q_d_aaaa)).0,
  )
}

///|
fn d_check_skew_relations(variables? : Value) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  let mut answer : Value = Nil
  for u in cdr(variables).iter() {
    if d_must_replacep(u).truthy() {
      continue
    }
    for v in cdr(variables).iter() {
      if funcall(symval(q_d_order_function), [u, v]).truthy() && !equal(u, v) {
        let tem = ncmul_star(list2(v, u))
        if d_must_replacep(tem).truthy() {
          ()
        } else {
          format(t, "~%no replacement for ~A", [tem]) |> ignore
          answer = cons(tem, answer)
        }
      }
    }
  }
  if answer is Nil {
    t
  } else {
    // (cons '(mlist) answer) is computed in the FINALLY clause but not
    // returned, so the loop returns NIL.
    Nil
  }
}

///|
fn get_alt(item : Value, a_list : Value) -> Value raise {
  let mut a_list = a_list
  while a_list.truthy() {
    if equal(item, car(a_list)) {
      return second(a_list)
    } else {
      a_list = cddr(a_list)
    }
  }
  Nil
}

///|
fn d_collect_skew_relations(variables? : Value) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  let a_list = Collector::new()
  for u in cdr(variables).iter() {
    if d_must_replacep(u).truthy() {
      continue
    }
    for v in cdr(variables).iter() {
      if funcall(symval(q_d_order_function), [u, v]).truthy() && !equal(u, v) {
        let tem = ncmul_star(list2(v, u))
        let tem2 = get_alt(tem, cdr(symval(q_d_dot_simplifications)))
        if tem2.truthy() {
          a_list.add(tem)
          a_list.add(tem2)
        }
      }
    }
  }
  cons(list2(q_mlist, q_simp), a_list.result())
}

///|
fn d_relations_from_dot_simps(dot_simps? : Value) -> Value raise {
  let dot_simps = match dot_simps {
    Some(v) => v
    None => symval(q_d_dot_simplifications)
  }
  let mut a_list = cdr(dot_simps)
  let tem = Collector::new()
  while a_list.truthy() {
    tem.add(sub_star(first(a_list), d_totaldisrep(second(a_list))))
    a_list = cddr(a_list)
  }
  cons(list1(q_mlist), tem.result())
}

///|
fn repl_deg() -> Value raise {
  sort_list(
    mapcar(x => d_nc_degree(x), cdr(d_replacements())),
    (a, b) => alphalessp(a, b).truthy(),
  )
}

///|
fn d_pb(n : Value) -> Value raise {
  mfuncall(q_d_playback, list1(list3(list1(q_mlist), n, Fix(1000L))))
}

///|
fn d_find_central_thru_deg(begin : Value, to_n : Value) -> Value raise {
  displa(symval(q_d_current_variables)) |> ignore
  set(q_d_centrals_so_far, Nil) |> ignore
  let mut i = begin
  while num_le(i, to_n) {
    d_check_overlaps(
      num_add(i, Fix(1L)),
      add_to_simps=t,
      maybe_reset=Nil,
      from_degree=i,
    )
    |> ignore
    let tem = mfuncall(
      q_d_central_elements,
      list2(symval(q_d_current_variables), i),
    )
    set(
      q_d_centrals_so_far,
      cons(list3(list1(q_mlist), i, tem), cdr(symval(q_d_centrals_so_far))),
    )
    |> ignore
    // (maclist $centrals_so_far)
    set(q_d_centrals_so_far, maclist(symval(q_d_centrals_so_far))) |> ignore
    format(t, "~%Central in degree ~A ", [i]) |> ignore
    displa(tem) |> ignore
    i = num_add(i, Fix(1L))
  }
  symval(q_d_centrals_so_far)
}

///|
/// The MACLIST macro, which sets X to (cons '(mlist) x): the new value.
fn maclist(x : Value) -> Value raise {
  cons(list1(q_mlist), x)
}

///|
fn rat_variable_info(cre_form : Value) -> Value raise {
  car(cre_form)
}

///|
fn fast_scalarp(x : Value) -> Value raise {
  if atom(x) {
    if numberp(x) {
      t
    } else if symbolp(x) {
      mget(x, q_d_scalar)
    } else {
      d_scalarp(x)
    }
  } else {
    let op = caar(x)
    if eq(op, q_mnctimes) {
      Nil
    } else if eq(op, q_mrat) {
      let gen_vars = fourth(rat_variable_info(x))
      for vv in gen_vars.iter() {
        if fast_scalarp(get(vv, q_disrep)) is Nil {
          if appears_in(cdr(x), vv).truthy() {
            return Nil
          }
        }
      }
      t
    } else {
      d_scalarp(x)
    }
  }
}

///|
fn my_ratcoeff(expr : Value, monom : Value, deg? : Value = Fix(1L)) -> Value raise {
  let answer = catch_tag(q_bad_variable_order, () => {
    if atom(expr) {
      if eq(expr, monom) {
        Fix(1L)
      } else {
        Fix(0L)
      }
    } else if equal(caar(expr), q_mrat) && eq(second(car(expr)), q_simp) {
      my_ratcoeff1(expr, monom, deg~)
    } else {
      d_ratcoef(expr, monom)
    }
  })
  if eq(answer, q_bad_order) {
    format(t, "~%Variable ~A is out of order so using $ratcoef.", [monom])
    |> ignore
    d_ratcoef(expr, monom, n=deg)
  } else {
    answer
  }
}

///|
fn my_ratcoeff1(expr : Value, monom : Value, deg? : Value = Fix(1L)) -> Value raise {
  let mut v = varlist(expr)
  let mut w = genvar(expr)
  while v is Cons(_) && w is Cons(_) {
    if equal(car(v), monom) {
      if appears_in(num(cdr(expr)), car(w)) is Nil {
        return Fix(0L)
      } else {
        return cons(
          rat_variable_info(expr),
          cons(my_ratcoeff2(num(cdr(expr)), car(w), deg~), denom(cdr(expr))),
        )
      }
    }
    v = cdr(v)
    w = cdr(w)
  }
  Fix(0L)
}

///|
fn my_ratcoeff2(rat_expr : Value, gen_var : Value, deg? : Value = Fix(1L)) -> Value raise {
  if atom(rat_expr) {
    return rzero()
  }
  let mut rat_num = rat_expr
  if eq(car(rat_num), gen_var) {
    rat_num = cdr(rat_num)
    while rat_num.truthy() {
      if eql(car(rat_num), deg) {
        return second(rat_num)
      }
      if eql(car(rat_num), Fix(0L)) {
        return my_ratcoeff2(second(rat_expr), gen_var)
      } else {
        rat_num = cddr(rat_num)
      }
    }
    Nil
  } else {
    rat_num = cdr(rat_num)
    while rat_num.truthy() {
      if eql(car(rat_num), Fix(0L)) {
        return my_ratcoeff2(second(rat_num), gen_var)
      } else if appears_in(cadr(rat_num), gen_var).truthy() {
        throw_tag(q_bad_variable_order, q_bad_order) |> ignore
      } else {
        rat_num = cddr(rat_num)
      }
    }
    Nil
  }
}

///|
fn d_denominator(expr : Value) -> Value raise {
  if d_ratp(expr).truthy() {
    cons(car(expr), cons(cddr(expr), Fix(1L)))
  } else if equal(caar(expr), q_mtimes) {
    let tem = Collector::new()
    for v in cdr(expr).iter() {
      if !atom(v) && equal(caar(v), q_mexpt) && num_lt(third(v), Fix(0L)) {
        let tem1 = copy_list(v)
        setf_car(cddr(tem1), num_neg(third(v))) |> ignore
        tem.add(tem1)
      }
    }
    simplifya(cons(list1(q_mtimes), tem.result()), Nil)
  } else {
    d_denominator(d_vrat(list1(expr)))
  }
}

///|
fn variables_same_divide(f : Value, g : Value) -> Value raise {
  vdiv_star(f, g)
}

///|
/// Divides top and bottom of a cre expression by their gcd.
fn simplify_rational_quotient(expr : Value) -> Value raise {
  check_arg(expr, q_d_ratp, list1(Str("Cre form"))) |> ignore
  let mut the_num = d_numerator(expr)
  let mut the_denom = d_denominator(expr)
  if equal(cdr(the_denom), cons(Fix(1L), Fix(1L))) {
    expr
  } else {
    let the_gcd = d_gcd(the_num, the_denom, Nil)
    the_num = variables_same_divide(the_num, the_gcd)
    the_denom = variables_same_divide(the_denom, the_gcd)
    append(list2(car(expr), num(cdr(the_num))), num(cdr(the_denom)))
  }
}

///|
fn two(x : Value) -> Value raise {
  ignore(x)
  Fix(2L)
}

///|
fn d_check_skew3_conditions(relations : Value) -> Value raise {
  with_special(q_d_expop, Fix(100L), () => {
    let relations = list3(
      list1(q_mlist),
      div_star(
        nth(1, relations),
        d_coeff(nth(1, relations), ncmul_star(list3(q_d_y, q_d_x, q_d_x))),
      ),
      div_star(
        nth(2, relations),
        d_coeff(nth(2, relations), ncmul_star(list3(q_d_y, q_d_y, q_d_x))),
      ),
    )
    displa(relations) |> ignore
    with_special(q_d_dot_simplifications, Nil, () => {
      let mut result = true
      let monoms3 = d_mono(list3(list1(q_mlist), q_d_x, q_d_y), Fix(3L))
      let tem = Collector::new()
      let mut relat = cdr(relations)
      let mut coeff_names = list2(symval(q_d_bbbb), symval(q_d_cccc))
      while relat is Cons(_) && coeff_names is Cons(_) {
        let mut j = 1
        for u in cdr(monoms3).iter() {
          tem.add(
            list3(
              list1(q_mequal),
              nth(j, car(coeff_names)),
              d_coeff(car(relat), u),
            ),
          )
          j += 1
        }
        relat = cdr(relat)
        coeff_names = cdr(coeff_names)
      }
      let coeff_values = cons(list1(q_mlist), tem.result())
      let answer = d_sublis(coeff_values, symval(q_d_skew3_conditions))
      for v in cdr(answer).iter() {
        if d_zerop(sub_star(nth(1, v), nth(2, v))) is Nil {
          format(t, "~%Inconsistent condition ", []) |> ignore
          displa(v) |> ignore
          result = false
        }
      }
      if !result {
        format(t, "~%Trying to interchange f and g...", []) |> ignore
        d_check_skew3_conditions(
          list2(list1(q_mlist), reverse(cdr(relations))),
        )
      } else {
        t
      }
    })
  })
}

///|
fn d_list_variables(expr : Value, key_strings : Value) -> Value raise {
  if key_strings is Nil {
    return d_listofvars(expr)
  }
  let key_strings = mapcar(v => Str(string_trim("&", lstring(v))), key_strings)
  let mut tem = d_listofvars(expr)
  for v in list_to_array(cdr(tem)) {
    let string_v = string_upcase(lstring(string(v)))
    let mut found = false
    for key in key_strings.iter() {
      if string_search(string_upcase(lstring(key)), string_v) >= 0 {
        found = true
        break
      }
    }
    if !found {
      tem = polyc__delete_equal(v, tem)
    }
  }
  tem
}

///|
/// Replaces the parameters ("par") of F by unused $aaaa variables
/// (the inner loop of $socle, $fast_normal_elements and
/// $fast_central_elements). Returns (f, unknowns).
fn polyb__replace_parameters(f : Value) -> (Value, Value) raise {
  let mut f = f
  let mut unknowns = d_list_variables(f, list2(Str("aa"), Str("par")))
  let parameters = Collector::new()
  for vv in cdr(unknowns).iter() {
    if string_search("PAR", string_upcase(lstring(string(vv)))) >= 0 {
      parameters.add(vv)
    }
  }
  let mut tem1 = cdr(symval(q_d_aaaa))
  for vv in parameters.result().iter() {
    while tem1.truthy() {
      if memq(car(tem1), unknowns) is Nil {
        f = subst(car(tem1), vv, f)
        unknowns = subst(car(tem1), vv, unknowns)
        format(t, "~%Replacing ~A by ~A in f.", [vv, car(tem1)]) |> ignore
        tem1 = cdr(tem1)
        break
      }
      tem1 = cdr(tem1)
    }
  }
  (f, unknowns)
}

///|
fn d_socle(variables : Value, deg : Value) -> Value raise {
  let f_ = symval(q_d_order_function)
  let variables = cons(
    list1(q_mlist),
    sort_list(cdr(variables), (a, b) => funcall(f_, [a, b]).truthy()),
  )
  let monoms = d_mono(variables, deg)
  let monoms_higher = d_mono(variables, num_add(deg, Fix(1L)))
  let mut f = d_general_sum(monoms, coefficients=symval(q_d_aaaa)).0
  for v in cdr(variables).iter() {
    let (f1, unknowns) = polyb__replace_parameters(f)
    f = f1
    let tem1 = list3(
      list1(q_mlist),
      ncmul_star(list2(f, v)),
      ncmul_star(list2(v, f)),
    )
    let eqns = d_extract_linear_equations(
      tem1,
      independent_monomials=monoms_higher,
    )
    amacros__show("UNKNOWNS", unknowns)
    let answer = d_fast_linsolve(eqns, variables=unknowns)
    f = meval_star(d_sublis(answer, f))
    displa(f) |> ignore
  }
  f
}

///|
/// Returns elements F in degree DEG in variables, which satisfy
/// u.F=F.phi(u) where phi is the auto which defaults to the identity and
/// can be specified by the list of images of VARIABLES.
fn d_fast_normal_elements(
  deg : Value,
  variables? : Value,
  up_to_deg? : Value = Nil,
  auto? : Value = Nil,
) -> Value raise {
  let mut variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  let mut auto = auto
  if auto is Nil {
    auto = variables
  }
  // (pairlis keys data) in SBCL returns the pairs in reverse order.
  let mut pairs : Value = Nil
  let mut ks = cdr(variables)
  let mut ds = cdr(auto)
  while ks is Cons(_) && ds is Cons(_) {
    pairs = cons(cons(car(ks), car(ds)), pairs)
    ks = cdr(ks)
    ds = cdr(ds)
  }
  // (sort ... #'$order_function :key #'car): the function $ORDER_FUNCTION
  let tem = sort_list(pairs, (a, b) => {
    funcall(q_d_order_function, [car(a), car(b)]).truthy()
  })
  variables = cons(list1(q_mlist), mapcar(x => car(x), tem))
  auto = cons(list1(q_mlist), mapcar(x => cdr(x), tem))
  set(q_d_commutators, Nil) |> ignore
  set(q_d_centralizers, Nil) |> ignore
  let monoms = if up_to_deg.truthy() {
    let c = Collector::new()
    let mut i : Value = Fix(1L)
    while num_le(i, deg) {
      c.append_list(copy_list(cdr(d_mono(variables, i))))
      i = num_add(i, Fix(1L))
    }
    cons(list1(q_mlist), c.result())
  } else {
    d_mono(variables, deg)
  }
  let mut f = d_general_sum(monoms, coefficients=symval(q_d_aaaa)).0
  let mut v = cdr(variables)
  let mut im = cdr(auto)
  while v is Cons(_) && im is Cons(_) {
    let (f1, unknowns) = polyb__replace_parameters(f)
    f = f1
    let tem1 = list2(
      list1(q_mlist),
      d_totaldisrep(
        d_dotsimp(
          sub_star(
            ncmul_star(list2(car(v), f)),
            ncmul_star(list2(f, car(im))),
          ),
        ),
      ),
    )
    set(
      q_d_commutators,
      append(
        list3(list1(q_mlist), car(v), second(tem1)),
        cdr(symval(q_d_commutators)),
      ),
    )
    |> ignore
    let eqns = d_extract_linear_equations(
      tem1,
      independent_monomials=d_list_nc_monomials(tem1),
    )
    amacros__show("UNKNOWNS", unknowns)
    let answer = d_fast_linsolve(eqns, variables=unknowns)
    f = d_ratsimp(d_sublis(answer, f), Nil)
    set(
      q_d_centralizers,
      append(
        list3(list1(q_mlist), car(v), f),
        cdr(symval(q_d_centralizers)),
      ),
    )
    |> ignore
    displa(f) |> ignore
    v = cdr(v)
    im = cdr(im)
  }
  d_separate_parameters(f, Nil)
}

///|
fn d_fast_central_elements(variables : Value, deg : Value) -> Value raise {
  let f_ = symval(q_d_order_function)
  let variables = cons(
    list1(q_mlist),
    sort_list(cdr(variables), (a, b) => funcall(f_, [a, b]).truthy()),
  )
  set(q_d_commutators, Nil) |> ignore
  set(q_d_centralizers, Nil) |> ignore
  let monoms = d_mono(variables, deg)
  let mut f = d_general_sum(monoms, coefficients=symval(q_d_aaaa)).0
  for v in cdr(variables).iter() {
    let (f1, unknowns) = polyb__replace_parameters(f)
    f = f1
    let tem1 = list2(list1(q_mlist), d_com(f, v))
    set(
      q_d_commutators,
      append(
        list3(list1(q_mlist), v, second(tem1)),
        cdr(symval(q_d_commutators)),
      ),
    )
    |> ignore
    let eqns = d_extract_linear_equations(
      tem1,
      independent_monomials=d_list_nc_monomials(tem1),
    )
    amacros__show("UNKNOWNS", unknowns)
    let answer = d_fast_linsolve(eqns, variables=unknowns)
    f = d_ratsimp(d_sublis(answer, f), Nil)
    set(
      q_d_centralizers,
      append(list3(list1(q_mlist), v, f), cdr(symval(q_d_centralizers))),
    )
    |> ignore
    displa(f) |> ignore
  }
  d_separate_parameters(f, Nil)
}

///|
fn d_central_elements_in_degrees(degrees : Value) -> Value raise {
  with_special(q_d_centrals_so_far, Nil, () => {
    for i in degrees.iter() {
      d_check_overlaps(num_add(i, Fix(1L)), add_to_simps=t, maybe_reset=Nil)
      |> ignore
      set(
        q_d_centrals_so_far,
        cons(
          d_fast_central_elements(symval(q_d_current_variables), i),
          symval(q_d_centrals_so_far),
        ),
      )
      |> ignore
      mapcar(x => displa(x), symval(q_d_centrals_so_far)) |> ignore
    }
    cons(list1(q_mlist), symval(q_d_centrals_so_far))
  })
}

///|
fn d_pbi(n : Value) -> Value raise {
  with_special(q_linel, num_sub(symval(q_linel), Fix(10L)), () => {
    let mut i = n
    while num_lt(i, symval(q_d_linenum)) {
      let tem = d_concat(list2(q_d_c, i))
      format(t, "~% ~4A: ~A", [
        Str(string_trim("$", invert_case(lstring(string(tem))))),
        string_grind(meval_star(tem)),
      ])
      |> ignore
      i = num_add(i, Fix(1L))
    }
    Nil
  })
}

///|
fn new_concat(a : Value, b : Value) -> Value raise {
  let me = b.iter().map(v => format_to_string("~A", [v]) catch { _ => "" }).fold(init="", (x, y) => x + y)
  Value::Sym(intern(format_to_string("~A~A", [a, Str(me)])))
}

///|
fn d_list_sublis(a_list : Value, b_list : Value, expr : Value) -> Value raise {
  let mut a_list = a_list
  let mut b_list = b_list
  if d_listp(a_list).truthy() {
    a_list = cdr(a_list)
  }
  if d_listp(b_list).truthy() {
    b_list = cdr(b_list)
  }
  let tem = Collector::new()
  while a_list is Cons(_) && b_list is Cons(_) {
    tem.add(cons(car(a_list), car(b_list)))
    a_list = cdr(a_list)
    b_list = cdr(b_list)
  }
  sublis(tem.result(), expr)
}

///|
fn string_grind(
  x : Value,
  d_display2d? : Value = Nil,
  stream? : Value = Nil,
) -> Value raise {
  let answ = with_special(q_d_display2d, d_display2d, () => {
    with_output_to_string(st => {
      if symval(q_d_display2d) is Nil {
        mgrind(x, st) |> ignore
      } else {
        with_special(standard_output, st, () => displa(x)) |> ignore
      }
    })
  })
  let answ = string_trim("\n $", answ)
  if stream.truthy() {
    format(stream, "~A", [Str(answ)])
  } else {
    Str(answ)
  }
}

///|
/// Acceptable to displa.
fn macsyma_typep(x : Value) -> Value raise {
  if numberp(x) {
    t
  } else if consp(x) && consp(car(x)) {
    get(caar(x), q_dimension)
  } else {
    Nil
  }
}

///|
fn fsh(x : Value, stream? : Value) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_output)
  }
  with_special(q_d_display2d, Nil, () => {
    if macsyma_typep(x).truthy() {
      string_grind(x, stream~)
    } else if affine_polynomialp(x).truthy() || rational_functionp(x).truthy() {
      string_grind(header_poly(x), stream~)
    } else if listp(x) &&
      (affine_polynomialp(car(x)).truthy() ||
      rational_functionp(car(x)).truthy()) {
      match length(x) {
        // (fsh x stream) on the same one-element list recurses forever.
        1 => raise LispError::SimpleError("Control stack exhausted")
        2 => {
          fsh(first(x), stream~) |> ignore
          format(stream, " and ", []) |> ignore
          fsh(second(x), stream~)
        }
        _ => {
          let n = length(x)
          let mut i = 1
          let mut v = x
          while v is Cons(_) && i < n {
            fsh(car(v), stream~) |> ignore
            format(stream, ",", []) |> ignore
            v = cdr(v)
            i += 1
          }
          format(stream, " and ", []) |> ignore
          fsh(car(last(x)), stream~)
        }
      }
    } else if listp(x) && macsyma_typep(car(x)).truthy() {
      format(stream, "(", []) |> ignore
      for v in x.iter() {
        fsh(v) |> ignore
        format(t, " ", []) |> ignore
      }
      format(t, ")", [])
    } else {
      des(x)
    }
  })
}

///|
fn init_share_polyb() -> Unit raise {
  defvar_init(q_ear_temp_pair, list2(Nil, Nil))
  defvar_init(q_ear_pbi_string, make_array([64], elt="character", fill=0))
  register_mspec(q_d_with_no_simp, form => d_with_no_simp(cadr(form)))
  defun(
    q_parse_string,
    args => polyb__parse_string(arg(args, 0)),
    name="parse-string",
  )
}
