// Port of share/affine/sheafc.lisp: Grobner-basis tests for ideal
// containment, open refinements, blowing up pre-ldata-sheaves, Jacobian
// dichotomies and linear (triangular) ldata.
//
// The structures (ldata, zopen, rmap, pre-ldata-sheaves, s-var, matrix) use
// the `sheafa__` helpers of core/share_sheafa_1.mbt.
//
// Notes on faithfulness:
// - Where the file defines a function several times, the last definition
//   is the live one (`open-refinement-for-list`, `linear-solvedp`,
//   `blowup-pls`, `non-singular-complete-intersection-p`).  The contract
//   declares some of them with the lambda list of an earlier definition;
//   see the comments at those functions.
// - `process-sleep` and `send` are Lisp Machine functions that are
//   undefined in Maxima on SBCL; calling them raises the same
//   undefined-function error here.
// - Format directives `~/maxima::tilde-q-fsh/` are not supported by the
//   runtime FORMAT; such calls are split into FORMAT pieces and direct calls
//   of TILDE-Q-FSH.

// ---------------------------------------------------------------------------
// Symbols without generated constants

///|
let sheafc__q_dot_ldat : Value = sym(".ldat.")

///|
/// The quoted form printed by the IASSERT in OPEN-REFINEMENT-FOR-LIST.
let sheafc__lit_iassert_form : Value = try! lread(
  "(unit-idealp answ (zopen-inequality zopen))",
)

// ---------------------------------------------------------------------------
// Helpers

///|
/// The undefined-function error SBCL signals for a Lisp Machine function.
fn sheafc__undefined_function(name : String) -> Value raise {
  raise LispError::SimpleError(
    "The function MAXIMA::" + name + " is undefined.",
  )
}

///|
/// `(process-sleep n)`: undefined in Maxima on SBCL.
fn sheafc__process_sleep(_n : Value) -> Unit raise {
  sheafc__undefined_function("PROCESS-SLEEP") |> ignore
}

///|
/// The `~/maxima::tilde-q-fsh/` format directive applied to `x` on
/// *standard-output*.
fn sheafc__fsh(x : Value) -> Unit raise {
  tilde_q_fsh(symval(standard_output), x, Nil, Nil) |> ignore
}

///|
fn sheafc__out(ctl : String, args : Array[Value]) -> Unit raise {
  format(t, ctl, args) |> ignore
}

///|
/// `(delete item list :test #'equal)` on a list the caller owns.
fn sheafc__delete_equal(item : Value, l : Value) -> Value {
  let c = Collector::new()
  for x in l.iter() {
    if !equal(x, item) {
      c.add(x)
    }
  }
  c.result()
}

///|
fn sheafc__funcall_key(key : Value, x : Value) -> Value raise {
  if eq(key, q_identity) {
    x
  } else {
    funcall(key, [x])
  }
}

///|
/// `(iassert form)` of amacros.lisp.
fn sheafc__iassert(v : Value, form : Value) -> Unit raise {
  if v is Nil {
    fsignal(list([Str("The expression ~A was not true"), form])) |> ignore
  }
}

///|
/// `(setq-eqns var ld)`: the equations of LD if it is an ldata, else LD.
fn sheafc__eqns_of(x : Value) -> Value raise {
  if ldatap(x).truthy() {
    sheafa__ldata_eqns(x)
  } else {
    x
  }
}

// ---------------------------------------------------------------------------
// Grobner bases and containment

///|
fn grobner_subset(
  id1 : Value,
  id2 : Value,
  may_invert? : Value = Fix(1L),
) -> (Value, Value) raise {
  let unit_ideal = unit_idealp(id2, may_invert~)
  let mut answ = t
  for v in id1.iter() {
    if !d_zerop(polysimp(v).0).truthy() {
      answ = Nil
      break
    }
  }
  (answ, unit_ideal)
}

///|
fn fast_grobner_basis(
  list_eqns : Value,
  may_invert? : Value = Fix(1L),
  string_for_inverse_name? : Value = Str(""),
) -> (Value, Value) raise {
  let pcomplexity_of_inverses : Value = Fix(80L)
  let mut newvars : Value = Nil
  let mut done = false
  for v in list_eqns.iter() {
    if may_invertp(v, may_invert).truthy() {
      set(q_ear_poly_simplifications, list([Fix(1L), rzero()])) |> ignore
      done = true
      break
    }
  }
  if done {
    ()
  } else if !numberp(may_invert) {
    let facts = if symval(q_ear_invert_separately).truthy() &&
      num_gt(pcomplexity(may_invert), pcomplexity_of_inverses) {
      npfactor(may_invert)
    } else {
      list([square_free(may_invert), Fix(1L)])
    }
    newvars = unused_variables(
      int(length(facts) / 2),
      strin=string_for_inverse_name,
    )
    let inverses = Collector::new()
    let mut f = facts
    let mut nv = newvars
    while f is Cons(_) && nv is Cons(_) {
      let pol = car(f)
      let new = car(nv)
      if num_lt(pcomplexity(pol), pcomplexity_of_inverses) {
        inverses.add(pdifference(ptimes(list([new, Fix(1L), Fix(1L)]), pol), Fix(1L)))
      } else {
        sheafc__out(
          "~3%*******  That inverse was a little to complex to use: .. ****~3%",
          [],
        )
        des(pol) |> ignore
      }
      f = cddr(f)
      nv = cdr(nv)
    }
    let eqns = sort_list(
      copy_list(append(inverses.result(), list_eqns)),
      (a, b) => alphalessp(a, b).truthy(),
    )
    set(q_ear_poly_simplifications, grobner_remember(eqns)) |> ignore
  } else {
    set(
      q_ear_poly_simplifications,
      grobner_remember(
        sort_list(copy_list(list_eqns), (a, b) => alphalessp(a, b).truthy()),
      ),
    )
    |> ignore
  }
  (symval(q_ear_poly_simplifications), newvars)
}

///|
fn contract_ideal_localization(
  list_eqns : Value,
  may_invert : Value,
) -> Value raise {
  let mut simps : Value = Nil
  let mut newvars : Value = Nil
  catch_tag(q_took_too_long, () => {
    let (s, n) = fast_grobner_basis(
      list_eqns,
      may_invert~,
      string_for_inverse_name=q_zzzzzzzz,
    )
    simps = s
    newvars = n
    s
  })
  |> ignore
  if simps is Nil {
    sheafc__out("~%******Invalid contraction", [])
    set(
      q_ear_invalid_contractions,
      cons(list([list_eqns, may_invert]), symval(q_ear_invalid_contractions)),
    )
    |> ignore
    list_eqns
  } else {
    let c = Collector::new()
    for v in poly_relations_from_simplifications().iter() {
      let mut ok = true
      for var_ in newvars.iter() {
        if !zerop(pdegree(v, var_)) {
          ok = false
          break
        }
      }
      if ok {
        c.add(v)
      }
    }
    c.result()
  }
}

///|
/// Has a side effect of setting the *poly-simplifications* to be the
/// correct ones.
fn unit_idealp(list_eqns : Value, may_invert? : Value = Fix(1L)) -> Value raise {
  sheafc__out("~%Entering unit-ideal", [])
  if symval(q_ear_verbose_check_overlaps).truthy() {
    sheafa__show("(GEN-PCOMPLEXITY LIST-EQNS)", gen_pcomplexity(list_eqns))
    sheafa__show("(PCOMPLEXITY MAY-INVERT)", pcomplexity(may_invert))
  }
  let answer = catch_tag(q_took_too_long, () => {
    fast_grobner_basis(list_eqns, may_invert~, string_for_inverse_name=Str("ZZ")).0
  })
  if eq(answer, q_took_too_long) {
    set(
      q_ear_too_long_for_grobner_basis,
      cons(
        list([list_eqns, may_invert]),
        symval(q_ear_too_long_for_grobner_basis),
      ),
    )
    |> ignore
    set(q_ear_poly_simplifications, Nil)
  } else if d_zerop(polysimp(Fix(1L)).0).truthy() {
    q_unit_ideal
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// Polynomial utilities

///|
fn ptruncate(poly : Value, var_ : Value, deg : Value) -> Value raise {
  if num_le(pdegree(poly, var_), deg) {
    poly
  } else {
    ptruncate1(poly, var_, deg)
  }
}

///|
fn ptruncate1(poly : Value, var_ : Value, degree : Value) -> Value raise {
  if atom(poly) {
    poly
  } else if pointergp(p__var(poly), var_).truthy() {
    let pol = Collector::new()
    let mut l = cdr(poly)
    while l is Cons(_) {
      let deg = car(l)
      let cof = cadr(l)
      let tem = ptruncate1(cof, var_, degree)
      if !pzerop(tem).truthy() {
        pol.add(deg)
        pol.add(tem)
      }
      l = cddr(l)
    }
    let pol = pol.result()
    if pol.truthy() {
      cons(p__var(poly), pol)
    } else {
      Fix(0L)
    }
  } else if eq(p__var(poly), var_) {
    let mut answ : Value = Nil
    let mut v = cdr(poly)
    while v is Cons(_) {
      if num_le(car(v), degree) {
        answ = v
        break
      }
      v = cddr(v)
    }
    if answ.truthy() {
      cons(var_, answ)
    } else {
      Fix(0L)
    }
  } else {
    poly
  }
}

///|
fn sort_key(
  data : Value,
  pred : Value,
  key : Value,
  rest_key_arg : Value,
) -> Value raise {
  sort_list(copy_list(data), (u, v) => funcall(pred, [
      apply(key, cons(u, rest_key_arg)),
      apply(key, cons(v, rest_key_arg)),
    ]).truthy())
}

///|
fn leading_coefficient(poly : Value, var_ : Value) -> Value raise {
  pcoeff(poly, list([var_, pdegree(poly, var_), Fix(1L)]))
}

// ---------------------------------------------------------------------------
// Opens

///|
/// `(defremember open-subsetp (op1 op2) ...)`.
/// Condition on domain of op1-->op2 is that the part of the denom of the
/// map op1-->op2 which is relatively prime to the inequality on op1, should
/// be invertible on op2.  Condition on the range is that the image of a
/// point in op1 should satisfy the inequality of op2.
fn sheafc__open_subsetp(op1 : Value, op2 : Value) -> Value raise {
  sheafa__remember(sym("open-subsetp"), list([op1, op2]), () => {
    let mut map12 : Value = Nil
    let mut domain_ok : Value = Nil
    let map21 = find_ring_map(op2, op1)
    // MAP12 is still NIL here, as in the original.
    let gf = numerator(apply_rmap(map12, sheafa__rmap_denom(map21)))
    map12 = find_ring_map(op1, op2)
    let gg = numerator(apply_rmap(map12, sheafa__zopen_inequality(op1)))
    if may_invertp(gf, ptimes(gg, sheafa__zopen_inequality(op2))).truthy() {
      domain_ok = t
    }
    if domain_ok.truthy() &&
      may_invertp(
        numerator(apply_rmap(map21, sheafa__zopen_inequality(op2))),
        sheafa__zopen_inequality(op1),
      ).truthy() {
      t
    } else {
      Nil
    }
  })
}

///|
fn open_refinement_for_list(zopen : Value, list_eqns : Value) -> Value raise {
  let gg = sheafa__zopen_inequality(zopen)
  if list_eqns is Nil {
    return list1(zopen)
  }
  for pol in list_eqns.iter() {
    if !any_linearp(pol, gg).truthy() &&
      gm_prepared(pol, inequal=gg).truthy() {
      let answ = best_open_cover(list_eqns, sheafa__zopen_inequality(zopen))
      sheafc__iassert(
        unit_idealp(answ, may_invert=sheafa__zopen_inequality(zopen)),
        sheafc__lit_iassert_form,
      )
      for gg1 in answ.iter() {
        if !(
            unit_idealp(list_eqns, may_invert=gg1).truthy() ||
            linear_ldatap(sheafa__make_ldata(eqns=list_eqns), open_g=gg1).truthy()
          ) {
          fsignal(list1(Str("This refinement is not sufficient."))) |> ignore
        }
      }
      sheafc__out("~%Refining for the equations ", [])
      sheafc__fsh(list_eqns)
      sheafc__out(" with inequality ", [])
      sheafc__fsh(gg)
      sheafc__out(" ~%Using inequalities ", [])
      sheafc__fsh(answ)
      sheafc__out(" ", [])
      let refs = mapcar(
        gg1 => {
          let ans = copy_list(zopen)
          sheafa__set_zopen_inequality(ans, gg1) |> ignore
          ans
        },
        answ,
      )
      return refs
    }
  }
  list1(zopen)
}

///|
/// Eliminates equal duplicates in A-LIST and then if test is given it
/// eliminates items w such that (funcall test v w) is true for some v not
/// equal to w, and if test-not is specified it eliminates w such that
/// (null (funcall test v w)) holds.
fn eliminate_larger(
  a_list : Value,
  key? : Value = q_identity,
  test_? : Value = Nil,
  test_not? : Value = Nil,
  verify? : Value = Nil,
  destructive? : Value = Nil,
) -> Value raise {
  sheafc__eliminate(a_list, key, test_, test_not, verify, destructive, true)
}

///|
fn eliminate_smaller(
  a_list : Value,
  key? : Value = q_identity,
  test_? : Value = Nil,
  test_not? : Value = Nil,
  verify? : Value = Nil,
  destructive? : Value = Nil,
) -> Value raise {
  sheafc__eliminate(a_list, key, test_, test_not, verify, destructive, false)
}

///|
/// Common body of ELIMINATE-LARGER (delete the w) and ELIMINATE-SMALLER
/// (delete the v).
fn sheafc__eliminate(
  a_list : Value,
  key : Value,
  test_ : Value,
  test_not : Value,
  verify : Value,
  destructive : Value,
  larger : Bool,
) -> Value raise {
  let mut a_list = a_list
  let mut test_ = test_
  if destructive is Nil {
    a_list = copy_list(a_list)
  }
  let negate = if test_not.truthy() {
    test_ = test_not
    true
  } else {
    false
  }
  let maybe_not = (x : Value) => if negate { x is Nil } else { x.truthy() }
  // in case two things are equal we don't want to delete both!!
  let orig = a_list
  a_list = union_equal(list1(a_list))
  let mut answ = copy_list(a_list)
  let mut i = 0
  for v in a_list.iter() {
    let mut j = 0
    for w in a_list.iter() {
      if i != j &&
        maybe_not(
          funcall(test_, [sheafc__funcall_key(key, v), sheafc__funcall_key(key, w)]),
        ) {
        answ = sheafc__delete_equal(if larger { w } else { v }, answ)
      }
      j += 1
    }
    i += 1
  }
  if verify.truthy() {
    for v in orig.iter() {
      let mut found = false
      for w in answ.iter() {
        if maybe_not(
            funcall(test_, [
              sheafc__funcall_key(key, w),
              sheafc__funcall_key(key, v),
            ]),
          ) {
          found = true
          break
        }
      }
      if !found {
        merr("~A is not larger than anything in the answer ~a", [v, answ])
        |> ignore
      }
    }
  }
  answ
}

///|
fn add_pls_zopen_history(pls : Value) -> Value raise {
  let opens = Collector::new()
  let mut i = 0
  for v in pls_opens(pls).iter() {
    opens.add(add_zopen_history(v, int(i)))
    i += 1
  }
  sheafa__set_sv_zopens(sheafa__pls_s_var(pls), opens.result()) |> ignore
  Nil
}

///|
fn find_position_in_list(
  item : Value,
  list_ : Value,
  test_? : Value,
) -> Value raise {
  let mut i = 0
  for v in list_.iter() {
    let hit = match test_ {
      None => equal(v, item)
      Some(f) => funcall(f, [v, item]).truthy()
    }
    if hit {
      return int(i)
    }
    i += 1
  }
  Nil
}

///|
/// Makes the list-eqns become first coords in open and in the other opens,
/// it should also look after refining if necessary: ie. if one of eqns is
/// gm-prepared it must refine.  Values: the normal pls, the opens not to
/// blowup, the component codimension.
fn normalize_pls(
  pls : Value,
  open_ : Value,
  ld_number : Value,
) -> (Value, Value, Value) raise {
  let mut ld_number = ld_number
  let opens = pls_opens(pls)
  let lis_data = sheafa__pls_data(pls)
  let nth_open = if numberp(open_) {
    open_
  } else {
    find_position_in_list(open_, opens)
  }
  let mut comp = match_components(pls, nth_open, ldata_number=ld_number)
  let codimension_component = int(
    length(
      sheafa__ldata_eqns(
        nth(to_int(ld_number), nth(to_int(nth_open), lis_data)),
      ),
    ),
  )
  let mut found : Value = Nil
  for v in comp.iter() {
    if eq(cdr(assoc_equal(nth_open, v)), ld_number) {
      found = v
      break
    }
  }
  comp = found
  let mut all_opens_data : Value = Nil
  let mut i = 0
  let mut ops = opens
  let mut lds = lis_data
  while ops is Cons(_) && lds is Cons(_) {
    let op = car(ops)
    let lis_ld = car(lds)
    ld_number = cdr(assoc_equal(int(i), comp))
    if ld_number.truthy() {
      let eqns = sheafa__ldata_eqns(nth(to_int(ld_number), lis_ld))
      let refs = open_refinement_for_list(op, eqns)
      for op1 in refs.iter() {
        all_opens_data = cons(
          list([
            op1,
            lis_ld,
            sheafa__ldata_eqns(nth(to_int(ld_number), lis_ld)),
          ]),
          all_opens_data,
        )
      }
    } else {
      all_opens_data = cons(list([op, lis_ld, Nil]), all_opens_data)
    }
    ops = cdr(ops)
    lds = cdr(lds)
    i += 1
  }
  all_opens_data = nreverse(all_opens_data)
  let all_opens = Collector::new()
  let data = Collector::new()
  let opens_not_to_blowup = Collector::new()
  let mut i = 0
  for v in all_opens_data.iter() {
    if caddr(v).truthy() {
      let tem = normalize_zopen(car(v), caddr(v)).0
      all_opens.add(tem)
      let mapl = find_ring_map(car(v), tem)
      data.add(mapcar(ld => apply_rmap(mapl, ld), cadr(v)))
    } else {
      opens_not_to_blowup.add(int(i))
      all_opens.add(car(v))
      data.add(cadr(v))
    }
    i += 1
  }
  (
    sheafa__make_pls(
      s_var=sheafa__make_s_var(zopens=all_opens.result()),
      data=data.result(),
    ),
    opens_not_to_blowup.result(),
    codimension_component,
  )
}

///|
fn a_factor(fact_list1 : Value, fact_list2 : Value) -> Value raise {
  let mut l = fact_list1
  while l is Cons(_) {
    let pol = car(l)
    let deg = cadr(l)
    let tem = get_alt(pol, fact_list2)
    if !(tem.truthy() && num_ge(tem, deg)) {
      return Nil
    }
    l = cddr(l)
  }
  t
}

///|
fn multiply_out_factorization(facts : Value) -> Value raise {
  let mut answ : Value = Fix(1L)
  let mut l = facts
  while l is Cons(_) {
    answ = ptimes(answ, pexpt(car(l), cadr(l)))
    l = cddr(l)
  }
  answ
}

///|
fn monomialp(pol : Value) -> Value raise {
  if atom(pol) {
    t
  } else if length(pol) == 3 {
    monomialp(caddr(pol))
  } else {
    Nil
  }
}

///|
fn one_variablep(f : Value) -> Value raise {
  lbool(length(f) == 3 && numberp(caddr(f)))
}

///|
fn ldata_simplify_homogeneous(
  ldata : Value,
  may_invert? : Value = Fix(1L),
) -> Value raise {
  let mut used : Value = Nil
  let mut eqns : Value = Nil
  let mut answ : Value = Nil
  let mut all_others : Value = Nil
  let mut simpler : Value = Nil
  let mut added = true
  sheafc__process_sleep(Fix(15L))
  let facts0 = Collector::new()
  for v in sheafa__ldata_eqns(ldata).iter() {
    sheafc__process_sleep(Fix(15L))
    if !d_zerop(v).truthy() {
      facts0.add(non_constant_factors(v, invert=may_invert))
    }
  }
  let mut facts = facts0.result()
  for v in facts.iter() {
    if v is Nil {
      answ = q_unit
      break
    }
  }
  if answ is Nil {
    facts = eliminate_larger(facts, test_=q_a_factor, verify=t)
    let tem = Collector::new()
    let others = Collector::new()
    for v in facts.iter() {
      let mut all_one = true
      let mut l = v
      while l is Cons(_) {
        if !one_variablep(car(l)).truthy() {
          all_one = false
          break
        }
        l = cddr(l)
      }
      if all_one {
        tem.add(multiply_out_factorization(v))
      } else {
        others.add(multiply_out_factorization(v))
      }
    }
    used = tem.result()
    grobner_basis(used) |> ignore
    all_others = others.result()
    // (loop named sue while added ...)
    let mut finished_normally = false
    while true {
      if !added {
        finished_normally = true
        break
      }
      added = false
      let tem = Collector::new()
      let mut inner_normal = true
      let mut sue_exit = false
      for w in all_others.iter() {
        let eqn = numerator(polysimp(w).0)
        if !d_zerop(eqn).truthy() {
          if numberp(eqn) {
            answ = q_unit
            sue_exit = true
            break
          } else if monomialp(eqn).truthy() {
            add_to_poly_simplifications(eqn) |> ignore
            used = cons(eqn, used)
            added = true
            inner_normal = false
            break
          }
          tem.add(eqn)
        }
        if may_invertp(eqn, may_invert).truthy() {
          answ = q_unit
          sue_exit = true
          break
        }
      }
      if sue_exit {
        break
      }
      if inner_normal {
        simpler = tem.result()
      }
    }
    if finished_normally {
      eqns = append(sheafc__delete_equal(Fix(0L), simpler), used)
    }
  }
  if eq(answ, q_unit) {
    sheafc__out("~%It turned out to be trivial", [])
    if symval(q_ear_leave_unit_ldata).truthy() {
      list1(sheafa__make_ldata(eqns=list1(Fix(1L))))
    } else {
      Nil
    }
  } else {
    sheafc__out(
      "~%There are ~A equations of complexity ~A of which ~A are monomials",
      [int(length(eqns)), gen_pcomplexity(eqns), int(length(used))],
    )
    let ld = copy_list(ldata)
    sheafa__set_ldata_eqns(ld, eqns) |> ignore
    list1(ld)
  }
}

///|
/// If the ldata on one open are trivial it will give empty list
/// corresponding to that open.
fn simplify_svar_homogeneous(pls : Value) -> Value raise {
  let pls = copy_list_structure(pls)
  let all_data = Collector::new()
  let mut ops = pls_opens(pls)
  let mut ws = sheafa__pls_data(pls)
  while ops is Cons(_) && ws is Cons(_) {
    let op = car(ops)
    let lds = Collector::new()
    for ld in car(ws).iter() {
      let tem = ldata_simplify_homogeneous(
        ld,
        may_invert=sheafa__zopen_inequality(op),
      )
      if tem.truthy() {
        for x in tem.iter() {
          lds.add(x)
        }
      }
    }
    all_data.add(cons(op, lds.result()))
    ops = cdr(ops)
    ws = cdr(ws)
  }
  let all_data = all_data.result()
  construct_pre_ldata_sheaves(
    s_var=sheafa__make_s_var(zopens=mapcar(x => car(x), all_data)),
    data=mapcar(x => cdr(x), all_data),
  )
}

///|
fn intersection_inequality_in_op1(op1 : Value, op2 : Value) -> Value raise {
  let map1 = find_ring_map(op1, op2)
  let map2 = find_ring_map(op2, op1)
  let mut hh = apply_rmap_to_square_free_factors(
    map2,
    sheafa__zopen_inequality(op2),
  )
  hh = sftimes(
    hh,
    apply_rmap_to_square_free_factors(map2, sheafa__rmap_denom(map1)),
  )
  hh = sftimes(hh, sheafa__zopen_inequality(op1))
  hh = sftimes(hh, sheafa__rmap_denom(map2))
  hh
}

///|
fn refine_pls(pls : Value, list_eqns : Value) -> (Value, Value) raise {
  let mut changed = false
  let all_ops = Collector::new()
  let all_dat = Collector::new()
  let the_eqns = Collector::new()
  let mut ops = pls_opens(pls)
  let mut liss = list_eqns
  let mut dats = sheafa__pls_data(pls)
  while ops is Cons(_) && liss is Cons(_) && dats is Cons(_) {
    let op = car(ops)
    let lis = car(liss)
    let lis_dat = car(dats)
    let refs = open_refinement_for_list(op, lis)
    if length(refs) > 1 {
      changed = true
    }
    for r in refs.iter() {
      all_ops.add(r)
    }
    for _ in 0..<length(refs) {
      all_dat.add(lis_dat)
    }
    for _ in 0..<length(refs) {
      the_eqns.add(lis)
    }
    ops = cdr(ops)
    liss = cdr(liss)
    dats = cdr(dats)
  }
  let new_pls = construct_pre_ldata_sheaves(
    opens=all_ops.result(),
    data=all_dat.result(),
  )
  if changed {
    add_pls_zopen_history(new_pls) |> ignore
  }
  (new_pls, the_eqns.result())
}

///|
fn all_linearp(eqns : Value, inequal? : Value = Fix(1L)) -> Value raise {
  for v in eqns.iter() {
    if !any_linearp(v, inequal).truthy() {
      return Nil
    }
  }
  t
}

///|
fn zopen_special_subset(op1 : Value, op2 : Value) -> Value raise {
  if equal(sheafa__zopen_coord(op1), sheafa__zopen_coord(op2)) {
    may_invertp(sheafa__zopen_inequality(op2), sheafa__zopen_inequality(op1))
  } else {
    Nil
  }
}

///|
fn zopen_equal(op1 : Value, op2 : Value) -> Value raise {
  lbool(
    equal(sheafa__zopen_coord(op1), sheafa__zopen_coord(op2)) &&
    equal(sheafa__zopen_inequality(op1), sheafa__zopen_inequality(op2)),
  )
}

///|
fn try_harder_and_intersect(
  op : Value,
  trans_ld : Value,
  lis_dat : Value,
  hh : Value,
) -> Value raise {
  let b = bind(q_ear_refine_opens, Nil)
  defer unbind(b)
  let mut answ = simplify_ldata(
    sheafa__make_ldata(
      eqns=append(
        sheafa__ldata_eqns(trans_ld),
        sheafa__ldata_eqns(car(lis_dat)),
      ),
    ),
    open_g=hh,
  )
  fsignal(list1(q_hi)) |> ignore
  sheafc__out("~%*** Having to try harder ***.", [])
  if length(answ) == 1 {
    answ = car(answ)
  } else if answ is Nil {
    answ = Nil
  } else {
    fsignal(list1(Str("Two components in the translate"))) |> ignore
  }
  if linear_ldatap(answ, open_g=sheafa__zopen_inequality(op)).truthy() {
    answ
  } else {
    fsignal(
      list1(Str("Real trouble : the ldata are not linear after translation")),
    )
  }
}

///|
/// The eqns will be translated around to other opens and the coords and
/// ldata will be normalized on the components it meets.  A pls and
/// opens-not-to-blowup are returned.
fn prepare_for_blowup(
  pls : Value,
  open_for_equations : Value,
  eqns : Value,
) -> (Value, Value) raise {
  let from_open = open_for_equations
  let orig_eqns = eqns
  let pls = copy_list_structure(pls)
  let ld = if ldatap(eqns).truthy() {
    eqns
  } else {
    sheafa__make_ldata(eqns~)
  }
  let lis_eqns = Collector::new()
  let lis_int_inequal = Collector::new()
  let mut int_inequal : Value = Nil
  let mut op_number = 0
  let mut ops = pls_opens(pls)
  let mut dats = sheafa__pls_data(pls)
  while ops is Cons(_) && dats is Cons(_) {
    let op = car(ops)
    let lis_dat = car(dats)
    let mut tem : Value = Nil
    if lis_dat.truthy() {
      let (a, b) = translate_reduced_component_and_reduce(
        from_open,
        op,
        ld,
        homogeneous_ldata_on_to_open=car(lis_dat),
      )
      tem = a
      int_inequal = b
      lis_eqns.add(sheafa__ldata_eqns(tem))
    } else {
      lis_eqns.add(Nil)
    }
    lis_int_inequal.add(int_inequal)
    if tem.truthy() &&
      length(sheafa__ldata_eqns(tem)) != length(sheafa__ldata_eqns(ld)) {
      merr("wrong number of  equations", []) |> ignore
    }
    sheafc__out("~2%On open ~A the inequality is ", [int(op_number)])
    sheafc__fsh(sheafa__zopen_inequality(op))
    sheafc__out(
      " (before refinement).~%The translated equations are ",
      [],
    )
    sheafc__fsh(sheafa__ldata_eqns(tem))
    sheafc__out(". ", [])
    ops = cdr(ops)
    dats = cdr(dats)
    op_number += 1
  }
  let (ref_pls, transl_eqns) = refine_pls(pls, lis_eqns.result())
  let ref_pls = copy_list_structure(ref_pls)
  let all_data = Collector::new()
  let opens_not_to_blowup = Collector::new()
  let mut i = 0
  let mut ops = pls_opens(ref_pls)
  let mut eqs = transl_eqns
  let mut dats = sheafa__pls_data(ref_pls)
  while ops is Cons(_) && eqs is Cons(_) && dats is Cons(_) {
    let op = car(ops)
    let eqns = car(eqs)
    let lis_dat = car(dats)
    if eqns.truthy() &&
      lis_dat.truthy() &&
      all_linearp(eqns, inequal=sheafa__zopen_inequality(op)).truthy() {
      let (norm_op, tr_data) = normalize_zopen(op, eqns, data=lis_dat)
      sheafc__out("~%On this open ", [])
      sheafc__fsh(eqns)
      sheafc__out(" will correspond to ", [])
      let xs = Collector::new()
      for k in 1..=length(eqns) {
        xs.add(xxx(int(k)))
      }
      sheafc__fsh(xs.result())
      check_normalization(open_for_equations, norm_op, orig_eqns) |> ignore
      sheafc__out("~%normalizing open ~A . ", [int(i)])
      all_data.add(cons(norm_op, tr_data))
    } else {
      sheafc__out("%The open ~A does not meet", [int(i)])
      all_data.add(cons(op, lis_dat))
      opens_not_to_blowup.add(int(i))
    }
    ops = cdr(ops)
    eqs = cdr(eqs)
    dats = cdr(dats)
    i += 1
  }
  let all_data = all_data.result()
  let opens_not_to_blowup = opens_not_to_blowup.result()
  if length(opens_not_to_blowup) == length(all_data) {
    merr("Not going to blowup anything", []) |> ignore
  }
  (
    construct_pre_ldata_sheaves(
      opens=mapcar(x => car(x), all_data),
      data=mapcar(x => cdr(x), all_data),
    ),
    opens_not_to_blowup,
  )
}

///|
fn check_normalization(
  original_open : Value,
  norm_op : Value,
  original_eqns : Value,
) -> Value raise {
  let mut original_eqns = original_eqns
  if !ldatap(original_eqns).truthy() {
    original_eqns = sheafa__make_ldata(eqns=original_eqns)
  }
  let answ = translate_component_and_reduce(
    original_open,
    norm_op,
    original_eqns,
  ).0
  let answ = sort_list(copy_list(sheafa__ldata_eqns(answ)), (a, b) => alphalessp(
      a, b,
    ).truthy())
  let mut vs = answ
  let mut ws = symval(q_ear_xxx)
  while vs is Cons(_) && ws is Cons(_) {
    let v = car(vs)
    let w = car(ws)
    if !(eq(car(v), w) && eql(cadr(v), Fix(1L))) {
      merr("bad normalization", []) |> ignore
    }
    vs = cdr(vs)
    ws = cdr(ws)
  }
  Nil
}

///|
fn hhh(
  pls : Value,
  reduced_pls : Value,
  op_num : Value,
  dat_num : Value,
) -> Value raise {
  blowup_pls_and_reduced_pls(
    pls,
    reduced_pls,
    nth(to_int(op_num), pls_opens(reduced_pls)),
    sheafa__ldata_eqns(pls_ldata(reduced_pls, op_num, ldata_number=dat_num)),
  )
}

///|
fn blowup_pls_and_reduced_pls(
  pls : Value,
  reduced_pls : Value,
  opens_for_eqns : Value,
  eqns : Value,
) -> Value raise {
  let new_pls = blowup_pls(pls, opens_for_eqns, eqns, simplify_homogeneous=t)
  let new_red_pls = blowup_pls(
    reduced_pls,
    opens_for_eqns,
    eqns,
    throw_out_components_in_exceptional_divisor=t,
  )
  list([new_pls, simplify_svar_ldata(new_red_pls)])
}

///|
/// The live definition of BLOWUP-PLS is the last one in sheafc.lisp, whose
/// keywords are :SIMPLIFY-HOMOGENEOUS and :ADD-EXCEPTIONAL-DIVISOR-LDATA
/// (see `sheafc__blowup_pls`).  The contract has the lambda list of the
/// earlier definition; :THROW-OUT-COMPONENTS-IN-EXCEPTIONAL-DIVISOR is not
/// a keyword of the live definition, so passing it is an error, as in CL.
fn blowup_pls(
  pls : Value,
  open_for_eqns : Value,
  eqns : Value,
  simplify_homogeneous? : Value = Nil,
  throw_out_components_in_exceptional_divisor? : Value = Nil,
) -> Value raise {
  if throw_out_components_in_exceptional_divisor.truthy() {
    raise LispError::SimpleError(
      "Unknown &KEY argument: :THROW-OUT-COMPONENTS-IN-EXCEPTIONAL-DIVISOR",
    )
  }
  sheafc__blowup_pls(pls, open_for_eqns, eqns, simplify_homogeneous, Nil)
}

///|
fn sheafc__blowup_pls(
  pls : Value,
  open_for_eqns : Value,
  eqns : Value,
  simplify_homogeneous : Value,
  add_exceptional_divisor_ldata : Value,
) -> Value raise {
  let pls = copy_list_structure(pls)
  let (new_pls, opens_not_to_blowup) = prepare_for_blowup(
    pls, open_for_eqns, eqns,
  )
  sheafa__show("OPENS-NOT-TO-BLOWUP", opens_not_to_blowup)
  let codim = if ldatap(eqns).truthy() {
    int(length(sheafa__ldata_eqns(eqns)))
  } else {
    int(length(eqns))
  }
  sheafc__out("~%****      Blowing a subscheme of codimension ~A  *** ", [
    codim,
  ])
  des(eqns) |> ignore
  blowup_sheaf(
    new_pls,
    codim,
    opens_not_to_blowup~,
    add_exceptional_divisor_ldata~,
    simplify_homogeneous~,
  )
}

///|
fn blowup_keep_exceptional(
  pls : Value,
  red_pls_list? : Value = Nil,
  open_eqns_list? : Value = Nil,
) -> Value raise {
  let mut open_ : Value = Nil
  let mut eqns : Value = Nil
  if red_pls_list.truthy() {
    let red_pls = car(red_pls_list)
    let op_num = cadr(red_pls_list)
    let ld_num = caddr(red_pls_list)
    open_ = nth(to_int(op_num), pls_opens(red_pls))
    eqns = nth(to_int(ld_num), nth(to_int(op_num), sheafa__pls_data(red_pls)))
  } else {
    open_ = car(open_eqns_list)
    eqns = cadr(open_eqns_list)
  }
  with_special(q_ear_leave_unit_ldata, t, () => sheafc__blowup_pls(
    pls, open_, eqns, t, t,
  ))
}

///|
fn blowup_pls_by_component_of_reduced(
  pls : Value,
  red_pls : Value,
  red_open_number : Value,
  ld_number : Value,
) -> Value raise {
  let eqns = nth(
    to_int(ld_number),
    nth(to_int(red_open_number), sheafa__pls_data(red_pls)),
  )
  let open_ = nth(to_int(red_open_number), pls_opens(red_pls))
  sheafc__out("~%Blowing up ", [])
  des(eqns) |> ignore
  sheafc__out(" with coordinates ", [])
  des(open_) |> ignore
  blowup_pls(pls, open_, eqns)
}

// ---------------------------------------------------------------------------
// Linear ldata

///|
/// Checks if the ldata eqns are in triangular linear form, that is if
/// there's a linear variable in eqn1 not occurring in remaining eqns etc.
fn linear_ldatap(ldata : Value, open_g? : Value = Fix(1L)) -> Value raise {
  let eqns = sheafa__ldata_eqns(ldata)
  let lv = Collector::new()
  for v in eqns.iter() {
    let tem = all_linear_variables(v, g=open_g)
    lv.add(tem)
    if tem is Nil {
      return Nil
    }
  }
  let lin_vars = lv.result()
  let var_occurs = mapcar(e => list_variables(e), eqns)
  let result = Collector::new()
  let mut vs = lin_vars
  let mut w = var_occurs
  while vs is Cons(_) && w is Cons(_) {
    let v = car(vs)
    let mut kay = None
    for vv in v.iter() {
      // check vv doesn't occur in remaining equations
      let mut occurs = false
      for ww in cdr(w).iter() {
        if memq(vv, ww).truthy() {
          occurs = true
          break
        }
      }
      if !occurs {
        kay = Some(vv)
        break
      }
    }
    match kay {
      Some(vv) => result.add(vv)
      None => return Nil
    }
    vs = cdr(vs)
    w = cdr(w)
  }
  result.result()
}

///|
fn reduce_linear_ldata(
  ldata : Value,
  variables : Value,
  open_g? : Value = Nil,
) -> Value raise {
  let eqns = reverse(sheafa__ldata_eqns(ldata))
  let vars = reverse(variables)
  let mut fns = eqns
  let mut used_up : Value = Nil
  let mut vs = vars
  while fns.truthy() && vs is Cons(_) {
    let v = car(vs)
    let f = car(fns)
    fns = replace_functions(fns, f, v, invertible_g=open_g)
    used_up = cons(f, used_up)
    vs = cdr(vs)
  }
  used_up
}

///|
/// Tries to check that (var ld2) is subset (var ld1) by checking where
/// dich-f is not zero and where it is zero.  If simplify is t it will try
/// simplifying ld1 further into components on the open where dich-f is not
/// zero, and then try to verify that (var ld2) is contained in one of the
/// components so obtained.
fn check_containment(
  ld1 : Value,
  ld2 : Value,
  dich_f : Value,
  open_g? : Value = Fix(1L),
  simplify? : Value = Nil,
) -> Value raise {
  let _eqn1 = sheafc__eqns_of(ld1)
  let eqn2 = sheafc__eqns_of(ld2)
  let lis_ld = if simplify.truthy() {
    ldata_simplifications(ld1, open_g=nplcm(open_g, dich_f))
  } else {
    list1(ld1)
  }
  // run through the splitting of lis-ld into components
  for ld in lis_ld.iter() {
    if check_containment1(ld, eqn2, dich_f, open_g~).truthy() {
      return t
    }
  }
  Nil
}

///|
fn check_containment1(
  ld1 : Value,
  ld2 : Value,
  dich_f : Value,
  open_g? : Value = Fix(1L),
) -> Value raise {
  let eqn1 = sheafc__eqns_of(ld1)
  let eqn2 = sheafc__eqns_of(ld2)
  let cont = grobner_subset(eqn1, eqn2, may_invert=nplcm(open_g, dich_f)).0
  let mut cont2 : Value = Nil
  if cont.truthy() {
    cont2 = grobner_subset(
      cons(dich_f, eqn1),
      cons(dich_f, eqn2),
      may_invert=open_g,
    ).0
  }
  if cont.truthy() {
    cont2
  } else {
    Nil
  }
}

///|
fn sub_scheme(pls : Value, op_number : Value, ld_number : Value) -> Value raise {
  construct_pre_ldata_sheaves(
    opens=list1(nth(to_int(op_number), pls_opens(pls))),
    data=list1(
      list1(
        nth(to_int(ld_number), nth(to_int(op_number), sheafa__pls_data(pls))),
      ),
    ),
  )
}

///|
fn open_sub_scheme(pls : Value, op_numbers : Value) -> Value raise {
  let ops = Collector::new()
  let dat = Collector::new()
  for i in op_numbers.iter() {
    ops.add(nth(to_int(i), pls_opens(pls)))
    dat.add(nth(to_int(i), sheafa__pls_data(pls)))
  }
  construct_pre_ldata_sheaves(opens=ops.result(), data=dat.result())
}

///|
fn intersect_ldata(ld1 : Value, ld2 : Value, open_g? : Value = Fix(1L)) -> Value raise {
  let b = bind(q_ear_refine_opens, Nil)
  defer unbind(b)
  let eqns = append(sheafa__ldata_eqns(ld1), sheafa__ldata_eqns(ld2))
  ldata_simplifications(sheafa__make_ldata(eqns~), open_g~)
}

///|
/// Writes `(setq PARTi (rerat 'part))` forms to FILE-NAME and returns
/// `(send st :pathname)`: SEND is undefined in Maxima on SBCL, and
/// WITH-OPEN-FILE then aborts (deleting the new file), so the only effect
/// is the error.
fn save_parts(obj : Value, file_name : Value) -> Value raise {
  ignore(obj)
  ignore(file_name)
  sheafc__undefined_function("SEND")
}

///|
/// Opens "r20:ps:<atp.schelter>blew-up.tem", a pathname on the logical
/// host R20, which is not defined in Maxima.
fn save_blew_up() -> Value raise {
  raise LispError::SimpleError("Logical host not yet defined: \"R20\"")
}

///|
fn delete_nth(n : Value, a_list : Value) -> Value raise {
  let c = Collector::new()
  let mut i = 0
  for v in a_list.iter() {
    if !eql(n, int(i)) {
      c.add(v)
    }
    i += 1
  }
  c.result()
}

///|
/// Will return a list of variables ANSWER occurring with degree 1 in
/// various equations such that the equations may be so reordered such that
/// the ith variable in Answer occurs linearly in the ith equation.
fn linear_triangularp(
  fns : Value,
  variables_solved_for? : Value = Nil,
  variables_in_prev_eqns? : Value = Nil,
  varlist_of_fns? : Value = Nil,
) -> Value raise {
  let mut varlist_of_fns = varlist_of_fns
  if varlist_of_fns is Nil {
    varlist_of_fns = mapcar(f => list_variables(f), fns)
  }
  if fns is Nil {
    return variables_solved_for
  }
  let mut i = 0
  let mut fs = fns
  let mut vls = varlist_of_fns
  while fs is Cons(_) && vls is Cons(_) {
    let f = car(fs)
    let varl = car(vls)
    for va in varl.iter() {
      if memq(va, variables_solved_for) is Nil &&
        memq(va, variables_in_prev_eqns) is Nil &&
        eql(pdegree(f, va), Fix(1L)) {
        let tem = linear_triangularp(
          delete_nth(int(i), fns),
          varlist_of_fns=delete_nth(int(i), varlist_of_fns),
          variables_solved_for=cons(va, variables_solved_for),
          variables_in_prev_eqns=append(varl, variables_in_prev_eqns),
        )
        if tem.truthy() {
          return tem
        }
      }
    }
    fs = cdr(fs)
    vls = cdr(vls)
    i += 1
  }
  Nil
}

///|
/// The live definition is the last one, `(fns &rest ignore)`: it returns
/// the variables occurring with degree 1 in one equation and in no other,
/// or NIL unless every equation has such a variable.  The keyword
/// arguments (from an earlier definition) are ignored.
fn linear_solvedp(
  fns : Value,
  variables_solved_for? : Value = Nil,
  variables_in_prev_eqns? : Value = Nil,
  order_functions? : Value = Nil,
  varlist_of_fns? : Value = Nil,
) -> Value raise {
  ignore(variables_solved_for)
  ignore(variables_in_prev_eqns)
  ignore(order_functions)
  ignore(varlist_of_fns)
  let varl = list_variables(fns)
  let genvar = nreverse(sort_list(varl, (a, b) => pointergp(a, b).truthy()))
  with_special(q_genvar, genvar, () => {
    let all_degs = mapcar(fn_ => pdegreevector(fn_), fns)
    let mut bad : Value = Nil
    let mut good : Value = Nil
    for degs in all_degs.iter() {
      let mut found = false
      let mut j = 0
      for i in degs.iter() {
        if eql(i, Fix(1L)) && memq(int(j), bad) is Nil {
          let mut hit = false
          for vv in all_degs.iter() {
            if !physical_equal_value(degs, vv) &&
              !zerop(nth(j, vv)) {
              bad = cons(int(j), bad)
              hit = true
              break
            }
          }
          if !hit {
            good = cons(int(j), good)
            found = true
            break
          }
        }
        j += 1
      }
      if !found {
        good = Nil
        break
      }
    }
    mapcar(j => nth(to_int(j), genvar), nreverse(good))
  })
}

///|
fn plain_simplify_svar_ldata(pls : Value) -> Value raise {
  let all_data = Collector::new()
  let mut i = 0
  let mut ops = pls_opens(pls)
  let mut liss = sheafa__pls_data(pls)
  while ops is Cons(_) && liss is Cons(_) {
    let op = car(ops)
    let one_pls = open_sub_scheme(pls, list1(int(i)))
    let simp_one_pls = simplify_svar_ldata(one_pls)
    let mut list_of_dat : Value = Nil
    if length(pls_opens(simp_one_pls)) == 1 {
      list_of_dat = car(sheafa__pls_data(simp_one_pls))
    } else {
      let all_dat = Collector::new()
      let mut opes = pls_opens(simp_one_pls)
      let mut dats = sheafa__pls_data(simp_one_pls)
      while opes is Cons(_) && dats is Cons(_) {
        let ope = car(opes)
        let ineq = num(
          ratreduce(
            sheafa__zopen_inequality(ope),
            sheafa__zopen_inequality(op),
          ),
        )
        for ld in car(dats).iter() {
          all_dat.add(
            sheafa__make_ldata(
              eqns=contract_ideal_localization(sheafa__ldata_eqns(ld), ineq),
            ),
          )
        }
        opes = cdr(opes)
        dats = cdr(dats)
      }
      list_of_dat = delete_redundant_ldata(
        all_dat.result(),
        gg=sheafa__zopen_inequality(op),
      )
    }
    all_data.add(list_of_dat)
    ops = cdr(ops)
    liss = cdr(liss)
    i += 1
  }
  construct_pre_ldata_sheaves(opens=pls_opens(pls), data=all_data.result())
}

///|
fn svar_simp(ld : Value, open_g? : Value = Fix(1L)) -> Value raise {
  simplify_svar_ldata(
    construct_pre_ldata_sheaves(
      opens=list1(make_normal_zopen(Nil, Fix(8L), open_g)),
      data=list1(list1(ld)),
    ),
  )
}

// ---------------------------------------------------------------------------
// Jacobians

///|
fn jacobian(eqns : Value, variables? : Value, codim? : Value) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => list_variables(eqns)
  }
  let codim = match codim {
    Some(c) => c
    None => int(length(eqns))
  }
  let mat = sheafa__matrix_rows(jacobian_matrix(eqns, variables~))
  let row_tables = sheafa__list_tableaux(codim, int(length(eqns)))
  let col_tables = sheafa__list_tableaux(codim, int(length(variables)))
  let all = Collector::new()
  for ro_tabl in row_tables.iter() {
    let jacob = Collector::new()
    for tabl in col_tables.iter() {
      set(
        q_ear_sparse_matrix,
        convert_to_sparse_matrix(
          mat,
          columns_to_use=tabl,
          rows_to_use=ro_tabl,
          re_use_sparse_matrix=symval(q_ear_sparse_matrix),
        ),
      )
      |> ignore
      let det = sp_determinant(symval(q_ear_sparse_matrix))
      if numberp(det) {
        if !d_zerop(det).truthy() {
          sp_show_matrix(symval(q_ear_sparse_matrix)) |> ignore
          sheafa__show("TABL", tabl)
          sheafa__show("RO-TABL", ro_tabl)
          return list1(Fix(1L))
        }
      } else {
        jacob.add(det)
      }
    }
    for x in jacob.result().iter() {
      all.add(x)
    }
  }
  all.result()
}

///|
/// Values: the determinant (must invert) and the rank.
fn rank_generic_reduce_jacobian(
  eqns : Value,
  variables? : Value,
) -> (Value, Value) raise {
  let variables = match variables {
    Some(v) => v
    None => list_variables(eqns)
  }
  let mat = sheafa__matrix_rows(jacobian_matrix(eqns, variables~))
  set(
    q_ear_sparse_matrix,
    convert_to_sparse_matrix(
      mat,
      re_use_sparse_matrix=symval(q_ear_sparse_matrix),
    ),
  )
  |> ignore
  let det = sp_determinant(symval(q_ear_sparse_matrix))
  (det, sp_number_of_pivots(symval(q_ear_sparse_matrix)))
}

///|
fn reduce_jacobian(eqns : Value, variables? : Value) -> (Value, Value) raise {
  let variables = match variables {
    Some(v) => v
    None => list_variables(eqns)
  }
  let mat = sheafa__matrix_rows(jacobian_matrix(eqns, variables~))
  set(
    q_ear_sparse_matrix,
    convert_to_sparse_matrix(
      mat,
      re_use_sparse_matrix=symval(q_ear_sparse_matrix),
    ),
  )
  |> ignore
  let det = sp_determinant(symval(q_ear_sparse_matrix))
  (det, sp_number_of_pivots(symval(q_ear_sparse_matrix)))
}

///|
/// Values: (singular-locus non-singularp).  The live definition is the
/// last one, which also has the keywords :CODIM (default the number of
/// equations) and :VARIABLES (default the variables of EQNS); the contract
/// has the lambda list of the earlier definition, so they take their
/// defaults here.
fn non_singular_complete_intersection_p(
  eqns : Value,
  open_g? : Value = Fix(1L),
  use_simplification? : Value = t,
) -> (Value, Value) raise {
  let variables = list_variables(eqns)
  let mut eqns = eqns
  if ldatap(eqns).truthy() {
    eqns = sheafa__ldata_eqns(eqns)
  }
  let codim = int(length(eqns))
  let eqns_and_jacob = mapcar(
    x => square_free(x),
    append(eqns, jacobian(eqns, variables~, codim~)),
  )
  if use_simplification.truthy() {
    let new = ldata_simplifications(
      sheafa__make_ldata(eqns=eqns_and_jacob),
      open_g~,
    )
    if new is Nil {
      (list1(Fix(1L)), t)
    } else {
      (new, Nil)
    }
  } else if unit_idealp(eqns_and_jacob, may_invert=open_g).truthy() {
    (list1(Fix(1L)), t)
  } else {
    let singular_locus = poly_relations_from_simplifications()
    (list1(sheafa__make_ldata(eqns=singular_locus)), Nil)
  }
}

///|
fn simplify_dichotomy(
  ldata : Value,
  fn_ : Value,
  open_g? : Value = Fix(1L),
) -> Value raise {
  let a = ldata_simplifications(
    sheafa__make_ldata(eqns=cons(fn_, sheafa__ldata_eqns(ldata))),
    open_g~,
  )
  let b = mapcar(
    v => sheafa__make_ldata(
      eqns=contract_ideal_localization(sheafa__ldata_eqns(v), fn_),
    ),
    ldata_simplifications(ldata, open_g=sftimes(open_g, fn_)),
  )
  let answ = append(a, b)
  delete_redundant_ldata(answ, open_g~, ignore_ldata_inequalities=t)
}

///|
fn non_trivial_open_sub_scheme(pls : Value) -> Value raise {
  let c = Collector::new()
  let mut i = 0
  for lis in sheafa__pls_data(pls).iter() {
    if lis.truthy() &&
      member_equal(Fix(1L), sheafa__ldata_eqns(car(lis))) is Nil {
      c.add(int(i))
    }
    i += 1
  }
  let non_trivial = c.result()
  sheafa__show("NON-TRIVIAL", non_trivial)
  // (break t): enters the debugger.
  raise LispError::SimpleError("Break: T")
}

///|
fn show_divisors(pls : Value) -> Value raise {
  let c = Collector::new()
  let mut i = 0
  for lis in sheafa__pls_data(pls).iter() {
    let inner = Collector::new()
    for ld in cdr(lis).iter() {
      let tem = car(sheafa__ldata_eqns(ld))
      if !numberp(tem) {
        inner.add(tem)
      }
    }
    let tem = inner.result()
    c.add(tem)
    sheafc__out("~%On open ~D the divisors are ", [int(i)])
    sheafc__fsh(tem)
    i += 1
  }
  c.result()
}

///|
fn jacobian_dichotomy(ldata : Value, open_g? : Value = Fix(1L)) -> Value raise {
  let (c_reqd, rank) = rank_generic_reduce_jacobian(sheafa__ldata_eqns(ldata))
  let gg = sftimes(open_g, sheafa__ldata_inequality(ldata))
  let answer = if may_invertp(c_reqd, gg).truthy() {
    if eql(int(length(sheafa__ldata_eqns(ldata))), rank) {
      sheafc__out("~%Non singular ldata", [])
    } else {
      sheafc__out("~%singular ldata", [])
    }
    list1(ldata)
  } else if eql(rank, int(length(sheafa__ldata_eqns(ldata)))) {
    let ld1 = copy_list_structure(ldata)
    let ld2 = copy_list(ldata)
    sheafa__set_ldata_eqns(
      ld1,
      append(sheafa__ldata_eqns(ldata), list1(c_reqd)),
    )
    |> ignore
    sheafa__set_ldata_inequality(ld1, gg) |> ignore
    sheafa__set_ldata_inequality(ld2, sftimes(gg, c_reqd)) |> ignore
    sheafc__out("~%Breaking into dichotomy on:", [])
    sh(c_reqd) |> ignore
    sheafc__out("%original ldata followed by consequents:", [])
    des(ldata) |> ignore
    des(ld1) |> ignore
    des(ld2) |> ignore
    append(
      ldata_simplifications(ld1, open_g~, recursive_p=t),
      ldata_simplifications(ld2, open_g~, recursive_p=t),
    )
  } else {
    list1(ldata)
  }
  delete_redundant_ldata(answer, open_g~, ignore_ldata_inequalities=t)
}

///|
fn d_list_components(lis_ldat : Value) -> Value raise {
  let mut lis_ldat = lis_ldat
  if eq(car(lis_ldat), q_pre_ldata_sheaves) {
    // (apply 'append (pls-data lis-ldat))
    let c = Collector::new()
    for l in sheafa__pls_data(lis_ldat).iter() {
      c.append_list(l)
    }
    lis_ldat = c.result()
  } else if ldatap(lis_ldat).truthy() {
    lis_ldat = list1(lis_ldat)
  }
  cons(
    list1(q_mlist),
    mapcar(
      v => cons(list1(q_mlist), mapcar(e => new_disrep(e), sheafa__ldata_eqns(v))),
      lis_ldat,
    ),
  )
}

///|
fn d_simple_solve(eqns : Value, open_g? : Value = Fix(1L)) -> Value raise {
  let mut open_g = open_g
  let ld = sheafa__make_ldata(eqns=st_rat(eqns))
  let (to_invert0, rank) = rank_generic_reduce_jacobian(sheafa__ldata_eqns(ld))
  let to_invert = sftimes(Fix(1L), to_invert0)
  if eql(int(length(sheafa__ldata_eqns(ld))), rank) {
    if may_invertp(to_invert, open_g).truthy() {
      ()
    } else {
      sheafc__out("having to invert ", [])
      sheafc__fsh(to_invert)
      open_g = sftimes(open_g, to_invert)
    }
  }
  open_g = st_rat(open_g)
  let vari = linear_ldatap(ld, open_g~)
  if vari is Nil {
    fsignal(list1(Str("equations not linear-ldatap"))) |> ignore
  }
  let solu = solve_simple_system(sheafa__ldata_eqns(ld), vari, invertible=open_g)
  let c = Collector::new()
  let mut vs = vari
  let mut ws = solu
  while vs is Cons(_) && ws is Cons(_) {
    c.add(
      list([list1(q_mequal), get(car(vs), q_disrep), new_disrep(st_rat(car(ws)))]),
    )
    vs = cdr(vs)
    ws = cdr(ws)
  }
  cons(list1(q_mlist), c.result())
}

// ---------------------------------------------------------------------------
// Body macros: these return the macro expansion.

///|
/// `(setq-eqns var1 val1 var2 val2 ...)`: expands to
/// `(progn (cond ((ldatap val1) (setf var1 (ldata-eqns val1)))
///               (t (setf var1 val1))) ...)`.
fn setq_eqns(alt_list : Value) -> Value raise {
  let c = Collector::new()
  let mut v = alt_list
  while v is Cons(_) {
    let var_ = car(v)
    let val = cadr(v)
    c.add(
      list([
        q_cond,
        list([
          list([q_ldatap, val]),
          list([q_setf, var_, list([q_ldata_eqns, val])]),
        ]),
        list([t, list([q_setf, var_, val])]),
      ]),
    )
    v = cddr(v)
  }
  cons(q_progn, c.result())
}

///|
/// `(sim-hom x)`: `(setq simp-x (simplify-svar-homogeneous x))`.
fn sim_hom(x : Value) -> Value raise {
  let name = sym("simp-" + lstring(string(x)))
  list([q_setq, name, list([q_simplify_svar_homogeneous, x])])
}

///|
/// `(sim-ld x)`: `(setq red-<x trimmed of the characters of "simp-">
/// (simplify-svar-ldata x))`.
fn sim_ld(x : Value) -> Value raise {
  let name = sym("red-" + string_trim("simp-", lstring(string(x))))
  list([q_setq, name, list([q_simplify_svar_ldata, x])])
}

///|
/// `(save-rational name [file-name])`.  Without FILE-NAME the expansion
/// itself calls SEND (undefined in Maxima on SBCL).
fn save_rational(name : Value, file_name? : Value) -> Value raise {
  let file_name = match file_name {
    None => return sheafc__undefined_function("SEND")
    Some(f) => f
  }
  list([
    q_with_open_file,
    list([q_st, list([q_quote, file_name]), q_kw_direction, q_kw_output]),
    list([
      q_let,
      list1(q_ear_print_gensym),
      list([
        q_format,
        q_st,
        Str(
          ";;; -*- mode: lisp; package: cl-maxima; syntax: common-lisp -*-\n     ~%(setq ~A (rerat '",
        ),
        list([q_quote, name]),
      ]),
      list([q_format, q_st, Str("~s"), name]),
      list([q_format, q_st, Str("))")]),
      list([q_quote, file_name]),
    ]),
  ])
}

///|
/// `(alter-ldata ldat key1 repl1 ...)`: expands to
/// `(let ((.ldat. ldat)) (setf (ldata-key1 .ldat.) repl1) ... .ldat.)`, or
/// `(progn ldat)` without keys.
fn alter_ldata(ldat : Value, keys : Value) -> Value raise {
  let body = Collector::new()
  let mut k = keys
  while k is Cons(_) {
    let key = car(k)
    let repl = cadr(k)
    let acc = sym("ldata-" + lstring(string(key)))
    body.add(list([q_setf, list([acc, sheafc__q_dot_ldat]), repl]))
    k = cddr(k)
  }
  let body = body.result()
  if body.truthy() {
    list_star([
      q_let,
      list1(list([sheafc__q_dot_ldat, ldat])),
      append(body, list1(sheafc__q_dot_ldat)),
    ])
  } else {
    list([q_progn, ldat])
  }
}

///|
fn init_share_sheafc() -> Unit raise {

}
