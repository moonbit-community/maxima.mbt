// Port of share/affine/polysmp.lisp: Groebner bases of commutative
// polynomial ideals over the affine package's CRE polynomials.
//
// A degree sequence is an alternating list (var1 deg1 var2 deg2 ...) of
// genvars and degrees, most main variable first. *poly-simplifications*
// is an alternating list (seq1 repl1 seq2 repl2 ...) of the leading
// monomials (as degree sequences) and their replacements (rational
// functions).

///|
fn get_altq(item : Value, a_list : Value) -> Value raise {
  let mut v = a_list
  while v is Cons(_) {
    if eq(item, car(v)) {
      return second(v)
    }
    v = cddr(v)
  }
  Nil
}

///|
/// Degree of a monomial in var. Returns nil if var not in monom.
fn mdegree(monom : Value, var_ : Value) -> Value raise {
  let mut v = monom
  while true {
    if numberp(v) {
      return Nil
    }
    if eq(car(v), var_) {
      return second(v)
    }
    v = caddr(v)
  }
  Nil
}

///|
/// The argument is a CRE polynomial and the monomial degs is an
/// alternating list of the variable and the degree. Note these must be
/// ordered in increasing degree for the degree sequence.
fn part_above_degree(poly : Value, monomial_degs : Value) -> Value raise {
  let mut monomial_degs = monomial_degs
  if monomial_degs is Nil {
    poly
  } else if numberp(monomial_degs) {
    poly
  } else if numberp(poly) {
    let mut w = cdr(monomial_degs)
    while w is Cons(_) {
      if !eql(car(w), Fix(0L)) {
        return Nil
      }
      w = cddr(w)
    }
    poly
  } else {
    let mut deg : Value = Nil
    if eq(car(monomial_degs), car(poly)) {
      deg = num_sub(second(monomial_degs), Fix(1L))
      monomial_degs = cddr(monomial_degs)
    } else {
      deg = get_altq(car(poly), monomial_degs)
      deg = if deg.truthy() { num_sub(deg, Fix(1L)) } else { Fix(-1L) }
    }
    let the_cof = Collector::new()
    let mut v = cdr(poly)
    while v is Cons(_) && num_gt(car(v), deg) {
      let tem = part_above_degree(second(v), monomial_degs)
      if tem.truthy() {
        the_cof.add(car(v))
        the_cof.add(tem)
      }
      v = cddr(v)
    }
    let the_cof = the_cof.result()
    if the_cof.truthy() {
      cons(car(poly), the_cof)
    } else {
      Nil
    }
  }
}

///|
/// "x^3*y+x^2*u, x^2 ==> x*y+u"
fn part_above(poly : Value, monom : Value) -> Value raise {
  let v = part_above1(poly, monom)
  if v.truthy() {
    v
  } else {
    Fix(0L)
  }
}

///|
fn part_above1(poly : Value, monom : Value) -> Value raise {
  if numberp(monom) {
    poly
  } else if numberp(poly) {
    Nil
  } else {
    let mut monom = monom
    let mut true_deg : Value = Fix(0L)
    let mut deg : Value = Nil
    if eq(p__var(monom), p__var(poly)) {
      deg = num_sub(second(monom), Fix(1L))
      true_deg = second(monom)
      monom = caddr(monom)
    } else {
      deg = mdegree(monom, car(poly))
      deg = if deg.truthy() { num_sub(deg, Fix(1L)) } else { Fix(-1L) }
    }
    let the_cof = Collector::new()
    let mut v = cdr(poly)
    while v is Cons(_) && num_gt(car(v), deg) {
      let tem = part_above1(second(v), monom)
      if tem.truthy() {
        the_cof.add(num_sub(car(v), true_deg))
        the_cof.add(tem)
      }
      v = cddr(v)
    }
    let the_cof = the_cof.result()
    if the_cof.truthy() {
      cons(car(poly), the_cof)
    } else {
      Nil
    }
  }
}

///|
/// "x^3*y+x^2*u, x^2 ==> u". Rule: if a variable appears in monom it must
/// be to the exact power, and if it is in variables to exclude it may not
/// appear unless it was in monom to the exact power. (pcoeff pol 1 ..)
/// will exclude variables like substituting them to be zero.
fn pcoeff(
  poly : Value,
  monom : Value,
  variables_to_exclude_from_cof? : Value,
) -> Value raise {
  let excl = match variables_to_exclude_from_cof {
    Some(v) => v
    None => list_variables(monom)
  }
  let mut monom = monom
  if eql(monom, Fix(1L)) {
    ()
  } else if atom(monom) {
    monom = list3(monom, Fix(1L), Fix(1L))
  }
  if !(listp(monom) || eql(monom, Fix(1L))) {
    raise LispError::SimpleError(
      format_to_string("The value of MONOM, ~S, should be 1 or a monomial", [
        monom,
      ]),
    )
  }
  let v = pcoeff1(poly, monom, variables_to_exclude_from_cof=excl)
  if v.truthy() {
    v
  } else {
    Fix(0L)
  }
}

///|
fn pcoeff1(
  poly : Value,
  monom : Value,
  variables_to_exclude_from_cof? : Value,
) -> Value raise {
  let excl = match variables_to_exclude_from_cof {
    Some(v) => v
    None => list_variables(monom)
  }
  if numberp(monom) && numberp(poly) {
    return poly
  }
  if numberp(poly) {
    return Nil
  }
  let mut monom = monom
  let mut true_deg : Value = Fix(0L)
  let mut first_case = true
  if numberp(monom) {
    if memq(p__var(poly), excl).truthy() {
      true_deg = Fix(0L)
    } else {
      first_case = false
    }
  } else if eq(p__var(monom), p__var(poly)) {
    true_deg = second(monom)
    monom = caddr(monom)
  } else if memq(p__var(poly), excl).truthy() {
    true_deg = Fix(0L)
  } else {
    first_case = false
  }
  if first_case {
    let mut r = cdr(poly)
    while r is Cons(_) {
      if eql(car(r), true_deg) {
        return pcoeff1(cadr(r), monom, variables_to_exclude_from_cof=excl)
      }
      r = cddr(r)
    }
    Nil
  } else if numberp(monom) || pointergp(car(poly), car(monom)).truthy() {
    let temm = Collector::new()
    let mut r = cdr(poly)
    while r is Cons(_) {
      let tem = pcoeff1(cadr(r), monom, variables_to_exclude_from_cof=excl)
      if tem.truthy() {
        temm.add(car(r))
        temm.add(tem)
      }
      r = cddr(r)
    }
    let temm = temm.result()
    if temm.truthy() {
      if eql(car(temm), Fix(0L)) {
        second(temm)
      } else {
        cons(car(poly), temm)
      }
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn replacements(simps? : Value) -> Value raise {
  let simps = match simps {
    Some(v) => v
    None => symval(q_ear_poly_simplifications)
  }
  let c = Collector::new()
  let mut v = simps
  while v is Cons(_) {
    c.add(car(v))
    v = cddr(v)
  }
  c.result()
}

///|
/// Checks for occurrence of seq in poly (without consing).
fn occurs_in(poly : Value, seq : Value) -> Value raise {
  lbool(eq(catch_tag(q_its_there, () => occurs_in1(poly, seq)), q_ok))
}

///|
fn occurs_in1(poly : Value, seq : Value) -> Value raise {
  catch_tag(q_not_in_this_one, () => {
    if seq is Nil {
      throw_tag(q_its_there, q_ok)
    } else if numberp(poly) {
      t
    } else {
      let var_ = first(seq)
      let deg = second(seq)
      if pointergp(car(poly), var_).truthy() {
        let mut r = cdr(poly)
        while r is Cons(_) {
          occurs_in1(cadr(r), seq) |> ignore
          r = cddr(r)
        }
        Nil
      } else if eq(car(poly), var_) {
        if num_lt(second(poly), deg) {
          throw_tag(q_not_in_this_one, Nil)
        } else {
          let mut r = cdr(poly)
          while r is Cons(_) && num_ge(car(r), deg) {
            occurs_in1(cadr(r), cddr(seq)) |> ignore
            r = cddr(r)
          }
          Nil
        }
      } else {
        throw_tag(q_not_in_this_one, Nil)
      }
    }
  })
}

///|
fn convert_deg_sequence_to_monomial(sequ : Value) -> Value raise {
  if sequ is Nil {
    Nil
  } else if numberp(sequ) {
    sequ
  } else {
    let tem = convert_deg_sequence_to_monomial(cddr(sequ))
    if tem.truthy() {
      if !eql(Fix(0L), second(sequ)) {
        list3(car(sequ), second(sequ), tem)
      } else {
        tem
      }
    } else {
      list3(car(sequ), second(sequ), Fix(1L))
    }
  }
}

///|
fn constant_deg_sequencep(seq : Value) -> Value raise {
  let mut w = seq
  while w is Cons(_) {
    if !eql(car(w), Fix(0L)) {
      return Nil
    }
    w = cddr(w)
  }
  t
}

///|
fn d_declare_constant_list(ll : Value) -> Value raise {
  declare_constant(cdr(ll))
}

///|
fn declare_constant(l : Value) -> Value raise {
  for v in l.iter() {
    if get(v, q_disrep).truthy() {
      putprop(v, t, q_constant) |> ignore
    } else {
      putprop(car(num(new_rat(v))), t, q_constant) |> ignore
    }
  }
  Nil
}

///|
fn show_constants() -> Value raise {
  for v in symval(q_ear_genvar).iter() {
    if get(v, q_constant).truthy() {
      format(t, "~A disreps to ~A and is constant.", [v, get(v, q_disrep)])
      |> ignore
    }
  }
  Nil
}

///|
fn remove_constant_property(a_list : Value) -> Value raise {
  for u in a_list.iter() {
    let mut v = symval(q_ear_varlist)
    let mut w = symval(q_ear_genvar)
    while v is Cons(_) && w is Cons(_) {
      if eq(car(v), u) || eq(car(w), u) {
        remprop(car(w), q_constant) |> ignore
      }
      v = cdr(v)
      w = cdr(w)
    }
  }
  Nil
}

///|
/// Assumes that the variables have been ordered so that the constant
/// variables are the least main.
fn constant_functionp(poly : Value) -> Value raise {
  if numberp(poly) || numberp(car(poly)) {
    t
  } else if symval(q_ear_use_constants).truthy() && symbolp(car(poly)) {
    get(car(poly), q_constant)
  } else {
    Nil
  }
}

///|
fn find_main_monomial(poly : Value) -> (Value, Value) raise {
  if numberp(poly) {
    return (Nil, poly)
  }
  let mut poly = poly
  let mut cof : Value = Nil
  let seq = Collector::new()
  while poly.truthy() {
    seq.add(car(poly))
    seq.add(second(poly))
    poly = third(poly)
    if constant_functionp(poly).truthy() {
      cof = poly
      poly = Nil
    }
  }
  (seq.result(), cof)
}

///|
fn find_least_main_monomial(poly : Value) -> (Value, Value) raise {
  let mut poly = poly
  let mut mono_so_far : Value = Nil
  let mut cof : Value = Nil
  while poly.truthy() {
    let mut tem = last2(poly)
    if !(mono_so_far is Nil && zerop(car(tem)) && numberp(second(tem))) {
      if !zerop(car(tem)) {
        mono_so_far = cons(car(tem), cons(car(poly), mono_so_far))
      }
    } else {
      tem = polyc__lastn(Fix(4L), poly)
      mono_so_far = cons(car(tem), cons(car(poly), mono_so_far))
    }
    if numberp(second(tem)) {
      poly = Nil
      cof = second(tem)
    } else {
      poly = second(tem)
    }
  }
  (nreverse(mono_so_far), cof)
}

///|
fn deg_sequence(variables : Value, degrees : Value) -> Value raise {
  let c = Collector::new()
  let mut v = variables
  let mut w = degrees
  while v is Cons(_) && w is Cons(_) {
    if !eql(car(w), Fix(0L)) {
      c.add(car(v))
      c.add(car(w))
    }
    v = cdr(v)
    w = cdr(w)
  }
  c.result()
}

///|
fn factor_out_monomial(poly : Value, monomial_degs : Value, copy_ : Value) -> Value raise {
  let poly = if copy_.truthy() { copy_tree(poly) } else { poly }
  if numberp(poly) || numberp(monomial_degs) {
    poly
  } else {
    let deg = get_altq(car(poly), monomial_degs)
    let mut v = poly
    while v is Cons(_) && third(v).truthy() {
      if deg.truthy() {
        setf_car(cdr(v), sub(second(v), deg)) |> ignore
      }
      setf_car(cddr(v), factor_out_monomial(third(v), monomial_degs, Nil))
      |> ignore
      v = cddr(v)
    }
    poly
  }
}

///|
/// REPLACEMENT is a poly not a rat-poly.
fn replace_monomial(
  poly : Value,
  replacement : Value,
  monomial_degs : Value,
  part_above? : Value = Nil,
) -> Value raise {
  check_arg(poly, q_affine_polynomialp, list1(Str("polynomial"))) |> ignore
  check_arg(replacement, q_rational_functionp, list1(Str("rat'l function")))
  |> ignore
  let to_replace = if part_above.truthy() {
    part_above
  } else {
    part_above_degree(poly, monomial_degs)
  }
  if numberp(poly) && zerop(poly) {
    rzero()
  } else if to_replace.truthy() {
    let mut answer = pdifference(poly, to_replace)
    let denom_replacement = denom(replacement)
    answer = ptimes(denom_replacement, answer)
    let tem = ptimes(
      num(replacement),
      factor_out_monomial(to_replace, monomial_degs, t),
    )
    answer = pplus(answer, tem)
    maybe_ratreduce(answer, denom_replacement)
  } else {
    poly
  }
}

///|
/// REPLACEMENT is a poly not a rat-poly.
fn replace_monomial_rat(
  poly : Value,
  replacement : Value,
  monomial_degs : Value,
  part_above? : Value = Nil,
) -> Value raise {
  check_arg(poly, q_rational_functionp, list1(Str("rat'l function"))) |> ignore
  check_arg(replacement, q_rational_functionp, list1(Str("rat'l function")))
  |> ignore
  let to_replace = if part_above.truthy() {
    part_above
  } else {
    part_above_degree(num(poly), monomial_degs)
  }
  if numberp(num(poly)) && zerop(num(poly)) {
    rzero()
  } else if to_replace.truthy() {
    let mut answer = pdifference(num(poly), to_replace)
    let denom_replacement = denom(replacement)
    answer = ptimes(denom_replacement, answer)
    let tem = ptimes(
      num(replacement),
      factor_out_monomial(to_replace, monomial_degs, t),
    )
    answer = pplus(answer, tem)
    if eql(Fix(1L), denom(poly)) {
      maybe_ratreduce(answer, denom_replacement)
    } else {
      maybe_ratreduce(answer, ptimes(denom(poly), denom_replacement))
    }
  } else {
    poly
  }
}

///|
fn maybe_ratreduce(a : Value, b : Value) -> Value raise {
  if symval(q_ear_reduce).truthy() {
    ratreduce(a, b)
  } else {
    cons(a, b)
  }
}

///|
fn d_add_to_poly_simplifications(rat_monom : Value) -> Value raise {
  let rat_monom = cdr(d_new_rat(rat_monom))
  add_to_poly_simplifications(rat_monom)
}

///|
fn add_to_poly_simplifications(rat_monom : Value, simplify? : Value = t) -> Value raise {
  let mut simplify = simplify
  let orig = rat_monom
  let mut rat_monom = rat_monom
  if symval(q_ear_simplify_rhs).truthy() {
    rat_monom = polysimp(rat_monom).0
  } else {
    rat_monom = new_rat(rat_monom)
  }
  if numberp(rat_monom) {
    if !zerop(rat_monom) || d_zerop(orig) is Nil {
      set(q_ear_poly_simplifications, list2(Fix(1L), rzero())) |> ignore
    }
  } else if eql(Fix(0L), num(rat_monom)) {
    princ(Str(".")) |> ignore
    simplify = Nil
  } else if numberp(rat_monom) ||
    (listp(rat_monom) && constant_functionp(num(rat_monom)).truthy()) {
    set(q_ear_poly_simplifications, list2(Fix(1L), rzero())) |> ignore
    with_special(q_ear_print_level, Fix(2L), () => {
      format(t, "There is a constant ~A in the *poly-simplifications*", [
        rat_monom,
      ])
    })
    |> ignore
  } else {
    let (seq, cof) = find_main_monomial(num(rat_monom))
    let replacement_num = pdifference(
      ptimes(cof, convert_deg_sequence_to_monomial(seq)),
      num(rat_monom),
    )
    if !numberp(denom(rat_monom)) &&
      constant_functionp(denom(rat_monom)) is Nil {
      format(
        t,
        "Warning: a denominator was discared which might take the value 0",
        [Nil],
      )
      |> ignore
    }
    let replacement = ratreduce(replacement_num, cof)
    if !numberp(cof) {
      if member_equal(cof, symval(q_ear_degenerate_conditions)) is Nil {
        set(
          q_ear_degenerate_conditions,
          cons(cof, symval(q_ear_degenerate_conditions)),
        )
        |> ignore
      }
    }
    set(
      q_ear_poly_simplifications,
      append(symval(q_ear_poly_simplifications), list2(seq, replacement)),
    )
    |> ignore
  }
  if simplify.truthy() {
    simplify_poly_simplifications() |> ignore
  }
  symval(q_ear_poly_simplifications)
}

///|
fn grobner_basis(list_polys : Value, homogeneous? : Value = Nil) -> Value raise {
  set(q_ear_poly_simplifications, Nil) |> ignore
  set(q_ear_degenerate_conditions, Nil) |> ignore
  for v in list_polys.iter() {
    add_to_poly_simplifications(v) |> ignore
  }
  check_overlaps(Fix(40L), reset=t, homogeneous~) |> ignore
  symval(q_ear_poly_simplifications)
}

///|
fn ideal_subsetp(
  id1 : Value,
  id2 : Value,
  verbose? : Value = t,
  reset_basis? : Value = t,
) -> Value raise {
  if reset_basis.truthy() {
    grobner_basis(id2) |> ignore
  }
  for v in id1.iter() {
    let tem = polysimp(v).0
    if rzerop(tem) is Nil {
      if verbose.truthy() {
        format(
          t,
          "~A is not zero modulo the second ideal. It is congruent to ~A",
          [id2, tem],
        )
        |> ignore
      }
      return Nil
    }
  }
  t
}

///|
fn d_set_up_poly_simplifications(a_list : Value) -> Value raise {
  check_arg(a_list, q_d_listp, Nil) |> ignore
  set(q_ear_poly_simplifications, Nil) |> ignore
  for v in cdr(a_list).iter() {
    add_to_poly_simplifications(st_rat(v)) |> ignore
  }
  convert_poly_simplifications_to_macsyma_form(
    symval(q_ear_poly_simplifications),
  )
}

///|
fn d_show_simps() -> Value raise {
  convert_poly_simplifications_to_macsyma_form(
    symval(q_ear_poly_simplifications),
  )
}

///|
fn must_replacep(poly : Value) -> (Value, Value, Value) raise {
  let mut part_above : Value = Nil
  let mut monom : Value = Nil
  let mut replace : Value = Nil
  let mut r = symval(q_ear_poly_simplifications)
  while r is Cons(_) {
    let seq = car(r)
    let repl = cadr(r)
    part_above = part_above_degree(poly, seq)
    if part_above.truthy() {
      monom = convert_deg_sequence_to_monomial(seq)
      replace = repl
      break
    }
    r = cddr(r)
  }
  set(q_ear_must_replace_data, list3(part_above, monom, replace)) |> ignore
  (part_above, monom, replace)
}

///|
fn monomial_finish_replace() -> Value raise {
  let data = symval(q_ear_must_replace_data)
  let part_above = first(data)
  let mon = second(data)
  let repl = third(data)
  cons(ptimes(num(repl), num(ratreduce(part_above, mon))), denom(repl))
}

///|
fn sort_poly_simplifications() -> Value raise {
  set(
    q_ear_poly_simplifications,
    sort_grouped_list(
      symval(q_ear_poly_simplifications),
      Fix(2L),
      lfunc("lambda", args => {
        let x = arg(args, 0)
        let y = arg(args, 1)
        if equal(x, y) {
          Nil
        } else {
          funcall(symval(q_ear_monomial_order_function), [y, x])
        }
      }),
    ),
  )
}

///|
fn check_simp(a : Value, simped : Value, tag? : Value = q_simps_not_equal) -> Value raise {
  if !equal(polysimp(a).0, simped) {
    amacros__break(prin1_to_string(tag))
  } else {
    Nil
  }
}

///|
fn conclusionp() -> Value raise {
  if symval(q_ear_conclusion).truthy() {
    format(t, "~%Checking conclusion... ", []) |> ignore
    if zero_modulo_simplifications(symval(q_ear_conclusion)).truthy() {
      format(t, "~%The conclusion already follows.", []) |> ignore
      throw_tag(q_its_proven, t)
    } else {
      format(t, "no good yet", [])
    }
  } else {
    Nil
  }
}

///|
fn new_zerop(x : Value) -> Value raise {
  lbool(eql(x, Fix(0L)) || (listp(x) && eql(car(x), Fix(0L))))
}

///|
fn simplify_poly_simplifications() -> Value raise {
  let mut resimplify = false
  if symval(q_ear_show_grob).truthy() {
    let leng = length(symval(q_ear_poly_simplifications))
    format(t, "~%Starting to simplify ~A poly-simplifications ", [
      int(leng / 2),
    ])
    |> ignore
    if 10 > leng {
      show_simps() |> ignore
    } else {
      format(t, "~%Replacements are :", []) |> ignore
      show_replacements() |> ignore
    }
  }
  let mut unit_ideal = false
  let mut r = symval(q_ear_poly_simplifications)
  while r is Cons(_) {
    if numberp(car(r)) {
      set(q_ear_poly_simplifications, list2(Fix(1L), rzero())) |> ignore
      unit_ideal = true
      break
    }
    r = cddr(r)
  }
  if !unit_ideal {
    sort_poly_simplifications() |> ignore
    let mut i = 2
    while i <= length(symval(q_ear_poly_simplifications)) {
      let ps = symval(q_ear_poly_simplifications)
      let seq = nth(i - 2, ps)
      let repl = nth(i - 1, ps)
      let old_simps = ps
      set(
        q_ear_poly_simplifications,
        append(subseq(ps, 0, end=i - 2), nthcdr(i, ps)),
      )
      |> ignore
      let mono = convert_deg_sequence_to_monomial(seq)
      if must_replacep(mono).0.truthy() {
        if symval(q_ear_show_grob).truthy() {
          sh(mono) |> ignore
          format(t, "   is not  reduced", []) |> ignore
        }
        let replacement_of_mono = monomial_finish_replace()
        if equal(replacement_of_mono, repl) {
          i -= 2
          format(t, "eliminated one", []) |> ignore
        } else {
          let mut dif = pdifference(
            ptimes(num(replacement_of_mono), denom(repl)),
            ptimes(num(repl), denom(replacement_of_mono)),
          )
          if symval(q_ear_simplify_rhs).truthy() {
            dif = polysimp(dif).0
          }
          if new_zerop(dif) is Nil {
            add_to_poly_simplifications(dif, simplify=Nil) |> ignore
          }
          resimplify = true
          break
        }
      } else if symval(q_ear_simplify_rhs).truthy() &&
        must_replacep(num(repl)).0.truthy() {
        // replace the replacement only so monom ok..
        let mut repl_simp = polysimp(num(repl)).0
        repl_simp = ratreduce(
          num(repl_simp),
          ptimes(denom(repl_simp), denom(repl)),
        )
        setf_car(nthcdr(i - 1, old_simps), repl_simp) |> ignore
        set(q_ear_poly_simplifications, old_simps) |> ignore
      } else {
        set(q_ear_poly_simplifications, old_simps) |> ignore
      }
      i += 2
    }
  }
  if resimplify {
    simplify_poly_simplifications() |> ignore
  }
  symval(q_ear_poly_simplifications)
}

///|
/// `#'-`
let polysmp__minus_fn : Value = lfunc("-", args => {
  num_sub(arg(args, 0), arg(args, 1))
})

///|
fn seq_op(seqa : Value, seqb : Value, op? : Value) -> Value raise {
  let op = match op {
    Some(f) => f
    None => polysmp__minus_fn
  }
  if seqa is Nil {
    seqb
  } else if seqb is Nil {
    seqa
  } else if eq(car(seqa), car(seqb)) {
    nconc(
      list2(car(seqa), funcall(op, [second(seqa), second(seqb)])),
      seq_op(cddr(seqa), cddr(seqb), op~),
    )
  } else if pointergp(car(seqa), car(seqb)).truthy() {
    // (nconc (list ...) (seq-op (cddr seqa) seqb) op): the function OP is
    // the last argument of NCONC (and the recursive call uses #'-).
    nconc_n([list2(car(seqa), second(seqa)), seq_op(cddr(seqa), seqb), op])
  } else {
    nconc(list2(car(seqb), second(seqb)), seq_op(seqa, cddr(seqb), op~))
  }
}

///|
fn seq_lessp(seqa : Value, seqb : Value) -> Value raise {
  let r = catch_tag(q_less, () => {
    seq_op(
      seqa,
      seqb,
      op=lfunc("lambda", args => {
        if num_gt(arg(args, 0), arg(args, 1)) {
          throw_tag(q_less, t)
        } else {
          Nil
        }
      }),
    )
  })
  if r.truthy() {
    Nil
  } else {
    t
  }
}

///|
fn seq_minus(seqa : Value) -> Value raise {
  let seqa = copy_list(seqa)
  let mut v = cdr(seqa)
  while v is Cons(_) {
    setf_car(v, num_neg(first(v))) |> ignore
    v = cddr(v)
  }
  seqa
}

///|
fn basis_from_simps(simps? : Value) -> Value raise {
  let simps = match simps {
    Some(v) => v
    None => symval(q_ear_poly_simplifications)
  }
  let c = Collector::new()
  let mut r = simps
  while r is Cons(_) {
    c.add(n__(car(r), cadr(r)))
    r = cddr(r)
  }
  cons(list1(q_mlist), c.result())
}

///|
fn convert_poly_simplifications_to_macsyma_form(simps : Value) -> Value raise {
  let c = Collector::new()
  let mut r = simps
  while r is Cons(_) {
    c.add(
      list3(
        list1(q_mlist),
        header_poly(convert_deg_sequence_to_monomial(car(r))),
        header_poly(cadr(r)),
      ),
    )
    r = cddr(r)
  }
  cons(list1(q_mlist), c.result())
}

///|
fn overlap_degree(seqa : Value, seqb : Value) -> Value raise {
  let mut sum : Value = Fix(0L)
  let mut v = seqa
  while v is Cons(_) {
    let tem = get_altq(car(v), seqb)
    let mut counted = false
    if tem.truthy() {
      let temm = num_min(tem, second(v))
      if !zerop(temm) {
        sum = num_add(sum, num_sub(second(v), temm))
        counted = true
      }
    }
    if !counted {
      sum = num_add(sum, second(v))
    }
    v = cddr(v)
  }
  num_add(sum, degree_of_deg_sequence(seqb))
}

///|
fn overlap(seqa : Value, seqb : Value) -> Value raise {
  let c = Collector::new()
  let mut v = seqa
  while v is Cons(_) {
    let tem = get_altq(car(v), seqb)
    if tem.truthy() {
      let tem = num_min(tem, second(v))
      if !zerop(tem) {
        c.add(car(v))
        c.add(tem)
      }
    }
    v = cddr(v)
  }
  c.result()
}

///|
fn degree_of_deg_sequence(seq : Value) -> Value raise {
  let mut sum : Value = Fix(0L)
  let mut v = cdr(seq)
  while v is Cons(_) {
    sum = num_add(sum, car(v))
    v = cddr(v)
  }
  sum
}

///|
fn replacement_sequences() -> Value raise {
  replacements(simps=symval(q_ear_poly_simplifications))
}

///|
fn show_replacements() -> Value raise {
  displa(d_poly_replacements())
}

///|
fn d_poly_replacements() -> Value raise {
  let c = Collector::new()
  for v in replacements().iter() {
    c.add(header_poly(convert_deg_sequence_to_monomial(v)))
  }
  cons(list1(q_mlist), c.result())
}

///|
fn degree_of_worst_monomial(poly : Value) -> Value raise {
  degree_of_deg_sequence(find_main_monomial(poly).0)
}

///|
fn show_simps(simps? : Value) -> Value raise {
  let simps = match simps {
    Some(v) => v
    None => symval(q_ear_poly_simplifications)
  }
  displa(convert_poly_simplifications_to_macsyma_form(simps))
}

///|
/// `(get-internal-run-time)` in SBCL's microseconds.
fn polysmp__internal_run_time() -> Value {
  int64((cpu_time() * 1000000.0).to_int64())
}

///|
fn timedbasis(initial_time : Value) -> Value raise {
  let tgb = symval(q_ear_timed_grobner_basis)
  if tgb.truthy() &&
    num_lt(tgb, num_sub(polysmp__internal_run_time(), initial_time)) {
    if symval(q_ear_verbose_check_overlaps).truthy() {
      format(t, "~%Grobner basis took too long, didn't finish", []) |> ignore
      show_simps() |> ignore
    }
    throw_tag(q_took_too_long, q_took_too_long)
  } else {
    Nil
  }
}

///|
fn check_overlaps(
  deg : Value,
  reset? : Value = Nil,
  homogeneous? : Value = Nil,
  from_degree? : Value = Fix(1L),
  add_to_simps? : Value = t,
  maybe_reset? : Value = t,
  initial_time? : Value,
) -> Value raise {
  let mut initial_time = match initial_time {
    Some(v) => v
    None => polysmp__internal_run_time()
  }
  let mut homogeneous = homogeneous
  let mut from_degree = from_degree
  if symval(q_ear_homogeneous_relations).truthy() {
    amacros__show("*HOMOGENEOUS-RELATIONS*", symval(q_ear_homogeneous_relations))
    format(t, "Assuming homogeneous relations", []) |> ignore
    homogeneous = t
  }
  if reset.truthy() {
    set(q_ear_overlaps_already_checked, Nil) |> ignore
  } else if maybe_reset.truthy() {
    if amacros__y_or_n_p("Reset  *overlaps-already-checked* to nil") {
      set(q_ear_overlaps_already_checked, Nil) |> ignore
    }
  }
  let mut i = from_degree
  while num_le(i, deg) {
    // (block big-sue ...)
    let mut subl = nreverse(replacement_sequences())
    let mut done = false
    while subl is Cons(_) && !done {
      let v = car(subl)
      let mut ws = cdr(subl)
      while ws is Cons(_) {
        let w = car(ws)
        if w.truthy() && num_eq(overlap_degree(v, w), i) {
          let tem = overlap(v, w)
          if tem.truthy() &&
            member_equal(list2(v, w), symval(q_ear_overlaps_already_checked))
            is Nil {
            timedbasis(initial_time) |> ignore
            let associator = check_associative(v, tem, w)
            set(
              q_ear_overlaps_already_checked,
              cons(list2(v, w), symval(q_ear_overlaps_already_checked)),
            )
            |> ignore
            if rzerop(associator).truthy() {
              initial_time = num_add(initial_time, Fix(30L))
              if symval(q_ear_verbose_check_overlaps).truthy() {
                amacros__show(
                  "(- (GET-INTERNAL-RUN-TIME) INITIAL-TIME)",
                  num_sub(polysmp__internal_run_time(), initial_time),
                )
                format(t, " zero associator, ", []) |> ignore
              }
            } else if add_to_simps.truthy() {
              add_to_poly_simplifications(associator) |> ignore
              if symval(q_ear_show_complexity).truthy() {
                terpri()
                let mut s = cdr(symval(q_ear_poly_simplifications))
                while s is Cons(_) {
                  let vv = car(s)
                  format(t, " . ~a", [
                    num_add(pcomplexity(num(vv)), pcomplexity(denom(vv))),
                  ])
                  |> ignore
                  s = cddr(s)
                }
              }
              conclusionp() |> ignore
              if homogeneous is Nil {
                from_degree = num_min(
                  from_degree,
                  degree_of_worst_monomial(car(associator)),
                )
              }
              check_overlaps(
                deg,
                homogeneous~,
                from_degree~,
                initial_time~,
                add_to_simps~,
                maybe_reset=Nil,
              )
              |> ignore
              done = true
              break
            } else {
              amacros__break("FOUND-NON-ASSOCIATIVE") |> ignore
            }
          }
        }
        ws = cdr(ws)
      }
      subl = cdr(subl)
    }
    if homogeneous.truthy() {
      from_degree = i
    }
    i = num_add(i, Fix(1L))
  }
  symval(q_ear_poly_simplifications)
}

///|
fn d_polysimp(f : Value) -> Value raise {
  let typ = poly_type(f)
  let answer = if eq(typ, q_kw_number) {
    f
  } else if eq(typ, q_kw_polynomial) {
    polysimp(f).0
  } else if eq(typ, q_kw_rational_function) {
    ratquotient(polysimp(num(f)).0, polysimp(denom(f)).0)
  } else {
    Nil
  }
  if answer.truthy() {
    header_poly(answer)
  } else if mbagp(f).truthy() {
    cons(car(f), mapcar(x => d_polysimp(x), cdr(f)))
  } else {
    d_polysimp(new_rat(d_totaldisrep(f)))
  }
}

///|
fn check_associative(a : Value, overlap : Value, b : Value) -> Value raise {
  if symval(q_ear_show_grob).truthy() {
    format(t, "Checking overlap ~A for ~A ~A ", [
      disrep_list(overlap),
      disrep_list(a),
      disrep_list(b),
    ])
    |> ignore
  }
  let ma = convert_deg_sequence_to_monomial(a)
  let mo = convert_deg_sequence_to_monomial(overlap)
  let mb = convert_deg_sequence_to_monomial(b)
  let mut simpa = get_altq(a, symval(q_ear_poly_simplifications))
  let mut simpb = get_altq(b, symval(q_ear_poly_simplifications))
  simpa = cons(ptimes(num(simpa), num(ratreduce(mb, mo))), denom(simpa))
  simpb = cons(ptimes(num(simpb), num(ratreduce(ma, mo))), denom(simpb))
  // everything you're just shifting a numerator there
  if equal(simpa, simpb) {
    princ(Str(".")) |> ignore
    if symval(q_ear_show_grob).truthy() {
      format(t, "..The overlap is associative", []) |> ignore
    }
    rzero()
  } else {
    let mut answer = ratdifference(simpa, simpb)
    let mut plain_answer : Value = Nil
    if symval(q_ear_simplify_rhs) is Nil {
      plain_answer = answer
      answer = nred(
        polysimp(function_numerator(answer)).0,
        function_denominator(answer),
      )
    }
    if symval(q_ear_simplify_rhs) is Nil {
      if new_zerop(answer) is Nil {
        answer = plain_answer
      }
    }
    if symval(q_ear_show_grob).truthy() {
      format(t, "~%The difference  is ..", []) |> ignore
      sh(answer) |> ignore
    }
    if new_zerop(answer).truthy() {
      princ(Str(".")) |> ignore
      rzero()
    } else {
      answer
    }
  }
}

///|
fn reverse_z_order_sequence(seqa : Value, seqb : Value) -> Value raise {
  lbool(!equal(seqa, seqb) && z_order_sequence(seqb, seqa) is Nil)
}

///|
fn z_order_sequence(seqa : Value, seqb : Value) -> Value raise {
  let mut v = seqa
  let mut w = seqb
  if atom(v) || atom(w) {
    return lbool(!equal(v, w))
  }
  while true {
    if num_lt(symbol_value(car(v)), symbol_value(car(w))) ||
      num_lt(second(v), second(w)) {
      return Nil
    }
    v = cddr(v)
    if atom(v) {
      break
    }
    w = cddr(w)
    if atom(w) {
      break
    }
  }
  lbool(!equal(v, w))
}

///|
fn n_star_star(l : Value) -> Value raise {
  match length(l) {
    0 => Fix(1L)
    1 => car(l)
    2 => n_star(list2(car(l), cadr(l)))
    _ => n_star(list2(car(l), n_star_star(cdr(l))))
  }
}

///|
/// So x<x^2<z<z^2<z^2*x<z^2*x*t: the worst monomial is the most main
/// monomial, ie highest degree in z then highest in y etc.
fn xyz_order_sequence(seqa : Value, seqb : Value) -> Value raise {
  let mut seqa = seqa
  let mut r = seqb
  while r is Cons(_) && seqa.truthy() {
    let var_ = car(r)
    let deg = cadr(r)
    if eq(car(seqa), var_) {
      if num_gt(second(seqa), deg) {
        return Nil
      } else if num_lt(second(seqa), deg) {
        return t
      } else {
        seqa = cddr(seqa)
      }
    } else if pointergp(car(seqa), var_).truthy() {
      return Nil
    } else {
      return t
    }
    r = cddr(r)
  }
  if seqa is Nil {
    seqb
  } else {
    Nil
  }
}

///|
fn degree_of_sequence(seq : Value) -> Value raise {
  let mut sum : Value = Fix(0L)
  let mut v = cdr(seq)
  while v is Cons(_) {
    sum = num_add(sum, car(v))
    v = cddr(v)
  }
  sum
}

///|
fn xyz_and_degree(seqa : Value, seqb : Value) -> Value raise {
  let d1 = degree_of_sequence(seqa)
  let d2 = degree_of_sequence(seqb)
  if eq(d1, d2) {
    xyz_order_sequence(seqa, seqb)
  } else if num_lt(d1, d2) {
    t
  } else {
    Nil
  }
}

///|
fn remove_0(lis : Value) -> Value raise {
  let c = Collector::new()
  let mut r = lis
  while r is Cons(_) {
    if !zerop(cadr(r)) {
      c.add(car(r))
      c.add(cadr(r))
    }
    r = cddr(r)
  }
  c.result()
}

///|
fn reverse_xyz_order_sequence(seqa : Value, seqb : Value) -> Value raise {
  lbool(!equal(seqa, seqb) && xyz_order_sequence(seqb, seqa) is Nil)
}

///|
fn zero_modulo_simplifications(poly : Value) -> Value raise {
  pzerop(polysimp_ignore_denominator(poly))
}

///|
/// Returns something G where G*unit = poly modulo simplifications.
fn polysimp_ignore_denominator(poly : Value) -> Value raise {
  with_special(q_ear_reduce, Nil, () => {
    let mut poly = if affine_polynomialp(poly).truthy() {
      cons(poly, Fix(1L))
    } else if rational_functionp(poly).truthy() {
      cons(num(poly), Fix(1L))
    } else {
      cons(num(new_rat(poly)), Fix(1L))
    }
    if constant_functionp(poly) is Nil {
      let mut changes = true
      while changes {
        changes = false
        let mut v = symval(q_ear_poly_simplifications)
        while v is Cons(_) {
          let tem = part_above_degree(num(poly), car(v))
          if tem.truthy() {
            changes = true
            let repl = replace_monomial_rat(poly, second(v), car(v), part_above=tem)
            if eql(num(repl), Fix(0L)) {
              changes = false
            }
            poly = cons(num(repl), Fix(1L))
            break
          }
          v = cddr(v)
        }
      }
    }
    function_numerator(poly)
  })
}

///|
fn polysimp(poly : Value) -> (Value, Value) raise {
  let mut poly = poly
  let mut changed : Value = Nil
  if affine_polynomialp(poly).truthy() {
    poly = cons(poly, Fix(1L))
  } else if rational_functionp(poly).truthy() {
    ()
  } else {
    fsignal(list2(Str("bad-poly ~a"), poly)) |> ignore
    poly = new_rat(poly)
  }
  if constant_functionp(poly).truthy() {
    if get_altq(Fix(1L), symval(q_ear_poly_simplifications)).truthy() {
      (Fix(0L), Nil)
    } else {
      (poly, Nil)
    }
  } else {
    let mut changes = true
    while changes {
      changes = false
      let mut v = symval(q_ear_poly_simplifications)
      while v is Cons(_) {
        let tem = part_above_degree(num(poly), car(v))
        if tem.truthy() {
          changes = true
          changed = t
          let repl = replace_monomial_rat(poly, second(v), car(v), part_above=tem)
          if eql(num(repl), Fix(0L)) {
            changes = false
          }
          poly = repl
          break
        }
        v = cddr(v)
      }
    }
    (poly, changed)
  }
}

///|
fn convert_monomial_to_deg_sequence(monom : Value) -> Value raise {
  if atom(monom) || monom is Nil {
    Nil
  } else {
    let tem = convert_monomial_to_deg_sequence(third(monom))
    append(list2(car(monom), second(monom)), tem)
  }
}

///|
fn d_current_grobner_basis(simps? : Value) -> Value raise {
  let simps = match simps {
    Some(v) => v
    None => symval(q_ear_poly_simplifications)
  }
  let c = Collector::new()
  let mut r = simps
  while r is Cons(_) {
    let seq = car(r)
    let repl = cadr(r)
    if numberp(seq) {
      return list2(list1(q_mlist), Fix(1L))
    }
    c.add(
      header_poly(
        cons(
          pdifference(
            num(repl),
            ptimes(convert_deg_sequence_to_monomial(seq), denom(repl)),
          ),
          Fix(1L),
        ),
      ),
    )
    r = cddr(r)
  }
  cons(list1(q_mlist), c.result())
}

///|
fn d_grobner_basis(
  ideal : Value,
  no_concl? : Value = Nil,
  homogeneous? : Value = Nil,
  upto? : Value = Fix(100L),
) -> Value raise {
  if no_concl.truthy() {
    set(q_ear_conclusion, Nil) |> ignore
  }
  check_arg(ideal, q_d_listp, list1(Str("macsyma list"))) |> ignore
  d_set_up_poly_simplifications(ideal) |> ignore
  conclusionp() |> ignore
  check_overlaps(upto, reset=t, homogeneous~) |> ignore
  d_current_grobner_basis()
}

///|
/// Deletes first occurrence.
fn delete_pair(first_item : Value, a_list : Value) -> Value raise {
  let tem = Collector::new()
  let mut w = a_list
  while w is Cons(_) {
    if !equal(car(w), first_item) {
      tem.add(car(w))
      tem.add(second(w))
    } else {
      return nconc(tem.result(), cddr(w))
    }
    w = cddr(w)
  }
  tem.result()
}

///|
fn seq_subset(seqa : Value, seqb : Value) -> Value raise {
  let answer = catch_tag(q_not_in, () => {
    seq_op(
      seqa,
      seqb,
      op=lfunc("lambda", args => {
        let a = arg(args, 0)
        let b = arg(args, 1)
        if num_le(a, b) {
          num_sub(b, a)
        } else {
          throw_tag(q_not_in, q_no)
        }
      }),
    )
  })
  if eq(answer, q_no) {
    Nil
  } else {
    answer
  }
}

///|
/// This is dangerous for some reason...
fn substitute_real_symbols_for_genvar(a_list? : Value = Nil) -> Value raise {
  let mut a_list = a_list
  if a_list is Nil {
    a_list = mapcar(
      v => Value::Sym(intern(string_trim("$", lstring(string(get(v, q_disrep)))))),
      symval(q_ear_genvar),
    )
  }
  if length(a_list) != length(symval(q_ear_genvar)) {
    raise LispError::SimpleError("The value of A-LIST is not right length")
  }
  let mut v = symval(q_ear_genvar)
  let mut w = a_list
  while v is Cons(_) && w is Cons(_) {
    set(car(w), symbol_value(car(v))) |> ignore
    set_symbol_plist(car(w), symbol_plist(car(v))) |> ignore
    v = cdr(v)
    w = cdr(w)
  }
  set(q_ear_genvar, a_list) |> ignore
  set(q_ear_old_genvar, symval(q_ear_genvar)) |> ignore
  Nil
}

///|
fn d_nilpotent(d_f : Value) -> Value raise {
  let old_simps = symval(q_ear_poly_simplifications)
  let r = try {
    with_special(q_ear_conclusion, Nil, () => {
      let me = sub_star(mul_star(list2(d_f, q_d_ggggg)), Fix(1L))
      let mee = new_rat(me)
      add_to_poly_simplifications(mee) |> ignore
      check_overlaps(Fix(10L), add_to_simps=t, reset=t) |> ignore
      if eql(Fix(0L), d_polysimp(q_d_ggggg)) {
        t
      } else {
        Nil
      }
    })
  } catch {
    e => {
      set(q_ear_poly_simplifications, old_simps) |> ignore
      raise e
    }
  }
  set(q_ear_poly_simplifications, old_simps) |> ignore
  r
}

///|
fn rat_variable(a_var : Value) -> Value raise {
  let mut v = symval(q_ear_varlist)
  let mut w = symval(q_ear_genvar)
  // (loop for v in *varlist* for w in *genvar* ...): at the end V is the
  // exhausted one (NIL) and W keeps its last value when *varlist* ran out
  // first.
  let mut last_v : Value = Nil
  let mut last_w : Value = Nil
  while true {
    if atom(v) {
      last_v = Nil
      last_w = car(w)
      break
    }
    if atom(w) {
      last_v = car(v)
      last_w = Nil
      break
    }
    if eq(car(v), a_var) {
      return list3(car(w), Fix(1L), Fix(1L))
    }
    v = cdr(v)
    if atom(v) {
      last_v = Nil
      last_w = car(w)
      break
    }
    w = cdr(w)
  }
  amacros__show("A-VAR", a_var)
  amacros__show("V", last_v)
  amacros__show("W", last_w)
  new_rat(mul_star(list2(a_var, Fix(2L)))) |> ignore
  rat_variable(a_var)
}

///|
fn must_replace_monom(monom : Value, repl : Value) -> Value raise {
  for seq in repl.iter() {
    if occurs_in(monom, seq).truthy() {
      return t
    }
  }
  Nil
}

///|
fn sort_list_of_monomials(a_list : Value) -> Value raise {
  let grouped = Collector::new()
  for v in a_list.iter() {
    grouped.add(convert_monomial_to_deg_sequence(v))
    grouped.add(v)
  }
  let grouped = sort_grouped_list(
    grouped.result(),
    Fix(2L),
    symval(q_ear_monomial_order_function),
  )
  let c = Collector::new()
  let mut w = cdr(grouped)
  while w is Cons(_) {
    c.add(car(w))
    w = cddr(w)
  }
  c.result()
}

///|
fn d_poly_monomial_dimensions(variables : Value, to_deg : Value) -> Value raise {
  let mut tot : Value = Fix(0L)
  let mut i : Value = Fix(0L)
  while num_le(i, to_deg) {
    let tem = int(length(polysmp__grobner_monomials(variables, i, None, Nil)))
    format(t, "~%There are ~A independent monomials in degree ~A", [tem, i])
    |> ignore
    tot = num_add(tot, tem)
    i = num_add(i, Fix(1L))
  }
  format(t, "~% The total is ~A.", [tot]) |> ignore
  tot
}

///|
/// The DEFREMEMBER memory lookup for F with the key KEY.
fn polysmp__remember(
  f : Value,
  key : Value,
  recall : () -> Value raise,
  body : () -> Value raise,
) -> Value raise {
  if get(f, q_kw_dont_remember).truthy() {
    return body()
  }
  let hash_table = get(f, q_kw_memory_table)
  if hash_table.truthy() {
    let ans = gethash(key, hash_table)
    if ans.truthy() {
      ans
    } else {
      let ans = body()
      sethash(key, hash_table, ans) |> ignore
      ans
    }
  } else {
    putprop(f, make_hash_table(kind=Equal), q_kw_memory_table) |> ignore
    recall()
  }
}

///|
/// `(defremember grobner-bi-monomials (variables-y variables-x n-y n-x
/// &optional (replacements (replacements)) reset) ...)`
fn polysmp__grobner_bi_monomials(
  variables_y : Value,
  variables_x : Value,
  n_y : Value,
  n_x : Value,
  replacements_ : Value?,
  reset : Value,
) -> Value raise {
  let replacements_ = match replacements_ {
    Some(v) => v
    None => replacements()
  }
  polysmp__remember(
    polysmp__q_grobner_bi_monomials,
    list([variables_y, variables_x, n_y, n_x, replacements_, reset]),
    () => polysmp__grobner_bi_monomials(
      variables_y,
      variables_x,
      n_y,
      n_x,
      Some(replacements_),
      reset,
    ),
    () => {
      if reset.truthy() {
        clear_memory_function(q_grobner_monomials) |> ignore
      }
      check_arg(variables_y, q_d_listp, list1(Str("macsyma list"))) |> ignore
      if num_eq(n_x, Fix(0L)) {
        polysmp__grobner_monomials(variables_y, n_y, Some(replacements_), reset)
      } else if num_eq(n_y, Fix(0L)) {
        polysmp__grobner_monomials(variables_x, n_x, Some(replacements_), reset)
      } else {
        let c = Collector::new()
        for w in polysmp__grobner_bi_monomials(
            variables_y,
            variables_x,
            num_sub(n_y, Fix(1L)),
            n_x,
            Some(replacements_),
            reset,
          ).iter() {
          for uu in polysmp__grobner_monomials(
              variables_y,
              Fix(1L),
              Some(replacements_),
              reset,
            ).iter() {
            if num_ge(symbol_value(car(uu)), symbol_value(car(w))) {
              let tem = ptimes(w, uu)
              if must_replace_monom(tem, replacements_) is Nil {
                c.add(tem)
              }
            }
          }
        }
        c.result()
      }
    },
  )
}

///|
/// `(defremember grobner-monomials (variables n &optional (replacements
/// (replacements)) reset) ...)`
fn polysmp__grobner_monomials(
  variables : Value,
  n : Value,
  replacements_ : Value?,
  reset : Value,
) -> Value raise {
  let replacements_ = match replacements_ {
    Some(v) => v
    None => replacements()
  }
  polysmp__remember(
    q_grobner_monomials,
    list4(variables, n, replacements_, reset),
    () => polysmp__grobner_monomials(variables, n, Some(replacements_), reset),
    () => {
      if reset.truthy() {
        clear_memory_function(q_grobner_monomials) |> ignore
      }
      check_arg(variables, q_d_listp, list1(Str("macsyma list"))) |> ignore
      if num_eq(n, Fix(0L)) {
        if member(Fix(1L), replacements_).truthy() {
          Nil
        } else {
          list1(Fix(1L))
        }
      } else if num_eq(n, Fix(1L)) {
        let rat_vars = Collector::new()
        for v in cdr(variables).iter() {
          let vv = rat_variable(v)
          if must_replace_monom(vv, replacements_) is Nil {
            rat_vars.add(vv)
          }
        }
        sort_list(rat_vars.result(), (x, y) => pointergp(car(x), car(y)).truthy())
      } else {
        let c = Collector::new()
        for w in polysmp__grobner_monomials(
            variables,
            num_sub(n, Fix(1L)),
            Some(replacements_),
            reset,
          ).iter() {
          for uu in polysmp__grobner_monomials(
              variables,
              Fix(1L),
              Some(replacements_),
              reset,
            ).iter() {
            if num_ge(symbol_value(car(uu)), symbol_value(car(w))) {
              let tem = ptimes(w, uu)
              if must_replace_monom(tem, replacements_) is Nil {
                c.add(tem)
              }
            }
          }
        }
        c.result()
      }
    },
  )
}

///|
fn d_grobner_monomials(
  variables : Value,
  n : Value,
  replacements? : Value,
  reset? : Value = Nil,
) -> Value raise {
  cons(
    list1(q_mlist),
    mapcar(
      x => new_disrep(x),
      polysmp__grobner_monomials(variables, n, replacements, reset),
    ),
  )
}

///|
fn d_list_relations(l : Value) -> Value raise {
  let c = Collector::new()
  for v in l.iter() {
    if d_listp(v).truthy() {
      c.append_list(cdr(d_list_relations(cdr(v))))
    } else if equal(caar(v), q_mequal) {
      c.add(sub_star(second(v), third(v)))
    } else {
      c.add(v)
    }
  }
  cons(list1(q_mlist), c.result())
}

///|
fn rat_degree(poly : Value, var_ : Value) -> Value raise {
  if numberp(poly) {
    Fix(0L)
  } else if eq(car(poly), var_) {
    second(poly)
  } else {
    let mut m : Value = Nil
    let mut r = cdr(poly)
    while r is Cons(_) {
      let x = rat_degree(cadr(r), var_)
      if m is Nil || num_gt(x, m) {
        m = x
      }
      r = cddr(r)
    }
    if m is Nil {
      Fix(0L)
    } else {
      m
    }
  }
}

///|
/// To do y-->y/u where u is earlier in the order and u is a poly.
fn rational_sub(poly : Value, var_ : Value, new_denom : Value) -> (Value, Value, Value) raise {
  let deg = rat_degree(poly, var_)
  let poly = copy_tree(poly)
  rational_sub1(poly, var_, new_denom, deg) |> ignore
  (poly, new_denom, deg)
}

///|
fn rational_sub1(
  poly : Value,
  var_ : Value,
  new_denom : Value,
  degree : Value,
) -> Value raise {
  let mut poly = poly
  if atom(poly) {
    poly = ptimes(poly, pexpt(new_denom, degree))
  } else if eq(car(poly), var_) {
    let mut tail = cdr(poly)
    while tail is Cons(_) {
      let deg = car(tail)
      let cof = cadr(tail)
      setf_car(cdr(tail), ptimes(cof, pexpt(new_denom, num_sub(degree, deg))))
      |> ignore
      tail = cddr(tail)
    }
  } else {
    let mut tail = cdr(poly)
    while tail is Cons(_) {
      setf_car(cdr(tail), rational_sub1(second(tail), var_, new_denom, degree))
      |> ignore
      tail = cddr(tail)
    }
  }
  poly
}

///|
/// polysmp.lisp defines $te twice (and polyb.lisp before it); the last
/// definition, $te (poly var), is the one in effect: REPL is ignored.
fn d_te(poly : Value, var_ : Value, repl : Value) -> Value raise {
  ignore(repl)
  rat_degree(num(new_rat(poly)), caar(new_rat(var_)))
}

///|
fn d_contract_to_variables(
  a_list : Value,
  upto_variable : Value,
  before_var? : Value = Nil,
) -> Value raise {
  check_arg(a_list, q_d_listp, list1(Str("Macsyma list"))) |> ignore
  let before_var = if before_var is Nil {
    num_add(symbol_value(get_genvar(upto_variable)), Flo(0.5))
  } else {
    symbol_value(get_genvar(before_var))
  }
  let llist = Collector::new()
  for v in cdr(a_list).iter() {
    let mut tem : Value = Nil
    let typ = poly_type(v)
    if eq(typ, q_kw_polynomial) {
      tem = car(v)
    } else if eq(typ, q_kw_rational_function) {
      tem = caar(v)
    } else if eq(typ, polybas__kw_drat) {
      tem = caadr(v)
    }
    if num_gt(before_var, symbol_value(tem)) {
      tem = v
    } else {
      tem = Nil
    }
    if tem.truthy() {
      llist.add(tem)
    }
  }
  cons(list1(q_mlist), llist.result())
}

///|
fn st_rat(x : Value) -> Value raise {
  if listp(x) && listp(car(x)) && mbagp(x).truthy() {
    mapcar(y => st_rat1(y), cdr(x))
  } else {
    st_rat1(x)
  }
}

///|
fn st_rat1(x : Value) -> Value raise {
  if affine_polynomialp(x).truthy() {
    x
  } else if rational_functionp(x).truthy() {
    if eql(denom(x), Fix(1L)) {
      num(x)
    } else {
      x
    }
  } else if d_ratp(x).truthy() {
    if numberp(num(cdr(x))) {
      st_rat(cdr(x))
    } else if memq(caadr(x), symval(q_ear_genvar)).truthy() {
      st_rat(cdr(x))
    } else {
      st_rat(d_totaldisrep(x))
    }
  } else {
    st_rat(new_rat(x))
  }
}

///|
fn get_genvar(var_ : Value) -> Value raise {
  caar(new_rat(var_))
}

///|
/// Thus h is in ideal1 ^R ideal2 iff h is in ideal1*zz+ideal2*(1-zz).
/// Returns the grobner basis of the intersection of the ideals generated
/// by the two lists ideal1 and ideal2.
fn d_ideal_intersection(ideal1 : Value, ideal2 : Value) -> Value raise {
  check_arg(ideal1, q_d_listp, list1(Str("macsyma list"))) |> ignore
  let new_var = Value::Sym(intern("zzzzz1"))
  let gen = get_genvar(new_var)
  ignore(gen)
  let basis = append(
    mapcar(w => n_star(list2(new_var, w)), cdr(ideal1)),
    mapcar(w => n_star(list2(n__(Fix(1L), new_var), w)), cdr(ideal2)),
  )
  let basis = d_grobner_basis(cons(list1(q_mlist), basis))
  d_contract_to_variables(basis, Nil, before_var=new_var)
}

///|
fn d_grobner_basis_of_slice(slices : Value, original_relations : Value) -> Value raise {
  check_arg(slices, q_d_listp, list1(Str("macsyma list"))) |> ignore
  check_arg(original_relations, q_d_listp, list1(Str("macsyma list"))) |> ignore
  let mut relats = append(
    mapcar(u => bring_to_left_side(u), cdr(slices)),
    cdr(original_relations),
  )
  relats = cons(list1(q_mlist), relats)
  displa(relats) |> ignore
  d_grobner_basis(relats)
}

///|
fn display(expr : Value) -> Value raise {
  if atom(expr) {
    displa(expr)
  } else if affine_polynomialp(expr).truthy() ||
    rational_functionp(expr).truthy() {
    sh(expr)
  } else if affine_polynomialp(car(expr)).truthy() ||
    rational_functionp(car(expr)).truthy() {
    for v in expr.iter() {
      display(v) |> ignore
    }
    Nil
  } else {
    displa(expr)
  }
}

///|
fn ldata_simplifications_write(
  ldata : Value,
  open_g? : Value = Fix(1L),
  pathname? : Value = Str("haskell:>wfs>answer.lisp"),
) -> Value raise {
  let answ = ldata_simplifications(ldata, open_g~)
  let text = with_output_to_string(st => {
    with_specials(
      [(standard_output, st), (q_ear_print_radix, Nil)],
      () => {
        // (for-editor (des answ))
        with_specials([(q_linel, Fix(75L)), (q_d_display2d, Nil)], () => {
          des(answ)
        })
        |> ignore
        format(st, "~%(setq (answ (rerat '~A)))", [answ])
      },
    )
    |> ignore
  })
  write_file(lstring(pathname), text)
  Nil
}

///|
fn init_share_polysmp() -> Unit raise {
  defun(
    q_grobner_monomials,
    args => polysmp__grobner_monomials(
      arg(args, 0),
      arg(args, 1),
      args.get(2),
      arg(args, 3),
    ),
    name="grobner-monomials",
  )
  defun(
    polysmp__q_grobner_bi_monomials,
    args => polysmp__grobner_bi_monomials(
      arg(args, 0),
      arg(args, 1),
      arg(args, 2),
      arg(args, 3),
      args.get(4),
      arg(args, 5),
    ),
    name="grobner-bi-monomials",
  )
  // DEFREMEMBER clears the memory and :dont-remember when it is loaded.
  for f in [q_grobner_monomials, polysmp__q_grobner_bi_monomials] {
    if get(f, q_kw_memory_table).truthy() {
      clrhash(get(f, q_kw_memory_table)) |> ignore
    }
    remprop(f, q_kw_dont_remember) |> ignore
  }
}

///|
let polysmp__q_grobner_bi_monomials : Value = sym("grobner-bi-monomials")
