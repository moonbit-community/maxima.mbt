// Translation of share/affine/modsimp.lisp: noncommutative products of
// affine polynomials and simplification in cyclic modules.

///|
/// (pv-the-sparse-matrix x): slot 13 of the POLYNOMIAL-VECTORS structure
/// (amacros.lisp), made with make_struct("polynomial-vectors", ...).
fn modsimp__pv_the_sparse_matrix(x : Value) -> Value raise {
  struct_ref(x, 13)
}

///|
/// The MSHOW macro of amacros.lisp.
fn modsimp__mshow(name : String, v : Value) -> Unit raise {
  format(t, "~%The value of ~A is.. ", [Str(name)]) |> ignore
  des(v) |> ignore
}

///|
/// The IASSERT macro of amacros.lisp.
fn modsimp__iassert(ok : Bool, form : String) -> Unit raise {
  if !ok {
    fsignal(list([Str("The expression ~A was not true"), Str(form)])) |> ignore
  }
}

///|
/// A call ($dotsimp x), through the function cell: after load(affine) it
/// holds ndotsimp.lisp's definition.
fn modsimp__dotsimp(x : Value) -> Value raise {
  funcall(q_d_dotsimp, [x])
}

///|
/// CL Y-OR-N-P: asks on *standard-output*, reads the answer from
/// *standard-input*.
fn modsimp__y_or_n_p(prompt : String) -> Bool raise {
  while true {
    format(t, "~%~A (y or n) ", [Str(prompt)]) |> ignore
    match read_line() {
      None => return false
      Some(line) => {
        let s = string_trim(" \t\r", line)
        match s {
          "y" | "Y" | "yes" | "YES" => return true
          "n" | "N" | "no" | "NO" => return false
          _ => format(t, "~%Please type \"y\" for yes or \"n\" for no.", [])
            |> ignore
        }
      }
    }
  }
  false
}

///|
fn nn_plus(l : Value) -> Value raise {
  if l is Nil {
    Fix(0L)
  } else if cddr(l).truthy() {
    n_plus(car(l), nn_plus(cdr(l)))
  } else {
    n_plus(car(l), cadr(l))
  }
}

///|
/// first three elements of a polynomial: (subseq p 0 3)
fn modsimp__first3(p : Value) -> Value raise {
  subseq(p, 0, end=3)
}

///|
/// a and b should be polynomials or rational-functions with the following
/// restrictions: Any noncommutative variables or monomials occur with
/// higher pointergp than any scalars.  A noncommutative polynomial looks
/// like ncprod-or-var*cof+ncpolynomial where cof is a scalar polynomial.
fn n_dot(a : Value, b : Value) -> Value raise {
  if numberp(a) {
    n_star(list([a, b]))
  } else if numberp(b) {
    n_star(list([a, b]))
  } else if atom(b) {
    n_dot(a, st_rat(b))
  } else if affine_polynomialp(a).truthy() {
    if affine_polynomialp(b).truthy() {
      let va = get(p__var(a), q_disrep)
      if d_scalarp(va).truthy() {
        ptimes(a, b)
      } else {
        let vb = get(p__var(b), q_disrep)
        if d_scalarp(vb).truthy() {
          ptimes(a, b)
        } else {
          if !(length(a) <= 5 && num_le(cadr(a), Fix(1L))) {
            raise LispError::SimpleError("an nc polynomial")
          }
          if !(length(b) <= 5 && num_le(cadr(b), Fix(1L))) {
            raise LispError::SimpleError("an nc polynomial")
          }
          let ncprod = add_newvar(ncmul2_star(va, vb)).0
          nn_plus(
            list([
              ptimes(
                list([ncprod, Fix(1L), Fix(1L)]),
                ptimes(caddr(a), caddr(b)),
              ),
              if cdddr(a).truthy() {
                n_dot(nth(4, a), modsimp__first3(b))
              } else {
                Fix(0L)
              },
              if cdddr(b).truthy() {
                n_dot(modsimp__first3(a), nth(4, b))
              } else {
                Fix(0L)
              },
              if cdddr(a).truthy() && cdddr(b).truthy() {
                n_dot(nth(4, a), nth(4, b))
              } else {
                Fix(0L)
              },
            ]),
          )
        }
      }
    } else if rational_functionp(b).truthy() {
      nred(n_dot(a, num(b)), denom(b))
    } else {
      n_dot(a, st_rat(b))
    }
  } else if rational_functionp(a).truthy() {
    nred(n_dot(num(a), b), denom(a))
  } else {
    n_dot(st_rat(a), b)
  }
}

///|
/// The first definition of $FIND_SYGY in modsimp.lisp (the declared
/// signature).  The file redefines it later with two arguments
/// (degn matrix); see the porting report.
fn d_find_sygy(degn : Value) -> Value raise {
  let mut monoms = d_mono(
    symval(q_d_current_variables),
    num_sub(degn, Fix(1L)),
  )
  let coll = Collector::new()
  for v in cdr(monoms).iter() {
    coll.add(ncmul2_star(v, q_d_x))
    coll.add(ncmul2_star(v, q_d_y))
  }
  monoms = cons(list1(q_mlist), coll.result())
  modsimp__mshow("MONOMS", monoms)
  let general_term = d_general_sum(monoms, coefficients=symval(q_d_aaaa)).0
  let mut simp = d_ratdisrep(modsimp__dotsimp(general_term))
  modsimp__mshow("SIMP", simp)
  modsimp__mshow("($LIST_NC_MONOMIALS SIMP)", d_list_nc_monomials(simp))
  simp = d_ratsimp(d_numerator(simp), Nil)
  let eqns = d_extract_linear_equations(list([list1(q_mlist), simp]))
  let sols = d_fast_linsolve(
    eqns,
    variables=d_list_variables(eqns, list1(Str("aa"))),
  )
  modsimp__mshow("EQNS", eqns)
  modsimp__mshow("SOLS", sols)
  d_separate_parameters(d_sublis(sols, general_term), Nil)
}

///|
/// (matrix-row mat n) ==> (nth n mat)
fn matrix_row(mat : Value, n : Value) -> Value raise {
  nth(to_int(n), mat)
}

///|
fn matrix_column(mat : Value, n : Value) -> Value raise {
  let i = to_int(n)
  cons(list1(q_mlist), mapcar(v => nth(i, v), cdr(mat)))
}

///|
/// $list_matrix_entries / list wrapping shared by the kernel finders.
fn modsimp__as_list(simp : Value) -> Value raise {
  if d_listp(simp).truthy() {
    simp
  } else if d_matrixp(simp).truthy() {
    d_list_matrix_entries(simp)
  } else {
    list([list1(q_mlist), simp])
  }
}

///|
/// if matrix is m x n then it finds the kernel of the MAPL on the right
/// multiplication B:A^m-->A^n v |---> vB or the kernel of the left
/// multiplication A^m <--- A^n:B Bv<----|v
fn d_find_kernel(
  in_deg : Value,
  matrix : Value,
  multiply_on_left? : Value = Nil,
) -> Value raise {
  let first = if multiply_on_left.truthy() {
    matrix_row(matrix, Fix(1L))
  } else {
    matrix_column(matrix, Fix(1L))
  }
  // in-deg refers to degree of image in 1-1 position
  let coll = Collector::new()
  let mut i = 1
  for u in cdr(first).iter() {
    coll.add(
      d_scalar_sum(
        d_concat(list([q_d_ff, int(i)])),
        d_mono(
          symval(q_d_current_variables),
          num_sub(in_deg, d_nc_degree(u)),
        ),
      ).0,
    )
    i += 1
  }
  let general_from = cons(list1(q_mlist), coll.result())
  modsimp__mshow("$GENERAL_FROM", general_from)
  let general_image = if multiply_on_left.truthy() {
    ncmul2_star(matrix, d_transpose(general_from))
  } else {
    ncmul2_star(general_from, matrix)
  }
  modsimp__mshow("GENERAL-IMAGE", general_image)
  let mut simp = d_ratdisrep(modsimp__dotsimp(general_image))
  let msk = symval(q_d_module_simp_for_kernel)
  if msk.truthy() {
    format(t, "~%Simplifying by ~A", [msk]) |> ignore
    simp = d_totaldisrep(funcall(msk, [simp]))
  }
  modsimp__mshow("SIMP", simp)
  simp = d_ratsimp(d_numerator(simp), Nil)
  simp = modsimp__as_list(simp)
  let eqns = d_extract_linear_equations(simp)
  let sols = d_fast_linsolve(
    eqns,
    variables=d_list_variables(eqns, list1(Str("ff"))),
  )
  modsimp__mshow("EQNS", eqns)
  modsimp__mshow("SOLS", sols)
  d_separate_parameters(
    d_sublis(sols, general_from),
    list([Str("par"), Str("ff")]),
  )
}

///|
fn d_find_basis(list_vectors : Value) -> Value raise {
  let sum = d_scalar_sum(q_d_aa, list_vectors).0
  let eqns = d_ratsimp(
    d_numerator(d_ratdisrep(modsimp__dotsimp(sum))),
    Nil,
  )
  let eqns = d_extract_linear_equations(eqns)
  let sols = d_fast_linsolve(
    eqns,
    variables=d_list_variables(eqns, list1(Str("aa"))),
  )
  let _rk = sp_number_of_pivots(
    modsimp__pv_the_sparse_matrix(symval(q_d_poly_vector)),
  )
  d_separate_parameters(d_sublis(sols, sum), list([Str("par"), Str("aa")]))
}

///|
fn d_scalar_sum(prefix : Value, monoms : Value) -> (Value, Value) raise {
  let n = to_int(d_length(monoms))
  let coll = Collector::new()
  for i in 0..<n {
    coll.add(d_concat(list([prefix, int(i)])))
  }
  let scal = cons(list1(q_mlist), coll.result())
  d_declare_scalar_list(scal) |> ignore
  (d_general_sum(monoms, coefficients=scal).0, scal)
}

///|
fn replace_parameters_by(expr : Value, prefix : Value) -> Value raise {
  let mut pars = cdr(d_list_variables(expr, list1(Str("par"))))
  let olds = d_list_variables(expr, list1(prefix))
  let repl = Collector::new()
  let mut i = 0
  while pars.truthy() {
    let tem = d_concat(list([prefix, int(i)]))
    if member_equal(tem, olds) is Nil {
      repl.add(cons(car(pars), tem))
      pars = cdr(pars)
    }
    i += 1
  }
  let repl = repl.result()
  if repl.truthy() {
    for v in repl.iter() {
      format(t, "~%Replacing ~A by ~A", [car(v), cdr(v)]) |> ignore
    }
    sublis(repl, expr)
  } else {
    expr
  }
}

///|
/// currently the module is a cyclic left module M=A/A.module-relations and
/// we test to find solutions for h of v.h-A.module-relations for v in rad
/// everything is supposed to be homogeneous
fn d_leftsocle(
  in_degree : Value,
  module_relations : Value,
  rad : Value,
) -> Value raise {
  let cv = symval(q_d_current_variables)
  let mut h = d_scalar_sum(q_d_bbb, d_mono(cv, in_degree)).0
  let relats = Collector::new()
  let mut i = 0
  for v in cdr(module_relations).iter() {
    let tem = d_scalar_sum(
      d_concat(list([q_d_ccc, int(i)])),
      d_mono(cv, num_add(Fix(1L), num_sub(in_degree, d_nc_degree(v)))),
    ).0
    relats.add(ncmul2_star(tem, v))
    i += 1
  }
  let allrelats = meval_star(cons(list1(q_mplus), relats.result()))
  modsimp__mshow("ALLRELATS", allrelats)
  let _monoms = d_mono(cv, in_degree)
  // impose condition x.h-general-sum module-relations
  let all_rel = num(new_rat(allrelats))
  let mut newh : Value = Nil
  for v in cdr(rad).iter() {
    let v = st_rat(v)
    let hh = n_dot(v, num(new_rat(h)))
    let mut condition = n__(hh, all_rel)
    condition = new_rat_dotsimp(cons(condition, Fix(1L)))
    displa(condition) |> ignore
    condition = d_totaldisrep(d_numerator(condition))
    let eqns = d_extract_linear_equations(list([list1(q_mlist), condition]))
    let vari = d_list_variables(eqns, list([Str("bbb"), Str("ccc")]))
    let solns = d_fast_linsolve(eqns, variables=vari)
    newh = d_ratsimp(d_sublis(solns, h), Nil)
    if d_zerop(newh).truthy() {
      return list1(list1(q_mlist))
    }
    h = replace_parameters_by(newh, q_d_bbb)
    displa(h) |> ignore
  }
  d_separate_parameters(newh, list([Str("bbb"), Str("par")]))
}

///|
/// solve f=f1*(z-a*x)+f2*(z-b*x),g=g1*(z-a*x)+g2*(z-b*x)
fn d_try_bezout(f : Value, g : Value, linears? : Value) -> Value raise {
  let linears = match linears {
    Some(l) => l
    None => maxima_lit("[z-a*x,y-b*x]")
  }
  let deg = d_nc_degree(f)
  let cv = symval(q_d_current_variables)
  let cofs = Collector::new()
  for v in [q_f1, q_f2, q_g1, q_g2] {
    let tem = d_scalar_sum(
      d_concat(list([q_d_ccc, v])),
      d_mono(cv, num_sub(deg, Fix(1L))),
    ).0
    cofs.add(tem)
  }
  let cofs = cofs.result()
  let eqns = Collector::new()
  let mut c = cofs
  let mut ffs = list([f, g])
  while c is Cons(_) && ffs is Cons(_) {
    let aa = car(c)
    let bb = cadr(c)
    let ff = car(ffs)
    let mut eqn = ff
    let mut lins = cdr(linears)
    let mut acofs = list([aa, bb])
    while lins is Cons(_) && acofs is Cons(_) {
      eqn = sub_star(eqn, ncmul2_star(car(acofs), car(lins)))
      lins = cdr(lins)
      acofs = cdr(acofs)
    }
    eqns.add(eqn)
    c = cddr(c)
    ffs = cdr(ffs)
  }
  let eqns = mapcar(v => d_ratdisrep(modsimp__dotsimp(v)), eqns.result())
  let cof_eqns = d_extract_linear_equations(
    cons(list1(q_mlist), eqns),
    independent_monomials=d_mono(cv, deg),
  )
  modsimp__mshow("COF-EQNS", cof_eqns)
  let answ = d_fast_linsolve(
    cof_eqns,
    variables=d_list_variables(cof_eqns, list1(Str("cc"))),
  )
  let det = sp_determinant(
    modsimp__pv_the_sparse_matrix(symval(q_d_poly_vector)),
  )
  list([list1(q_mlist), answ, new_disrep(det)])
}

///|
/// Af1 intersect f2A yielding g1.f1=f2.g2, and returns a equations..
fn d_intersect_principals_variety(
  d_f1 : Value,
  d_f2 : Value,
  in_deg : Value,
  in_free_ring? : Value = Nil,
) -> Value raise {
  with_specials(
    [(q_d_f1, d_f1), (q_d_f2, d_f2), (q_d_g1, Nil), (q_d_g2, Nil)],
    () => {
      let cv = symval(q_d_current_variables)
      set(
        q_d_g1,
        d_scalar_sum(
          q_d_gg1,
          d_mono(cv, num_sub(in_deg, d_nc_degree(symval(q_d_f1)))),
        ).0,
      )
      |> ignore
      set(
        q_d_g2,
        d_scalar_sum(
          q_d_gg2,
          d_mono(cv, num_sub(in_deg, d_nc_degree(symval(q_d_f2)))),
        ).0,
      )
      |> ignore
      let mut eqn = maxima_lit("[g1.f1-f2.g2]")
      if !in_free_ring.truthy() {
        eqn = d_totaldisrep(modsimp__dotsimp(eqn))
      }
      d_extract_linear_equations(eqn)
    },
  )
}

///|
/// Af1 intersect f2A yielding g1.f1=f2.g2, and returns a
/// matrix([g1,g2],[g1p,g2p],...)
fn d_intersect_principals(
  d_f1 : Value,
  d_f2 : Value,
  in_deg : Value,
  modulo_free_ring? : Value = Nil,
) -> Value raise {
  with_specials(
    [(q_d_f1, d_f1), (q_d_f2, d_f2), (q_d_g1, Nil), (q_d_g2, Nil)],
    () => {
      if modulo_free_ring.truthy() {
        let mut free_result = with_special(q_d_dot_simplifications, Nil, () => d_intersect_principals(
          symval(q_d_f1),
          symval(q_d_f2),
          in_deg,
        ))
        free_result = d_totaldisrep(modsimp__dotsimp(free_result))
        let result = d_intersect_principals(
          symval(q_d_f1),
          symval(q_d_f2),
          in_deg,
        )
        d_nc_matrix_quotient(result, free_result)
      } else {
        let cv = symval(q_d_current_variables)
        set(
          q_d_g1,
          d_scalar_sum(
            q_d_gg1,
            d_mono(cv, num_sub(in_deg, d_nc_degree(symval(q_d_f1)))),
          ).0,
        )
        |> ignore
        set(
          q_d_g2,
          d_scalar_sum(
            q_d_gg2,
            d_mono(cv, num_sub(in_deg, d_nc_degree(symval(q_d_f2)))),
          ).0,
        )
        |> ignore
        let eqn = maxima_lit("totaldisrep(dotsimp([g1.f1-f2.g2]))")
        modsimp__mshow("EQN", eqn)
        let eqns = d_extract_linear_equations(eqn)
        set(q_d_eqns, eqns) |> ignore
        let solns = d_fast_linsolve(
          eqns,
          variables=d_list_variables(eqns, list1(Str("gg"))),
        )
        let result = d_sublis(solns, maxima_lit("[g1,g2]"))
        cons(
          list1(q_d_matrix),
          cdr(d_separate_parameters(result, list([Str("par"), Str("gg")]))),
        )
      }
    },
  )
}

///|
fn module_monom_must_replacep(monom : Value) -> Value raise {
  let ms = symval(q_d_module_simplifications)
  if atom(monom) {
    let repl = memq(monom, cdr(ms))
    if repl.truthy() {
      list([monom, cadr(repl)])
    } else {
      Nil
    }
  } else {
    let leng = length(monom)
    let mut v = cdr(ms)
    while v is Cons(_) {
      let cv = car(v)
      let hit = (cv is Nil || cv is Cons(_)) &&
        {
          let leng_first_v = length(cv)
          leng >= leng_first_v &&
          equal(nthcdr(leng - leng_first_v, cdr(monom)), cdr(cv))
        } ||
        eql(cv, nth(length(monom) - 1, monom))
      if hit {
        let s = cadr(v)
        return list([cv, if numberp(s) { s } else { cdr(s) }])
      }
      v = cddr(v)
    }
    Nil
  }
}

///|
fn module_must_replacep(poly : Value) -> Value raise {
  let mut poly = poly
  while poly.truthy() {
    if atom(poly) {
      return Nil
    }
    let monom = get(car(poly), q_disrep)
    if module_monom_must_replacep(monom).truthy() {
      return cons(car(poly), module_monom_must_replacep(monom))
    }
    poly = nth(4, poly)
  }
  Nil
}

///|
fn rat_simplifications(simps : Value) -> Value raise {
  let coll = Collector::new()
  let mut tail = cdr(simps)
  while tail is Cons(_) {
    let mon = car(tail)
    let rep = cadr(tail)
    coll.add(mon)
    coll.add(cons(symval(q_ear_fake_rat), new_rat(rep)))
    tail = cddr(tail)
  }
  cons(list1(q_mlist), coll.result())
}

///|
/// argument satisfies rational-functionp
fn module_simp(fun : Value) -> Value raise {
  let mut num_fun : Value = Nil
  let mut den_fun : Value = Nil
  if affine_polynomialp(fun).truthy() {
    num_fun = fun
    den_fun = Fix(1L)
  } else if rational_functionp(fun).truthy() {
    num_fun = car(fun)
    den_fun = cdr(fun)
  } else {
    fsignal(list1(Str("takes poly or rat'l function for argument"))) |> ignore
  }
  let mut did_replace = false
  while true {
    let repl_data = module_must_replacep(num_fun)
    if repl_data is Nil {
      break
    }
    let symbo = car(repl_data)
    let mon = cadr(repl_data)
    let repl = caddr(repl_data)
    let prev_mon = get(symbo, q_disrep)
    did_replace = true
    let lft = dot_right_quotient(prev_mon, mon)
    let actual_repl = n_dot(st_rat(lft), repl)
    let mut num_repl : Value = Nil
    let mut den : Value = Nil
    if affine_polynomialp(actual_repl).truthy() {
      num_repl = actual_repl
      den = Fix(1L)
    } else if rational_functionp(actual_repl).truthy() {
      num_repl = car(actual_repl)
      den = cdr(actual_repl)
    } else {
      fsignal(list1(Str("bad repl"))) |> ignore
    }
    format(t, "~%Module simp replacing ~A", [get(symbo, q_disrep)]) |> ignore
    num_fun = psublis(list1(cons(symbo, num_repl)), den, num_fun)
    den_fun = n_star(list([den, den_fun]))
  }
  if did_replace {
    ratreduce(num_fun, den_fun)
  } else {
    fun
  }
}

///|
fn delete_from_simps(simps : Value, mon : Value, repl : Value) -> Value raise {
  let mut tem : Value = Nil
  let mut v = cdr(simps)
  while v is Cons(_) {
    if equal(car(v), mon) && equal(cadr(v), repl) {
      return cons(list1(q_mlist), nconc(tem, cddr(v)))
    } else {
      tem = nconc(tem, subseq(v, 0, end=2))
    }
    v = cdr(v)
  }
  Nil
}

///|
fn make_relation(monom : Value, repl : Value) -> Value raise {
  let mut repl = repl
  if numberp(repl) {
    ()
  } else if affine_polynomialp(repl).truthy() {
    repl = cons(repl, Fix(1L))
  } else if rational_functionp(repl).truthy() {
    ()
  } else if eql(caar(repl), q_mrat) {
    repl = cdr(repl)
  } else {
    fsignal(list1(Str("bad repl"))) |> ignore
  }
  function_numerator(n__(monom, repl))
}

///|
fn sort_simps_by_degree(simps : Value) -> Value raise {
  let pred = lfunc("sort-simps-by-degree", args => {
    let u = arg(args, 0)
    let v = arg(args, 1)
    if atom(u) {
      t
    } else if atom(v) {
      Nil
    } else if length(u) < length(v) {
      t
    } else if length(u) > length(v) {
      Nil
    } else {
      funcall(symval(q_d_order_function), [v, u])
    }
  })
  cons(car(simps), sort_grouped_list(cdr(simps), Fix(2L), pred))
}

///|
fn module_and_dot_simp(pol : Value) -> Value raise {
  let mut pol = pol
  let mut changed = true
  while true {
    if module_must_replacep(pol).truthy() {
      pol = module_simp(pol)
      changed = true
    }
    if d_must_replacep(pol).truthy() {
      pol = cdr(new_rat_dotsimp(pol))
      changed = true
    }
    if !changed {
      break
    }
  }
  pol
}

///|
/// simplifier should return a polynomial or rational function
fn gen_dot_check_associative(
  a : Value,
  b : Value,
  c : Value,
  simplifier? : Value = q_module_and_dot_simp,
) -> Value raise {
  let answ = n__(
    n_dot(funcall(simplifier, [n_dot(a, b)]), c),
    n_dot(a, funcall(simplifier, [a, b])),
  )
  if pzerop(answ).truthy() {
    format(t, "~%It was associative", [])
  } else {
    answ
  }
}

///|
/// nil-->1, '(a) -->a '(x y z) --> x.y.z , x.y--> x.y
fn coerce_nctimes(a : Value) -> Value raise {
  if a is Nil {
    Fix(1L)
  } else if a is Cons(_) {
    if car(a) is Cons(_) || car(a) is Nil {
      if eql(caar(a), q_mnctimes) {
        if cdr(a) is Nil {
          Fix(1L)
        } else if cddr(a).truthy() {
          a
        } else {
          cadr(a)
        }
      } else {
        fsignal(list1(Str("what am i like?")))
      }
    } else if cdr(a) is Nil {
      car(a)
    } else {
      cons(list1(q_mnctimes), a)
    }
  } else {
    a
  }
}

///|
/// Returns an final segment of mon of degree n if possible, otherwise nil
fn d_lastn_ncdegree(mon : Value, n : Value) -> Value raise {
  if zerop(n) {
    Fix(1L)
  } else if atom(mon) {
    if equal(d_nc_degree(mon), n) {
      mon
    } else {
      Nil
    }
  } else {
    let mut tot : Value = Fix(0L)
    let mut i = length(mon) - 1
    while i >= 1 {
      let u = nth(i, mon)
      tot = num_add(tot, d_nc_degree(u))
      if num_ge(tot, n) {
        if eql(tot, n) {
          return coerce_nctimes(nthcdr(i, mon))
        } else {
          return Nil
        }
      }
      i -= 1
    }
    Nil
  }
}

///|
/// Returns an initial segment of mon of degree n if possible, otherwise nil
fn d_firstn_ncdegree(mon : Value, n : Value) -> Value raise {
  if zerop(n) {
    Fix(1L)
  } else if atom(mon) {
    if equal(d_nc_degree(mon), n) {
      mon
    } else {
      Nil
    }
  } else {
    let mut tot : Value = Fix(0L)
    let mut i = 2
    for u in cdr(mon).iter() {
      tot = num_add(tot, d_nc_degree(u))
      if num_ge(tot, n) {
        if eql(tot, n) {
          return coerce_nctimes(subseq(mon, 0, end=i))
        } else {
          return Nil
        }
      }
      i += 1
    }
    Nil
  }
}

///|
/// tot-deg is the degree of the lapped left and right. It will not catch
/// left a subset of right since it is presumed the right is in reduced form.
/// (The second definition in modsimp.lisp, which is the one in effect.)
fn d_find_right_lap(left : Value, right : Value, tot_deg : Value) -> Value raise {
  let ld = d_nc_degree(left)
  let rd = d_nc_degree(right)
  let size_lap = num_sub(num_add(ld, rd), tot_deg)
  if num_le(size_lap, Fix(0L)) {
    Nil
  } else {
    let a_lap = d_lastn_ncdegree(left, size_lap)
    let lap_list = a_lap is Nil || a_lap is Cons(_)
    let right_list = right is Nil || right is Cons(_)
    if a_lap.truthy() &&
      (
        equal(a_lap, right) ||
        (lap_list && right_list && initial_seg(cdr(a_lap), cdr(right)).0.truthy()) ||
        (atom(a_lap) && right_list && equal(cadr(right), a_lap))
      ) {
      list([
        d_firstn_ncdegree(left, num_sub(ld, size_lap)),
        a_lap,
        d_lastn_ncdegree(right, num_sub(rd, size_lap)),
      ])
    } else {
      Nil
    }
  }
}

///|
/// '(1 2) '(1 2 3) --> values: t '(3), '(1 2) '(0 1 2 3) --> nil,
/// '(1 2) '(1) --> nil
fn initial_seg(seg : Value, lis : Value) -> (Value, Value) raise {
  let mut seg = seg
  let mut lis = lis
  while true {
    if !eql(car(seg), car(lis)) {
      return (Nil, Nil)
    }
    lis = cdr(lis)
    seg = cdr(seg)
    if seg is Nil {
      return (t, lis)
    }
    if lis is Nil {
      return (Nil, Nil)
    }
  }
  (Nil, Nil)
}

///|
fn plain_add_to_module_simps(poly : Value) -> Value raise {
  if symval(q_d_module_simplifications).truthy() {
    ()
  } else {
    set(q_d_module_simplifications, list1(list1(q_mlist))) |> ignore
  }
  set(
    q_d_module_simplifications,
    append(
      symval(q_d_module_simplifications),
      make_simp(function_numerator(poly)),
    ),
  )
}

///|
/// inverse of make-relation, except that constants will be cancelled.
fn make_simp(relat : Value) -> Value raise {
  if numberp(relat) {
    if zerop(relat) {
      Nil
    } else {
      list([Fix(1L), Fix(0L)])
    }
  } else {
    let fifth = nth(4, relat)
    list([
      get(car(relat), q_disrep),
      if fifth.truthy() {
        cons(
          symval(q_ear_fake_rat),
          ratreduce(pminus(fifth), caddr(relat)),
        )
      } else {
        Fix(0L)
      },
    ])
  }
}

///|
/// a.b^^-1 with error if b not final segment
fn dot_right_quotient(a : Value, b : Value) -> Value raise {
  let mut answ : Value = Nil
  if atom(b) {
    if atom(a) {
      if eql(a, b) {
        ()
      } else {
        fsignal(list1(Str("doesn't divide evenly"))) |> ignore
      }
    } else if equal(car(last(a)), b) {
      answ = butlast(a)
    } else {
      fsignal(list1(Str("not tail"))) |> ignore
    }
  } else {
    let tem = 1 + (length(a) - length(b))
    let mut vs = cdr(b)
    let mut ws = nthcdr(tem, a)
    while vs is Cons(_) && ws is Cons(_) {
      if !equal(car(vs), car(ws)) {
        fsignal(list1(Str("b is not a tail of a"))) |> ignore
      }
      vs = cdr(vs)
      ws = cdr(ws)
    }
    answ = subseq(a, 0, end=tem)
  }
  if cddr(answ).truthy() {
    answ
  } else if cdr(answ).truthy() {
    cadr(answ)
  } else {
    Fix(1L)
  }
}

///|
fn simplify_module_simps(to_deg : Value) -> Value raise {
  with_special(q_present_deg, Fix(0L), () => {
    // (user-supply *module-overlaps-checked*)
    set(
      q_ear_module_overlaps_checked,
      user_supply1(
        q_ear_module_overlaps_checked,
        symval(q_ear_module_overlaps_checked),
      ),
    )
    |> ignore
    while true {
      let mut changed : Value = Nil
      for f in [0, 1] {
        let (new_simps, ch) = if f == 0 {
          type_i_simp(list([symval(q_present_deg), to_deg]))
        } else {
          type_ii_simp(symval(q_present_deg), to_deg)
        }
        changed = ch
        set(q_d_module_simplifications, new_simps) |> ignore
        if changed.truthy() {
          break
        }
      }
      if changed is Nil {
        break
      }
    }
    symval(q_d_module_simplifications)
  })
}

///|
/// eliminate simps such that one leading term is a left multiple of
/// another, ie common right overlap
fn type_i_simp(ignore_ : Value) -> (Value, Value) raise {
  ignore(ignore_)
  let old_simps = sort_simps_by_degree(symval(q_d_module_simplifications))
  set(q_d_module_simplifications, old_simps) |> ignore
  let mut tail_simps = cdr(old_simps)
  let mut i = 3
  while tail_simps is Cons(_) {
    let b = bind(
      q_d_module_simplifications,
      cons(list1(q_mlist), subseq(tail_simps, 0, end=2)),
    )
    defer unbind(b)
    let mut rest_ = cddr(tail_simps)
    let mut jj = i + 2
    while rest_ is Cons(_) {
      let mon = car(rest_)
      let repl = cadr(rest_)
      if module_monom_must_replacep(mon).truthy() ||
        (
          (repl is Nil || repl is Cons(_)) &&
          module_must_replacep(function_numerator(cdr(repl))).truthy()
        ) {
        let relat = make_relation(mon, repl)
        let mut new_relat = module_simp(relat)
        new_relat = new_rat_dotsimp(new_relat)
        if numberp(new_relat) {
          ()
        } else {
          new_relat = cdr(new_relat)
          modsimp__iassert(
            rational_functionp(new_relat).truthy(),
            "(RATIONAL-FUNCTIONP NEW-RELAT)",
          )
          new_relat = num(new_relat)
        }
        return (
          nconc(
            subseq(old_simps, 0, end=jj - 2),
            nconc(make_simp(new_relat), nthcdr(jj, old_simps)),
          ),
          t,
        )
      }
      rest_ = cddr(rest_)
      jj += 2
    }
    return (old_simps, Nil)
  }
  (Nil, Nil)
}

///|
fn dotsimp(ratl_or_poly : Value) -> Value raise {
  new_rat(new_rat_dotsimp(ratl_or_poly))
}

///|
fn ratl_function_id(number_or_rational_function : Value) -> Value raise {
  let x = number_or_rational_function
  if affine_polynomialp(x).truthy() {
    x
  } else if rational_functionp(x).truthy() {
    x
  } else if (x is Nil || x is Cons(_)) &&
    {
      let tem = car(x)
      (tem is Nil || tem is Cons(_)) && eql(car(tem), q_mrat)
    } {
    cdr(x)
  } else {
    fsignal(list1(Str("not right type")))
  }
}

///|
/// checks overlaps of type (a b c) where a.b is a dotsimp and b.c is a
/// modsimp and deg(a.b.c)<=i then replacement(a.b).c is a module relation
/// to be added.
fn type_ii_simp(from_deg : Value, to_deg : Value) -> (Value, Value) raise {
  let old_simps = sort_simps_by_degree(symval(q_d_module_simplifications))
  set(q_d_module_simplifications, old_simps) |> ignore
  let mut i = from_deg
  while num_le(i, to_deg) {
    // (block sue ...)
    set(q_present_deg, i) |> ignore
    let mut dtail = cdr(symval(q_d_dot_simplifications))
    let mut sue = false
    while dtail is Cons(_) && !sue {
      let mon = car(dtail)
      let repl = cadr(dtail)
      let mut mtail = cdr(old_simps)
      while mtail is Cons(_) {
        let monmod = car(mtail)
        let repmod = cadr(mtail)
        let tem = d_find_right_lap(mon, monmod, i)
        if tem.truthy() {
          let tem1 = cons(mon, monmod)
          if member_equal(tem1, symval(q_ear_module_overlaps_checked)) is Nil {
            set(
              q_ear_module_overlaps_checked,
              cons(tem1, symval(q_ear_module_overlaps_checked)),
            )
            |> ignore
            modsimp__iassert(
              nc_equal(ncmul2_star(car(tem), cadr(tem)), mon).truthy(),
              "(NC-EQUAL (NCMUL* (FIRST TEM) (SECOND TEM)) MON)",
            )
            modsimp__iassert(
              nc_equal(ncmul2_star(cadr(tem), caddr(tem)), monmod).truthy(),
              "(NC-EQUAL (NCMUL* (SECOND TEM) (THIRD TEM)) MONMOD)",
            )
            modsimp__iassert(
              nc_equal(d_nc_degree(ncmul2_star(mon, caddr(tem))), i).truthy(),
              "(NC-EQUAL ($NC_DEGREE (NCMUL* MON (THIRD TEM))) I)",
            )
            modsimp__iassert(
              !numberp(cadr(tem)),
              "(NOT (NUMBERP (SECOND TEM)))",
            )
            let a = car(tem)
            let c = caddr(tem)
            let mut new_repl = n__(
              n_dot(ratl_function_id(repl), c),
              n_dot(a, ratl_function_id(repmod)),
            )
            new_repl = dotsimp(new_repl)
            new_repl = function_numerator(new_repl)
            new_repl = function_numerator(module_simp(new_repl))
            modsimp__mshow("NEW-REPL", new_repl)
            mapcar(x => displa(x), make_simp(new_repl)) |> ignore
            if pzerop(new_repl).truthy() {
              ()
            } else {
              // (return-from sue (values ...)): leaves only the block,
              // the loop over degrees goes on.
              sue = true
              break
            }
          }
        }
        mtail = cddr(mtail)
      }
      dtail = cddr(dtail)
    }
    i = num_add(i, Fix(1L))
  }
  (old_simps, Nil)
}

///|
fn fake_header(form : Value) -> Value raise {
  if affine_polynomialp(form).truthy() {
    cons(symval(q_ear_fake_rat), cons(form, Fix(1L)))
  } else if rational_functionp(form).truthy() {
    cons(symval(q_ear_fake_rat), form)
  } else {
    fsignal(list1(Str("not poly or rat'l fun")))
  }
}

///|
fn d_modsimp(form : Value) -> Value raise {
  if atom(form) {
    fake_header(module_simp(new_rat(form)))
  } else if affine_polynomialp(form).truthy() ||
    rational_functionp(form).truthy() {
    fake_header(module_simp(form))
  } else if mbagp(form).truthy() {
    cons(car(form), mapcar(x => d_modsimp(x), cdr(form)))
  } else {
    fake_header(module_simp(new_rat(form)))
  }
}

///|
/// The second definition of $CYCLIC_MODULE_BASIS in modsimp.lisp (the
/// first one, using the DEFREMEMBER function CYCLIC-MODULE-BASIS, is
/// overridden at load time).
fn d_cyclic_module_basis(degree : Value, variables? : Value) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  let coll = Collector::new()
  for v in cdr(d_mono(variables, degree)).iter() {
    if module_monom_must_replacep(v) is Nil {
      coll.add(v)
    }
  }
  cons(list1(q_mlist), coll.result())
}

///|
fn d_module_replacements(module_simps? : Value) -> Value raise {
  let module_simps = match module_simps {
    Some(v) => v
    None => symval(q_d_module_simplifications)
  }
  let coll = Collector::new()
  let mut tail = cdr(module_simps)
  while tail is Cons(_) {
    coll.add(car(tail))
    tail = cddr(tail)
  }
  cons(list1(q_mlist), coll.result())
}

///|
fn d_module_dimensions(to_n : Value, variables? : Value) -> Value raise {
  let variables = match variables {
    Some(v) => v
    None => symval(q_d_current_variables)
  }
  let dims = Collector::new()
  let mut tot : Value = Fix(0L)
  let mut i : Value = Fix(0L)
  while num_le(i, to_n) {
    let tem = d_length(d_cyclic_module_basis(i, variables~))
    dims.add(tem)
    tot = num_add(tot, tem)
    format(t, "~%The dimension of the cyclic module in deg ~A is ~A.", [
      i, tem,
    ])
    |> ignore
    i = num_add(i, Fix(1L))
  }
  format(t, "~%The total dimension through degree ~A is ~A.", [to_n, tot])
  |> ignore
  cons(list1(q_mlist), dims.result())
}

///|
fn d_set_up_module_simplifications(
  relations : Value,
  to_deg? : Value = Nil,
) -> Value raise {
  set(q_d_module_simplifications, Nil) |> ignore
  set(q_ear_module_overlaps_checked, Nil) |> ignore
  for v in st_rat(relations).iter() {
    plain_add_to_module_simps(v) |> ignore
  }
  if to_deg.truthy() {
    simplify_module_simps(to_deg) |> ignore
  }
  symval(q_d_module_simplifications)
}

///|
/// shifts a sequence of degrees over by n to use for adding to check sums
fn d_shift_sequence(seq : Value, n : Value) -> Value raise {
  let k = to_int(num_abs(n))
  let tem = list(Array::make(k, Fix(0L)))
  if zerop(n) {
    seq
  } else if num_gt(n, Fix(0L)) {
    append(d_rest(seq, n~), tem)
  } else {
    d_append(list([cons(list1(q_mlist), tem), d_rest(seq, n~)]))
  }
}

///|
fn d_euler_sum(
  deg_seq : Value,
  size_of_module : Value,
  map_degs : Value,
) -> Value raise {
  let mut ans = deg_seq
  let mut tot : Value = Fix(0L)
  let mut vs = reverse(cdr(map_degs))
  let mut ss = cdr(size_of_module)
  let mut i = 1
  while vs is Cons(_) && ss is Cons(_) {
    let v = car(vs)
    let s = car(ss)
    tot = num_add(tot, v)
    modsimp__mshow("ANS", ans)
    if i % 2 == 0 {
      ans = add_star(
        list([ans, mul_star(list([s, d_shift_sequence(deg_seq, num_neg(tot))]))]),
      )
    } else {
      ans = sub_star(
        ans,
        mul_star(list([s, d_shift_sequence(deg_seq, num_neg(tot))])),
      )
    }
    vs = cdr(vs)
    ss = cdr(ss)
    i += 1
  }
  ans
}

///|
fn d_solve_sp(try_ : Value, eqns : Value) -> Value raise {
  let eqns = d_sublis(try_, eqns)
  // (make-ldata :eqns ...): a :type list :named structure
  // (ldata eqns inequality usedup open-inequality variables)
  let ld = list([
    q_ldata,
    mapcar(x => function_numerator(x), st_rat(eqns)),
    Fix(1L),
    Fix(0L),
    Fix(1L),
    Nil,
  ])
  des(ld) |> ignore
  let simp = simplify_ldata(ld)
  des(simp) |> ignore
  let syst = mapcar(
    u => cons(list1(q_mlist), mapcar(x => new_disrep(x), nth(1, u))),
    simp,
  )
  let solns = mapcar(
    v => d_append(list([try_, d_fast_linsolve(v, variables=d_list_variables(v, Nil))])),
    syst,
  )
  cons(list1(q_mlist), solns)
}

///|
fn d_nc_linear_factor(pol : Value) -> Value raise {
  let deg = d_nc_degree(pol)
  let cv = symval(q_d_current_variables)
  let lin = d_scalar_sum(q_d_bb, d_mono(cv, Fix(1L))).0
  let fac2 = d_scalar_sum(q_d_cc, d_mono(cv, num_sub(deg, Fix(1L)))).0
  let mut result = sub_star(pol, ncmul2_star(lin, fac2))
  result = modsimp__dotsimp(result)
  let eqns = d_extract_linear_equations(list([list1(q_mlist), result]))
  modsimp__mshow("EQNS", eqns)
  let mut answ : Value = Nil
  while true {
    format(t, "~%Supply a macsyma list of possible solns", []) |> ignore
    let try_ = mread_noprompt(Nil)
    modsimp__mshow("TRY", try_)
    let mut solns = d_solve_sp(try_, eqns)
    modsimp__mshow("SOLNS", solns)
    solns = d_ratsimp(solns, Nil)
    if !modsimp__y_or_n_p("Try again?") {
      let general = list([list1(q_mlist), lin, fac2])
      let coll = Collector::new()
      for v in cdr(solns).iter() {
        for x in cdr(
            d_separate_parameters(
              d_sublis(v, general),
              list([Str("bb"), Str("cc"), Str("par")]),
            ),
          ).iter() {
          coll.add(x)
        }
      }
      answ = cons(list1(q_mlist), coll.result())
      break
    }
  }
  if modsimp__y_or_n_p("Verify factors:?") {
    let mut i = 1
    for v in cdr(answ).iter() {
      let simp = modsimp__dotsimp(
        sub_star(
          pol,
          ncmul2_star(meval_star(cadr(v)), meval_star(caddr(v))),
        ),
      )
      if pzerop(simp).truthy() {
        format(t, "~%soln ~A is correct:", [int(i)]) |> ignore
        displa(
          list([
            list1(q_mequal),
            pol,
            cons(list1(q_mnctimes), cdr(v)),
          ]),
        )
        |> ignore
      } else {
        format(t, "~%soln ~A is not correct ****************", [int(i)])
        |> ignore
      }
      i += 1
    }
  }
  answ
}

///|
fn d_degless(u : Value, v : Value) -> Value raise {
  let u_deg = d_nc_degree(u)
  let v_deg = d_nc_degree(v)
  if num_lt(u_deg, v_deg) {
    t
  } else if eql(u_deg, v_deg) {
    funcall(symval(q_d_order_function), [u, v])
  } else {
    Nil
  }
}

///|
/// The second (live) definition of $FIND_SYGY in modsimp.lisp, which
/// replaces the first one when the file is loaded:
/// find_sygy(2,matrix([x],[y]))===> pq.  The declared D_FIND_SYGY has the
/// first definition's arity, so INIT_SHARE_MODSIMP installs this one in
/// the function cell of $FIND_SYGY.
fn modsimp__d_find_sygy2(degn : Value, matrix : Value) -> Value raise {
  let from_n = d_length(matrix)
  let _to_n = d_length(cadr(matrix))
  let monoms = d_mono(symval(q_d_current_variables), degn)
  let pref = Collector::new()
  let mut i : Value = Fix(1L)
  while num_le(i, from_n) {
    pref.add(d_concat(list([sym("$aa"), i])))
    i = one_plus(i)
  }
  let gf = Collector::new()
  for u in pref.result().iter() {
    let scal = Collector::new()
    let n = to_int(d_length(monoms))
    for k in 0..<n {
      scal.add(d_concat(list([u, int(k)])))
    }
    let scal = cons(list1(q_mlist), scal.result())
    d_declare_scalar_list(scal) |> ignore
    gf.add(d_general_sum(monoms, coefficients=scal).0)
  }
  let general_from = cons(list1(q_mlist), gf.result())
  modsimp__mshow("GENERAL-FROM", general_from)
  let general_image = ncmul2_star(general_from, matrix)
  modsimp__mshow("GENERAL-IMAGE", general_image)
  // (break t): CL's BREAK enters the Lisp debugger, which the port does
  // not have.
  raise LispError::SimpleError("break: T")
}

///|
fn init_share_modsimp() -> Unit raise {
  // The later definition of $FIND_SYGY (degn matrix) is the one in effect.
  defun(q_d_find_sygy, args => modsimp__d_find_sygy2(arg(args, 0), arg(args, 1)))
}
