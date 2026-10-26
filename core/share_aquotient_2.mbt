// Translation of share/affine/aquotient.lisp (part 2): rows, squaring,
// powers, Berlekamp and Hensel factorization, and the macros.

///|
/// The affine POLY-LENGTH (Grobner's poly-length has the declared name
/// POLY_LENGTH).
fn aquotient__poly_length(poly : Value) -> Value raise {
  if numberp(poly) {
    Fix(0L)
  } else {
    int(length(cdr(poly)))
  }
}

///|
fn poly_to_row(poly : Value, row? : Value = Nil) -> Value raise {
  let mut row = row
  if row.truthy() {
    if array_total_size(row) < length(poly) {
      let fp = fill_pointer(row)
      row = adjust_array(
        row,
        [10 + to_int(aquotient__poly_length(poly))],
        initial=Fix(0L),
      )
      set_fill_pointer(row, fp)
    }
  } else {
    let leng = to_int(aquotient__poly_length(poly))
    row = make_array([10 + leng], initial=Fix(0L), fill=0)
  }
  if numberp(poly) {
    sparsemat__vector_push(Fix(0L), row) |> ignore
    sparsemat__vector_push(poly, row) |> ignore
  } else {
    for u in cdr(poly).iter() {
      sparsemat__vector_push(u, row) |> ignore
    }
  }
  row
}

///|
/// SORT-GROUPED-ARRAY is a Lisp Machine function that Maxima does not
/// define.
fn row_to_terms(row : Value) -> Value raise {
  listarray(
    sparsemat__call_undefined(sparsemat__q_sort_grouped_array, [
      row,
      Fix(2L),
      sym(">"),
    ]),
  )
}

///|
fn afp_square(poly : Value) -> Value raise {
  if numberp(poly) {
    ctimes(poly, poly)
  } else {
    palgsimp(p__var(poly), afp_terms_square(p__terms(poly)), alg(poly))
  }
}

///|
fn afp_terms_square(p__terms : Value) -> Value raise {
  let mut p_terms = p__terms
  let mut orig_p2_terms : Value = Nil
  let mut p2_terms : Value = Nil
  let mut prod_exp : Value = Nil
  let mut prod_cof : Value = Nil
  let mut tail : Value = Nil
  let mut answ : Value = Nil
  // states: 0 begin, 1 tail-certain, 2 next-double-product,
  // 3 next-leading-square, 4 second-leading-square
  let mut state = 0
  while true {
    match state {
      0 =>
        if p_terms.truthy() {
          answ = afp_square(term_cof(p_terms))
          p2_terms = aquotient__plain_term_op(cddr(p_terms), Fix(2L), afp_pctimes)
          orig_p2_terms = p2_terms
          answ = aquotient__plain_term_op(
            p2_terms,
            term_cof(p_terms),
            afp_times,
            shift=term_deg(p_terms),
          )
          let lead = afp_square(term_cof(p_terms))
          if !pzerop(lead).truthy() {
            answ = cons(num_mul(Fix(2L), term_deg(p_terms)), cons(lead, answ))
          }
          if answ is Nil {
            p_terms = cddr(p_terms)
            p2_terms = cddr(p2_terms)
            state = 0
          } else {
            state = 4
          }
        } else {
          return Nil
        }
      1 =>
        // tail-certain: add in term to tail
        if cdr(tail).truthy() && num_gt(cadr(tail), prod_exp) {
          tail = cddr(tail)
          state = 1
        } else if cdr(tail) is Nil || num_lt(cadr(tail), prod_exp) {
          setf_cdr(tail, cons(prod_exp, cons(prod_cof, cdr(tail)))) |> ignore
          tail = cddr(tail)
          state = 2
        } else {
          prod_cof = pplus(caddr(tail), prod_cof)
          if pzerop(prod_cof).truthy() {
            setf_cdr(tail, cdddr(tail)) |> ignore
          } else {
            setf_car(cddr(tail), prod_cof) |> ignore
            tail = cddr(tail)
          }
          state = 2
        }
      2 => {
        // next-double-product
        p2_terms = cddr(p2_terms)
        if p2_terms is Nil {
          state = 3
          continue
        }
        prod_cof = afp_times(term_cof(p_terms), term_cof(p2_terms))
        if pzerop(prod_cof).truthy() {
          state = 2
          continue
        }
        prod_exp = num_add(term_deg(p_terms), term_deg(p2_terms))
        state = 1
      }
      3 => {
        // next-leading-square
        orig_p2_terms = cddr(orig_p2_terms)
        state = 4
      }
      _ => {
        // second-leading-square
        p_terms = cddr(p_terms)
        if p_terms is Nil {
          return answ
        }
        prod_cof = afp_square(term_cof(p_terms))
        p2_terms = orig_p2_terms
        tail = cdr(answ)
        if pzerop(prod_cof).truthy() {
          state = 2
          continue
        }
        prod_exp = num_mul(Fix(2L), term_deg(p_terms))
        state = 1
      }
    }
  }
  Nil
}

///|
fn afp_expt_modulo(poly : Value, exponent : Value, work_modulo : Value) -> Value raise {
  aquotient__working_modulo(work_modulo, () => afp_expt(poly, exponent))
}

///|
/// Raises the polynomial POLY to EXPONENT.  It never performs more than a
/// squaring before simplifying, so that if modulus or tellrat are in
/// effect, it will still be reasonable.
fn afp_expt(poly : Value, exponent : Value) -> Value raise {
  if eql(exponent, Fix(1L)) {
    poly
  } else if eql(exponent, Fix(0L)) {
    poly
  } else if num_lt(exponent, Fix(0L)) {
    merr("Use positive exponents", [])
  } else if numberp(poly) {
    cexpt(poly, exponent)
  } else if cdddr(poly).truthy() || alg(poly).truthy() {
    // main case
    let mut exponent = exponent
    let mut pow2 = poly
    let mut answer : Value = Fix(1L)
    while true {
      if oddp(exponent) {
        if eql(answer, Fix(1L)) {
          answer = pow2
        } else {
          answer = afp_times(answer, pow2)
        }
      }
      exponent = ash(exponent, -1)
      if zerop(exponent) {
        return answer
      }
      pow2 = afp_square(pow2)
    }
    Nil
  } else {
    // monomial of variable not tellrated
    let pow = afp_expt(p__cof(poly), exponent)
    if pzerop(pow).truthy() {
      Fix(0L)
    } else {
      psimp(p__var(poly), list([num_mul(p__deg(poly), exponent), pow]))
    }
  }
}

///|
/// Want to find sol'ns of v^p-v=0 (mod u).
fn berlekamp_set_up_and_reduce_matrix(u : Value, p : Value) -> Value raise {
  let du = to_int(p__deg(u))
  let rows = make_array([du], initial=Fix(0L), fill=du)
  with_specials([(q_modulus, p), (q_tellratlist, list1(u))], () => {
    let powers = aquotient__working_modulo(list1(u), () => {
      let pol = afp_expt(list([p__var(u), Fix(1L), Fix(1L)]), p)
      let mut pow : Value = Fix(1L)
      let belo = du - 1
      let c = Collector::new()
      let mut i = 0
      while true {
        c.add(pow)
        if !(i < belo) {
          break
        }
        if eql(pow, Fix(1L)) {
          pow = pol
        } else {
          pow = afp_times(pol, pow)
        }
        i = i + 1
      }
      c.result()
    })
    let mut count = 0
    let lim = if length(powers) > 5 { length(powers) } else { 5 }
    let mut i = 0
    let mut pp = powers
    while i < lim && pp is Cons(_) {
      let vv = car(pp)
      count = count + (if atom(vv) { 0 } else { length(vv) })
      i = i + 1
      pp = cdr(pp)
    }
    let estimated_size = 10 + to_int(quot(int(count), Fix(5L)))
    for i in 0..<fill_pointer(rows) {
      aset1(rows, i, make_array([estimated_size], initial=Fix(0L), fill=0))
      |> ignore
    }
    // putting the entries in the sparse matrix.  Each polynomial is a
    // column.
    let mut i = 1
    for vv in cdr(powers).iter() {
      if numberp(vv) {
        push_poly_number_deg_cof(rows, int(i), Fix(0L), vv) |> ignore
        push_poly_number_deg_cof(rows, int(i), int(i), Fix(-1L)) |> ignore
      } else {
        let mut subtracted_it = false
        let mut q = p__terms(vv)
        while q is Cons(_) {
          let deg = car(q)
          let mut cof = cadr(q)
          if eql(int(i), deg) {
            cof = num_sub(cof, Fix(1L))
            subtracted_it = true
          }
          if !zerop(cof) {
            push_poly_number_deg_cof(rows, int(i), deg, cof) |> ignore
          }
          q = p__next_term(q)
        }
        if !subtracted_it {
          push_poly_number_deg_cof(rows, int(i), int(i), Fix(-1L)) |> ignore
        }
      }
      i = i + 1
    }
    let sp = sparsemat__make_sparse_matrix()
    sparsemat__set_rows(sp, rows) |> ignore
    sparsemat__set_type_of_entries(sp, p) |> ignore
    sparsemat__set_columns_used_to_pivot(sp, make_hash_table(kind=Equal))
    |> ignore
    let cols = Collector::new()
    for i in 1..<du {
      cols.add(int(i))
    }
    sp_set_rows(sp, rows, list_of_columns=cols.result()) |> ignore
    sp_reduce(sp) |> ignore
    sp
  })
}

///|
fn berlekamp_polynomial_solutions(sp : Value, polynomial : Value) -> Value raise {
  sp_solve(sp) |> ignore
  let sp_sols = sparsemat__solutions(sp)
  // ROW-LENGTH calls the undefined ARRAY-DIMENSION-N.
  let n = to_int(row_length(sparsemat__rows(sp_sols)))
  let c = Collector::new()
  for i in 0..<n {
    c.add(
      psimp(
        p__var(polynomial),
        listarray(
          sparsemat__call_undefined(sparsemat__q_sort_grouped_array, [
            sp_row(sp_sols, int(i)),
            Fix(2L),
            sym(">"),
          ]),
        ),
      ),
    )
  }
  c.result()
}

///|
fn berlekamp_get_factors_little_prime(
  u : Value,
  reduced_sparse_matrix : Value,
  prime : Value,
) -> Value raise {
  let mut factor_list = list1(u)
  let number_of_factors = num_sub(
    p__deg(u),
    sp_number_of_pivots(reduced_sparse_matrix),
  )
  aquotient__show("NUMBER-OF-FACTORS", number_of_factors)
  sp_show_matrix(reduced_sparse_matrix) |> ignore
  if eql(Fix(1L), number_of_factors) {
    // irreducible
    factor_list
  } else {
    let b_polys = berlekamp_polynomial_solutions(reduced_sparse_matrix, u)
    let half_p = ash(prime, -1)
    for v in b_polys.iter() {
      let mut j = num_neg(half_p)
      while num_le(j, half_p) {
        let mut p = factor_list
        while p is Cons(_) {
          let u_fact = car(p)
          // make more efficient.
          let poly = pplus(v, j)
          let mut tem = afp_gcd(poly, u_fact)
          if !(numberp(tem) || eql(p__deg(tem), p__deg(u_fact))) {
            tem = afp_make_monic(tem)
            factor_list = cons(
              tem,
              cons(afp_quotient(u_fact, tem), remove_equal(u_fact, factor_list)),
            )
          }
          if eql(int(length(factor_list)), number_of_factors) {
            return factor_list
          }
          p = cdr(p)
        }
        j = one_plus(j)
      }
    }
    Nil
  }
}

///|
fn berlekamp_get_factors_big_prime(
  u : Value,
  reduced_sparse_matrix : Value,
  prime : Value,
) -> Value raise {
  let mut factor_list = list1(u)
  let number_of_factors = num_sub(
    p__deg(u),
    sp_number_of_pivots(reduced_sparse_matrix),
  )
  aquotient__show("NUMBER-OF-FACTORS", number_of_factors)
  if eql(Fix(1L), number_of_factors) {
    // irreducible
    factor_list
  } else {
    let b_polys = berlekamp_polynomial_solutions(reduced_sparse_matrix, u)
    let half_p = ash(prime, -1)
    while true {
      // added-factor
      if num_ge(int(length(factor_list)), number_of_factors) {
        return factor_list
      }
      let mut answ = afp_pctimes(
        car(b_polys),
        mt_random(num_max(Fix(500L), prime)),
      )
      for vv in cdr(b_polys).iter() {
        answ = pplus(answ, afp_pctimes(vv, mt_random(prime)))
      }
      let v = answ
      let pow = aquotient__working_modulo(list1(u), () => pdifference(
        afp_expt(v, half_p),
        Fix(1L),
      ))
      let c = Collector::new()
      for w in factor_list.iter() {
        let tem = afp_make_monic(afp_gcd(pow, w))
        if !(numberp(tem) || eql(p__deg(tem), p__deg(w))) {
          c.add(tem)
          c.add(afp_quotient(w, tem))
        } else {
          c.add(w)
        }
      }
      factor_list = c.result()
    }
    Nil
  }
}

///|
fn afp_make_monic(poly : Value) -> Value raise {
  if numberp(poly) {
    Fix(1L)
  } else if !(symval(q_modulus).truthy() ||
    eql(num_abs(p__cof(poly)), Fix(1L))) {
    merr("not finite modulus or unit coefficient", [])
  } else {
    let inv = crecip(p__cof(poly))
    afp_pctimes(poly, inv)
  }
}

///|
fn afp_try_make_monic(poly : Value) -> Value raise {
  if numberp(poly) {
    Fix(1L)
  } else if eql(p__cof(poly), Fix(1L)) {
    poly
  } else if eql(p__cof(poly), Fix(-1L)) {
    pminus(poly)
  } else if symval(q_modulus).truthy() {
    if numberp(p__cof(poly)) {
      afp_pctimes(poly, crecip(p__cof(poly)))
    } else {
      poly
    }
  } else {
    poly
  }
}

///|
fn afp_berlekamp_factor(pol : Value) -> Value raise {
  afp_berlekamp_factor1(
    pol,
    symval(q_modulus),
    use_little=lbool(num_le(symval(q_modulus), Fix(13L))),
  )
}

///|
fn afp_berlekamp_factor1(
  pol : Value,
  p : Value,
  use_little? : Value = Nil,
  use_big? : Value = Nil,
) -> Value raise {
  with_special(q_modulus, p, () => {
    let sp = berlekamp_set_up_and_reduce_matrix(pol, p)
    let answ = if use_big is Nil &&
      (use_little.truthy() || num_lt(p, Fix(13L))) {
      berlekamp_get_factors_little_prime(pol, sp, p)
    } else {
      berlekamp_get_factors_big_prime(pol, sp, p)
    }
    let mut ans : Value = Fix(1L)
    for v in answ.iter() {
      ans = ptimes(ans, v)
    }
    aquotient__show("ANS", ans)
    aquotient__iassert(equal(afp_mod(pol), ans))
    aquotient__show("ANSW", answ)
    mapcar(x => afp_mod(x), answ)
  })
}

///|
fn afp_factor(pol : Value, square_free_arg? : Value = Nil) -> Value raise {
  let mut pol = pol
  let mut lead : Value = Nil
  if symval(q_modulus).truthy() {
    lead = p__cof(pol)
    pol = afp_try_make_monic(pol)
  }
  let facts = if square_free_arg.truthy() {
    list([pol, Fix(1L)])
  } else {
    afp_square_free_factorization(pol)
  }
  let vars = list_variables(pol)
  let answ = if symval(q_modulus).truthy() {
    if cdr(vars).truthy() {
      fsignal(list1(q_not_univariate))
    } else {
      let factor_function = symval(q_ear_mod_p_factor)
      let mut const_ : Value = Fix(1L)
      let all = Collector::new()
      let mut p = facts
      while p is Cons(_) {
        let pol = car(p)
        let deg = cadr(p)
        if consp(pol) {
          for fa in funcall(factor_function, [pol]).iter() {
            all.add(fa)
            all.add(deg)
          }
        } else {
          const_ = ctimes(const_, pol)
          aquotient__iassert(eql(deg, Fix(1L)))
        }
        p = cddr(p)
      }
      const_ = num_mul(lead, const_)
      if !eql(const_, Fix(1L)) {
        cons(const_, cons(Fix(1L), all.result()))
      } else {
        all.result()
      }
    }
  } else {
    fsignal(list1(q_not_yet_without_modulus))
  }
  if symval(q_ear_sort_factors).truthy() {
    sort_grouped_list(answ, Fix(2L), q_alphagreatp)
  } else {
    answ
  }
}

///|
fn afp_mod(pol : Value) -> Value raise {
  afp_pctimes(pol, Fix(1L))
}

///|
fn get_factors(u : Value, use_for_gcd : Value, p : Value) -> Value raise {
  with_special(q_modulus, p, () => {
    let c = Collector::new()
    for w in use_for_gcd.iter() {
      let mut i : Value = Fix(0L)
      while num_lt(i, p) {
        let tem = afp_gcd(pplus(w, i), u)
        if !numberp(tem) {
          aquotient__show("I", i)
          c.add(monize(tem))
        }
        i = one_plus(i)
      }
    }
    c.result()
  })
}

///|
/// U should be univariate and square free.  Calculations are done modulo
/// PRIME.  It returns an alternating list of factors.
fn afp_distinct_degree_factor(u : Value, prime? : Value) -> Value raise {
  let prime = match prime {
    Some(p) => p
    None => symval(q_modulus)
  }
  let mut v = u
  let mut ww = list([p__var(u), Fix(1L), Fix(1L)])
  let mut d = 0
  with_special(q_modulus, prime, () => {
    let mon = ww
    let answ = Collector::new()
    let answer = while true {
      if numberp(v) {
        break answ.result()
      } else if num_gt(int(2 * (1 + d)), p__deg(v)) {
        break cons(v, answ.result())
      }
      d = d + 1
      let vv = v
      let www = ww
      ww = aquotient__working_modulo(list1(vv), () => afp_expt(www, prime))
      let gd = afp_gcd(pdifference(ww, mon), v)
      if consp(gd) && num_gt(int(d), p__deg(gd)) {
        fsignal(list1(q_big)) |> ignore
      }
      if !numberp(gd) {
        v = afp_quotient(v, gd)
        if consp(v) && consp(ww) {
          ww = palgsimp(p__var(v), cdr(ww), cdr(v))
        }
      }
      if !numberp(gd) {
        answ.append_list(
          copy_list(one_degree_factors(afp_try_make_monic(gd), int(d), prime)),
        )
      }
    } nobreak {
      Nil
    }
    let mut total : Value = Fix(0L)
    for v in answer.iter() {
      total = num_add(total, p__deg(v))
    }
    aquotient__iassert(eql(p__deg(u), total))
    answer
  })
}

///|
/// Assumes u has its irreducible factors of degree DEG and works modulo
/// P.  U should be univariate and square free.  The result is thus just a
/// list of the factors (powers are unnecessary).
fn one_degree_factors(u : Value, deg : Value, p : Value) -> Value raise {
  with_special(q_modulus, p, () => {
    let mut answ : Value = Nil
    aquotient__check_arg(oddp(p), "odd")
    if eql(p__deg(u), deg) {
      answ = list1(u)
    } else {
      let pow = quot(num_sub(expt(p, deg), Fix(1L)), Fix(2L))
      let mut facts = list1(u)
      let mut used_tt : Value = Nil
      let mut i = 1
      let mut finished = false
      while !finished {
        let mut tt : Value = Nil
        while true {
          tt = generate_t_for_one_degree_factors(u, deg, p, int(i))
          if !(numberp(tt) || member_equal(tt, used_tt).truthy()) {
            used_tt = cons(tt, used_tt)
            break
          }
        }
        let tt0 = tt
        tt = aquotient__working_modulo(list1(u), () => afp_expt(tt0, pow))
        let mut q = facts
        while q is Cons(_) {
          let v = car(q)
          let mut tem = afp_gcd(v, pplus(tt, Fix(1L)))
          if !(numberp(tem) || eql(p__deg(tem), p__deg(v))) {
            if eql(p__deg(tem), deg) {
              answ = cons(afp_make_monic(tem), answ)
            } else {
              facts = cons(tem, facts)
            }
            tem = afp_quotient(v, tem)
            if eql(p__deg(tem), deg) {
              answ = cons(afp_make_monic(tem), answ)
            } else {
              facts = cons(tem, facts)
            }
            facts = remove_equal(v, facts)
          }
          if facts is Nil {
            finished = true
            break
          }
          q = cdr(q)
        }
        i = i + 1
      }
    }
    if member(Fix(1L), answ).truthy() {
      fsignal(list1(q_bad)) |> ignore
    }
    let mut total : Value = Fix(0L)
    for pol in answ.iter() {
      if consp(pol) {
        total = num_add(total, p__deg(pol))
      }
    }
    aquotient__iassert(eql(p__deg(u), total))
    answ
  })
}

///|
fn generate_t_for_one_degree_factors(
  u : Value,
  deg : Value,
  p : Value,
  i : Value,
) -> Value raise {
  if num_lt(i, Fix(5L)) {
    list([p__var(u), Fix(1L), Fix(1L), Fix(0L), mt_random(p)])
  } else {
    let tem = num_add(
      Fix(1L),
      mt_random(num_sub(num_mul(Fix(2L), deg), Fix(1L))),
    )
    let c = Collector::new()
    let mut j = tem
    // make semi sparse
    while num_ge(j, Fix(0L)) {
      if evenp(mt_random(Fix(2L))) {
        c.add(j)
        c.add(num_add(Fix(1L), mt_random(num_sub(p, Fix(1L)))))
      }
      j = num_sub(j, Fix(1L))
    }
    psimp(p__var(u), c.result())
  }
}

///|
fn ff(u : Value, prime? : Value) -> Value raise {
  let prime = match prime {
    Some(p) => p
    None => symval(q_modulus)
  }
  with_special(q_modulus, prime, () => {
    let facts = afp_square_free_factorization(u)
    let c = Collector::new()
    let mut p = facts
    while p is Cons(_) {
      let pol = car(p)
      let pow = cadr(p)
      aquotient__show("POL", pol)
      aquotient__show("POW", pow)
      let fact1 = afp_distinct_degree_factor(pol, prime~)
      for ww in fact1.iter() {
        c.add(ww)
        c.add(pow)
      }
      p = cddr(p)
    }
    sort_grouped_list(c.result(), Fix(2L), q_alphagreatp)
  })
}

///|
fn nnpfactor(pol : Value) -> Value raise {
  sort_grouped_list(npfactor(pol), Fix(2L), q_alphagreatp)
}

///|
/// Lifts v and w which satisfy product=v*w mod(prime) to a list FACTS =
/// (uu vv) satisfying product = uu*vv mod (up-to-size).  Product, v, and w
/// are assumed to have leading coefficient 1.
fn hensel_lift(
  product : Value,
  v : Value,
  w : Value,
  prime : Value,
  up_to_size : Value,
) -> (Value, Value) raise {
  let mut facts = list([v, w])
  let ab = with_special(q_modulus, prime, () => {
    let (gcd, a, b) = recursive_ideal_gcd(v, w)
    if !numberp(gcd) {
      fsignal(list1(Str("must have gcd of factors a unit"))) |> ignore
    }
    aquotient__check_arg(eql(Fix(1L), afp_mod(p__cof(v))), "monic")
    list([a, b])
  })
  let a = car(ab)
  let b = cadr(ab)
  let mut power : Value = Fix(1L)
  while true {
    power = num_mul(power, prime)
    if !num_lt(power, up_to_size) {
      break
    }
    let v = car(facts)
    let w = cadr(facts)
    facts = hensel_lift1(product, v, w, power, prime, a~, b~)
  }
  (facts, power)
}

///|
fn gen_afp_times(lis : Value) -> Value raise {
  let lis = remove_equal(Fix(1L), copy_list(lis))
  if lis is Nil {
    Fix(1L)
  } else if cdr(lis) is Nil {
    car(lis)
  } else {
    afp_times(
      car(lis),
      if cddr(lis).truthy() {
        gen_afp_times1(cdr(lis))
      } else {
        cadr(lis)
      },
    )
  }
}

///|
fn gen_afp_times1(lis : Value) -> Value raise {
  if lis is Nil {
    Fix(1L)
  } else if cdr(lis) is Nil {
    car(lis)
  } else {
    afp_times(
      car(lis),
      if cddr(lis).truthy() {
        gen_afp_times(cdr(lis))
      } else {
        cadr(lis)
      },
    )
  }
}

///|
fn smallest_power_bigger(p : Value, up_to : Value) -> Value raise {
  let mut pow = p
  while num_lt(pow, up_to) {
    pow = num_mul(p, pow)
  }
  pow
}

///|
fn hensel_lift_list(
  product : Value,
  factor_list : Value,
  prime : Value,
  up_to_size : Value,
) -> Value raise {
  if length(factor_list) == 1 {
    list1(product)
  } else if length(factor_list) == 2 {
    hensel_lift(product, car(factor_list), cadr(factor_list), prime, up_to_size).0
  } else {
    let rest = with_special(q_modulus, prime, () => gen_afp_times(
      cdr(factor_list),
    ))
    let lift = hensel_lift(product, car(factor_list), rest, prime, up_to_size).0
    cons(
      car(lift),
      hensel_lift_list(cadr(lift), cdr(factor_list), prime, up_to_size),
    )
  }
}

///|
/// Lifts u=ve*we mod (p^e) to u=ve+1*we+1 mod (p^e+1) with ve=ve+1 and
/// we=we+1 mod (p^e+1) and deg(ve+1)<=deg(ve) deg(we+1)<=deg(we) and
/// returns the list of ve+1 and we+1.
fn hensel_lift1(
  product : Value,
  ve : Value,
  we : Value,
  prev_modulus : Value,
  prime : Value,
  a? : Value = Nil,
  b? : Value = Nil,
) -> Value raise {
  let new_modulus = num_mul(prime, prev_modulus)
  let dif = with_special(q_modulus, new_modulus, () => pdifference(
    product,
    ptimes(ve, we),
  ))
  if pzerop(dif).truthy() {
    list([ve, we])
  } else {
    let mut a = a
    let mut b = b
    with_special(q_modulus, prime, () => {
      if a is Nil {
        let (_, a1, b1) = recursive_ideal_gcd(ve, we)
        a = a1
        b = b1
      }
      (Nil : Value)
    })
    |> ignore
    with_special(q_modulus, new_modulus, () => {
      let h = ptimes(b, dif)
      let mut kk = ptimes(a, dif)
      let qrc = with_special(q_modulus, new_modulus, () => {
        let (q, r, c) = afp_pseudo_quotient(h, ve)
        list([q, r, c])
      })
      let quot = car(qrc)
      let zl_rem = cadr(qrc)
      let h = zl_rem
      kk = pplus(kk, ptimes(quot, we))
      list([pplus(ve, h), pplus(we, kk)])
    })
  }
}

///|
/// Makes sure there are no factors with leading cof = -1 and collects all
/// constants together and puts them first.
fn collect_number_factors(fact_list : Value) -> Value raise {
  let mut answ : Value = Nil
  let mut constant : Value = Fix(1L)
  let mut p = fact_list
  while p is Cons(_) {
    let mut pol = car(p)
    let deg = cadr(p)
    if numberp(pol) {
      constant = ctimes(constant, cexpt(pol, deg))
    } else if eql(p__cof(pol), Fix(-1L)) {
      constant = ctimes(constant, cexpt(p__cof(pol), deg))
      pol = pminus(pol)
      answ = nconc(answ, list([pol, deg]))
    } else {
      answ = nconc(answ, list([pol, deg]))
    }
    p = cddr(p)
  }
  if eql(Fix(1L), constant) {
    answ
  } else {
    cons(constant, cons(Fix(1L), answ))
  }
}

///|
/// Returns an alternating list of irreducible polynomials and their powers
/// in the factorization over the integers.
fn integer_univariate_factor(poly : Value) -> Value raise {
  let facts = afp_square_free_factorization(poly)
  aquotient__show("FACTS", facts)
  let c = Collector::new()
  let mut p = facts
  while p is Cons(_) {
    let pol = car(p)
    let deg = cadr(p)
    for pol1 in integer_univariate_factor1(pol).iter() {
      c.add(pol1)
      c.add(deg)
    }
    p = cddr(p)
  }
  collect_number_factors(c.result())
}

///|
/// Finds a small prime P so that the roots of poly with respect to
/// variable VARIABLE are distinct and so that poly has the same degree
/// reduced modulo P.
fn find_small_prime_so_square_free(
  poly : Value,
  variable? : Value,
  prime_start? : Value = Fix(13L),
) -> Value raise {
  let variable = match variable {
    Some(v) => v
    None => p__var(poly)
  }
  let mut prime_start = prime_start
  let deriv = pderivative(poly, variable)
  let cof = pcoeff(
    poly,
    list([variable, pdegree(poly, variable), Fix(1L)]),
  )
  if eql(symval(q_ear_mod_p_factor), q_afp_distinct_degree_factor) {
    prime_start = num_max(prime_start, Fix(3L))
  }
  let mut p = prime_start
  while true {
    if num_gt(num_sub(p, prime_start), Fix(500L)) {
      format(t, "~%I hope you have given me a square free polynomial!!", [])
      |> ignore
    }
    let pp = p
    if q__primep(p).truthy() &&
      with_special(q_modulus, pp, () => if pzerop(afp_mod(cof)).truthy() {
        (Nil : Value)
      } else {
        let the_gcd = afp_gcd(afp_mod(poly), afp_mod(deriv))
        lbool(
          numberp(the_gcd) || !memq(variable, list_variables(the_gcd)).truthy(),
        )
      }).truthy() {
      return p
    }
    p = one_plus(p)
  }
  Nil
}

///|
/// Argument pol is square free.
fn integer_univariate_factor1(pol : Value) -> Value raise {
  let up_to : Value = Fix(1000L)
  let p = find_small_prime_so_square_free(pol)
  let mut facts = with_special(q_modulus, p, () => afp_factor(
    pol,
    square_free_arg=t,
  ))
  let mod_ = smallest_power_bigger(p, up_to)
  let c = Collector::new()
  let mut q = facts
  while q is Cons(_) {
    let pol = car(q)
    let deg = cadr(q)
    if !eql(deg, Fix(1L)) {
      fsignal(list1(Str("bad-degree-for-square-free"))) |> ignore
    }
    c.add(pol)
    q = cddr(q)
  }
  facts = c.result()
  let lifts = hensel_lift_list(pol, facts, p, up_to)
  correct_factors(pol, lifts, p, mod_)
}

///|
/// Returns list of ordered sublists of LIST of length LENG.
fn sub_lists(leng : Value, list_ : Value) -> Value raise {
  if zerop(leng) {
    Nil
  } else if eql(Fix(1L), leng) {
    mapcar(x => list1(x), list_)
  } else {
    let c = Collector::new()
    let mut v = list_
    while v is Cons(_) {
      for w in sub_lists(num_sub(leng, Fix(1L)), cdr(v)).iter() {
        c.add(cons(car(v), w))
      }
      v = cdr(v)
    }
    c.result()
  }
}

///|
/// `(delete item list :count 1 :test #'equal)`
fn aquotient__delete_one_equal(item : Value, l : Value) -> Value {
  let c = Collector::new()
  let mut p = l
  let mut done = false
  while p is Cons(_) {
    if !done && equal(item, car(p)) {
      done = true
    } else {
      c.add(car(p))
    }
    p = cdr(p)
  }
  c.result()
}

///|
/// Given the factors FACTORS of polynomial POL modulo MOD, we determine
/// what the factors are over the integers.  It is assumed that MOD is
/// sufficiently large so that any real factors of POL lie in the range
/// -MOD/2 to MOD/2.  Also POL is assumed square free so that the factors
/// are listed without their multiplicities.
fn correct_factors(pol : Value, factors : Value, p : Value, mod_ : Value) -> Value raise {
  ignore(p)
  let mut pol = pol
  let mut factors = factors
  let mut tried : Value = Nil
  let mut answ : Value = Nil
  let mut d = 1
  while true {
    // look-for-factors
    if 2 * d > length(factors) {
      answ = cons(pol, answ)
      return answ
    }
    let mut restart = false
    for v in sub_lists(int(d), factors).iter() {
      if member_equal(v, tried).truthy() {
        continue
      }
      tried = cons(v, tried)
      let prod = with_special(q_modulus, mod_, () => gen_ptimes(v))
      let quot = afp_test_divide(pol, prod)
      if quot.truthy() {
        pol = quot
        answ = cons(prod, answ)
        for vv in v.iter() {
          factors = aquotient__delete_one_equal(vv, factors)
        }
        restart = true
        break
      }
    }
    if !restart {
      d = d + 1
    }
  }
  Nil
}

///|
fn q__primep(i : Value) -> Value raise {
  let lis = list([Fix(2L), Fix(3L), Fix(5L), Fix(7L), Fix(11L), Fix(13L)])
  let m = car(member(i, lis))
  if m.truthy() {
    m
  } else if evenp(i) {
    Nil
  } else {
    let mut found = false
    for v in cdr(lis).iter() {
      if zerop(num_mod(i, v)) {
        found = true
        break
      }
    }
    if found {
      Nil
    } else {
      primep(i)
    }
  }
}

///|
fn test_integer_factor(pol : Value) -> Value raise {
  let facts = integer_univariate_factor(pol)
  aquotient__iassert(equal(pol, exponent_product(facts)))
  facts
}

///|
fn subs_translate_sublis(point : Value, inv? : Value = Nil) -> Value raise {
  let c = Collector::new()
  for v in point.iter() {
    if !pzerop(cdr(v)).truthy() {
      if inv.truthy() {
        c.add(cons(car(v), pplus(list([car(v), Fix(1L), Fix(1L)]), cdr(v))))
      } else {
        c.add(
          cons(car(v), pdifference(list([car(v), Fix(1L), Fix(1L)]), cdr(v))),
        )
      }
    }
  }
  c.result()
}

///|
/// F and g should be univariate and the leading coefficient of g
/// invertible modulo modulus.  A list of two coefficients (a b) are
/// returned such that x^i= a*f + b*g and deg(a)< deg (g).
fn express_x_hati(f : Value, g : Value, k : Value, modulus? : Value) -> Value raise {
  let m = match modulus {
    Some(m) => m
    None => symval(q_modulus)
  }
  with_special(q_modulus, m, () => {
    aquotient__check_arg(symval(q_modulus).truthy(), "non-trivial")
    if eql(k, Fix(0L)) {
      let (_, a, b) = recursive_ideal_gcd(f, g)
      list([a, b])
    } else {
      let case0 = express_x_hati(f, g, Fix(0L))
      let mon = list([car(f), k, Fix(1L)])
      let a = ptimes(car(case0), mon)
      let mut b = ptimes(cadr(case0), mon)
      let (quot, zl_rem, _) = afp_pseudo_quotient(a, g)
      let a = zl_rem
      b = pplus(b, ptimes(quot, f))
      list([a, b])
    }
  })
}

///|
/// `(mshow v ...)`: `(format t "~%The value of ~A is.. " 'v)` `(des v)`.
fn aquotient__mshow(forms : Array[(String, Value)]) -> Unit raise {
  for fv in forms {
    format(t, "~%The value of ~A is.. ", [Str(fv.0)]) |> ignore
    des(fv.1) |> ignore
  }
}

///|
fn wr_lift(
  u : Value,
  fi : Value,
  gi : Value,
  up_to_k : Value,
  big_mod : Value,
  point : Value,
) -> Value raise {
  with_special(q_modulus, big_mod, () => {
    let main_var = p__var(u)
    let mut fi = fi
    let mut gi = gi
    let v = psublis(subs_translate_sublis(point), Fix(1L), u)
    let varl = remove_equal(car(u), list_variables(u))
    let f0 = fi
    let g0 = gi
    let mut i : Value = Fix(1L)
    while num_le(i, up_to_k) {
      let mut w = pdifference(afp_times(fi, gi), u)
      w = afp_truncate_powers(w, varl, i)
      aquotient__mshow([("W", w)])
      if pzerop(w).truthy() {
        // nothing-to-do
        ()
      } else if numberp(w) || !eql(p__var(w), main_var) {
        // (setq aw ...) twice; AW is not used afterwards in this branch.
        let tem = express_x_hati(f0, g0, Fix(0L))
        afp_times(w, car(tem)) |> ignore
        afp_times(w, cadr(tem)) |> ignore
      } else {
        let mut aw : Value = Fix(0L)
        let mut bw : Value = Fix(0L)
        let mut q = cdr(w)
        while q is Cons(_) {
          let deg = car(q)
          let cof = cadr(q)
          let tem = express_x_hati(f0, g0, deg)
          aw = afp_plus(aw, afp_times(car(tem), cof))
          bw = afp_plus(bw, afp_times(cadr(tem), cof))
          q = cddr(q)
        }
        let fi1 = pdifference(fi, bw)
        let gi1 = pdifference(gi, aw)
        fi = fi1
        gi = gi1
        aquotient__mshow([("AW", aw), ("BW", bw), ("FI", fi), ("GI", gi)])
      }
      i = one_plus(i)
    }
    aquotient__show("(PDIFFERENCE V (PTIMES FI GI))", pdifference(v, ptimes(fi, gi)))
    list([fi, gi])
  })
}

///|
fn afp_truncate_powers(pol : Value, varl : Value, deg : Value) -> Value raise {
  let varl = sort_list(varl, (a, b) => pointergp(a, b).truthy())
  afp_truncate_powers1(pol, varl, deg)
}

///|
fn afp_truncate_powers1(pol : Value, varl : Value, above_deg : Value) -> Value raise {
  if num_lt(above_deg, Fix(0L)) {
    Fix(0L)
  } else if numberp(pol) {
    pol
  } else if varl is Nil {
    pol
  } else if memq(p__var(pol), varl).truthy() {
    let c = Collector::new()
    let mut p = cdr(pol)
    while p is Cons(_) {
      let exp = car(p)
      let cof = cadr(p)
      let tem = num_sub(above_deg, exp)
      if !num_lt(tem, Fix(0L)) {
        let new_cof = afp_truncate_powers1(cof, cdr(varl), tem)
        if !pzerop(new_cof).truthy() {
          c.add(exp)
          c.add(new_cof)
        }
      }
      p = cddr(p)
    }
    psimp(p__var(pol), c.result())
  } else {
    let c = Collector::new()
    let mut p = cdr(pol)
    while p is Cons(_) {
      let exp = car(p)
      let new_cof = afp_truncate_powers1(cadr(p), varl, above_deg)
      if !pzerop(new_cof).truthy() {
        c.add(exp)
        c.add(new_cof)
      }
      p = cddr(p)
    }
    psimp(p__var(pol), c.result())
  }
}

///|
/// Checks factor-list and eliminates repeats.  All integer factors are
/// grouped at the beginning if any.
fn normalize_factor_list(factor_list : Value) -> Value raise {
  let mut numerical_factor : Value = Nil
  let mut facts = collect_number_factors(factor_list)
  if numberp(car(facts)) {
    numerical_factor = list([car(facts), cadr(facts)])
    facts = cddr(facts)
  }
  let c = Collector::new()
  let mut rest_facts = facts
  while rest_facts is Cons(_) {
    let pol = car(rest_facts)
    let deg = cadr(rest_facts)
    aquotient__show("FACTS", facts)
    aquotient__show("DEG", deg)
    if deg.truthy() {
      let mut sum : Value = Fix(0L)
      let mut v = cddr(rest_facts)
      while v is Cons(_) {
        if cadr(v).truthy() && equal(pol, car(v)) {
          sum = num_add(sum, cadr(v))
          setf_car(cdr(v), Nil) |> ignore
        }
        v = cddr(v)
      }
      let tot_deg = num_add(deg, sum)
      c.add(pol)
      c.add(tot_deg)
    }
    rest_facts = cddr(rest_facts)
  }
  nconc(numerical_factor, c.result())
}

///|
/// TEST-DIVIDE is not defined in Maxima.
fn find_factor_list_given_irreducible_factors(
  pol : Value,
  fact_list : Value,
) -> Value raise {
  let mut pol = pol
  let mut final_answ : Value = Nil
  while true {
    let divisor = car(fact_list)
    if divisor is Nil {
      break
    }
    let mut deg : Value = Fix(1L)
    while true {
      let answ = sparsemat__call_undefined(aquotient__q_test_divide, [
        pol, divisor,
      ])
      if answ is Nil {
        break
      }
      pol = answ
      deg = one_plus(deg)
    }
    final_answ = cons(deg, final_answ)
    final_answ = cons(pol, final_answ)
  }
  if !equal(final_answ, Fix(1L)) {
    fsignal(list1(Str("bad factorization"))) |> ignore
  }
  final_answ
}

///|
/// Input may be non square free.  TRY-MULTI-FACTOR1 is not defined in
/// Maxima.
fn try_multi_factor0(pol : Value) -> Value raise {
  let mut facs = afp_square_free_factorization(pol)
  let mut result : Value = Nil
  while true {
    // next-factor
    let fac = car(facs)
    let deg = cadr(facs)
    facs = cddr(facs)
    let mut newfacs = sparsemat__call_undefined(aquotient__q_try_multi_factor1, [
      fac,
    ])
    while true {
      result = cons(num_mul(cadr(newfacs), deg), result)
      result = cons(car(newfacs), result)
      newfacs = cddr(newfacs)
      if newfacs is Nil {
        break
      }
    }
    if facs is Nil {
      break
    }
  }
  result
}

///|
/// Note: the DO steps W to (cdr result), not (cdr w), so all but the first
/// degree land in the second slot.
fn afp_degvector(pol : Value, vars : Value) -> Value raise {
  let result = aquotient__make_list(length(vars))
  let mut v = vars
  let mut w = result
  while v is Cons(_) {
    setf_car(w, pdegree(pol, car(v))) |> ignore
    v = cdr(v)
    w = cdr(result)
  }
  result
}

///|
/// Note: BEST is never updated, so this is the last variable whose degree
/// is below 2^20.
fn afp_smallest_var(degvector : Value, list_variables : Value) -> Value raise {
  let best = expt(Fix(2L), Fix(20L))
  let mut best_variable : Value = Nil
  let mut v = degvector
  let mut w = list_variables
  while v is Cons(_) {
    if num_lt(car(v), best) {
      best_variable = car(w)
    }
    v = cdr(v)
    w = cdr(w)
  }
  best_variable
}

// ---------------------------------------------------------------------
// The macros of aquotient.lisp, as functions.

///|
/// `(p-cof f)`: leading coefficient of f.
fn p__cof(f : Value) -> Value raise {
  caddr(f)
}

///|
fn p__next_term(f : Value) -> Value raise {
  cddr(f)
}

///|
fn p__deg(f : Value) -> Value raise {
  cadr(f)
}

///|
fn term_cof(terms : Value) -> Value raise {
  cadr(terms)
}

///|
fn term_deg(terms : Value) -> Value raise {
  car(terms)
}

///|
/// TERM-OPERATION with OPERATION-FUNCTION a function designator.
fn term_operation(
  f : Value,
  g : Value,
  operation_function : Value,
  deg_shift_result? : Value = Nil,
) -> Value raise {
  aquotient__term_op(
    f,
    g,
    (a, b) => funcall(operation_function, [a, b]),
    shift=deg_shift_result,
  )
}

///|
/// PLAIN-TERM-OPERATION with OPERATION-FUNCTION a function designator.
fn plain_term_operation(
  terms_f : Value,
  terms_g : Value,
  operation_function : Value,
  deg_shift_result? : Value = Nil,
) -> Value raise {
  aquotient__plain_term_op(
    terms_f,
    terms_g,
    (a, b) => funcall(operation_function, [a, b]),
    shift=deg_shift_result,
  )
}

///|
fn quotient_not_exact() -> Value raise {
  if boundp(q_ear_testing) && symval(q_ear_testing).truthy() {
    throw_tag(q_quotient_not_exact, t)
  } else {
    fsignal(list1(q_quotient_not_exact))
  }
}

///|
fn qfirstn(n : Value, l : Value) -> Value raise {
  if eql(n, Fix(1L)) {
    list1(car(l))
  } else if eql(n, Fix(2L)) {
    list([car(l), cadr(l)])
  } else {
    subseq(l, 0, end=to_int(n))
  }
}

///|
fn add_one_term(deg : Value, cof : Value, terms : Value) -> Value raise {
  aquotient__add_one_term(deg, cof, terms)
}

///|
/// ASSUME-POINTERG-OR-EQUAL-P swaps the caller's variables F and G (and
/// flips REVERSE-FLAG) unless F is pointer-greater; as a function it
/// returns the list (f g reverse-flag) after the swap.
fn assume_pointerg_or_equal_p(
  f : Value,
  g : Value,
  reverse_flag? : Value = Nil,
) -> Value raise {
  if gen_pointergp(f, g).truthy() {
    list([f, g, reverse_flag])
  } else {
    list([g, f, lbool(reverse_flag is Nil)])
  }
}

///|
/// ASSUME-GREATER-EQUAL-DEGREE: as a function returns the list (f g
/// reverse-flag) after the swap (see ASSUME-POINTERG-OR-EQUAL-P).
fn assume_greater_equal_degree(
  f : Value,
  g : Value,
  reverse_flag? : Value = Nil,
) -> Value raise {
  if num_ge(gen_degree(f), gen_degree(g)) {
    list([f, g, reverse_flag])
  } else {
    list([g, f, lbool(reverse_flag is Nil)])
  }
}

///|
/// BUTLASTN knocks off the last n items of a list (the macro also stores
/// the result into the place LIST).
fn butlastn(n : Value, list_ : Value) -> Value raise {
  if num_lt(n, int(length(list_))) {
    setf_cdr(lastn(one_plus(n), list_), Nil) |> ignore
    list_
  } else {
    Nil
  }
}

///|
/// DEF-TEST defines a function TEST-<F1> comparing F1 and F2 on the same
/// arguments.
fn def_test(f1 : Value, f2 : Value) -> Value raise {
  let name = intern("test-" + symbol_name(f1))
  defun(Sym(name), args => aquotient__run_def_test(f1, f2, list(args)))
  Sym(name)
}

///|
fn aquotient__run_def_test(f1 : Value, f2 : Value, rest_args : Value) -> Value raise {
  let mut rest_args = rest_args
  let mut empty = false
  let kw_empty = q_kw_empty
  if memq(kw_empty, rest_args).truthy() {
    rest_args = subseq(
      rest_args,
      0,
      end=length(rest_args) - length(memq(kw_empty, rest_args)),
    )
    empty = true
  }
  with_specials([(q_ear_print_level, Fix(2L)), (q_ear_print_length, Fix(3L))], () => {
    format(
      t,
      "~%For functions ~A and ~A respectively, ~%with argument list being ~A",
      [f1, f2, rest_args],
    )
    |> ignore
    if empty {
      format(t, "~%All computations done in a temporary area:", []) |> ignore
    }
    if !empty && symval(q_modulus).truthy() {
      let ansa = apply(f1, rest_args)
      let ansb = remove_zero_coefficients(apply(f2, rest_args))
      aquotient__iassert(equal(ansa, ansb))
      Nil
    } else if empty {
      apply(f1, rest_args) |> ignore
      apply(f2, rest_args) |> ignore
      Nil
    } else {
      let ansa = apply(f1, rest_args)
      let ansb = apply(f2, rest_args)
      aquotient__iassert(equal(ansa, ansb))
      Nil
    }
  })
}

///|
fn push_poly_number_deg_cof(
  rows : Value,
  poly_number : Value,
  deg : Value,
  cof : Value,
) -> Value raise {
  let row = aref1(rows, to_int(deg))
  vector_push_extend(poly_number, row) |> ignore
  int(vector_push_extend(cof, row))
}

///|
fn init_share_aquotient() -> Unit raise {
  // (def-test nnpfactor afp-factor)
  def_test(q_nnpfactor, q_afp_factor) |> ignore
  // The affine POLY-LENGTH replaces Grobner's in the function cell.
  defun(q_poly_length, args => aquotient__poly_length(arg(args, 0)))
}

///|
/// `(make-list n)`
fn aquotient__make_list(n : Int) -> Value {
  let c = Collector::new()
  for _ in 0..<n {
    c.add(Nil)
  }
  c.result()
}
