// Port of share/affine/new-rat.lisp: conversion to CRE form over the
// affine package's alphabetical masterlist *varlist* / *genvar*.
//
// These functions keep an alphabetical masterlist in *genvar* and
// *varlist* and use them. genpairs just keeps the pairs needed for the
// current form. new-newvar must be called before new-prep1, because the
// newvarmexpt function which handles exponentiation has no new-
// analogue and so will call (newsym), not (add-newvar).

///|
fn safe_putprop(sym_ : Value, value : Value, indicator : Value) -> Value raise {
  putprop(sym_, value, indicator)
}

///|
fn new_prep1(x : Value) -> Value raise {
  if floatp(x) {
    if symval(q_d_keepfloat).truthy() {
      cons(x, Flo(1.0))
    } else {
      prepfloat(x)
    }
  } else if integerp(x) {
    cons(cmod(x), Fix(1L))
  } else if ratiop(x) {
    if symval(q_modulus) is Nil {
      cons(numerator(x), denominator(x))
    } else {
      cquotient(numerator(x), denominator(x))
    }
  } else if atom(x) {
    let v = assolike(x, symval(q_genpairs))
    if v.truthy() {
      v
    } else {
      format(t, "***In new-prep1**", []) |> ignore
      add_newvar_to_genpairs(x)
    }
  } else if symval(q_d_ratfac).truthy() &&
    assolike(x, symval(q_genpairs)).truthy() {
    assolike(x, symval(q_genpairs))
  } else if eq(caar(x), q_mplus) {
    if symval(q_d_ratfac).truthy() {
      let x = mapcar(y => new_prep1(y), cdr(x))
      if every(y => frpoly_q(y).truthy(), x) {
        let mut l = x
        while l is Cons(_) {
          rplaca(l, caar(l)) |> ignore
          l = cdr(l)
        }
        cons(mfacpplus(x), Fix(1L))
      } else {
        let mut a = car(x)
        let mut l = cdr(x)
        while !(l is Nil) {
          a = facrplus(a, car(l))
          l = cdr(l)
        }
        a
      }
    } else {
      let mut a = new_prep1(cadr(x))
      let mut l = cddr(x)
      while !(l is Nil) {
        a = ratplus(a, new_prep1(car(l)))
        l = cdr(l)
      }
      a
    }
  } else if eq(caar(x), q_mtimes) {
    let sw = lbool(
      !(symval(q_d_norepeat).truthy() && memq(q_ratsimp, cdar(x)).truthy()),
    )
    let mut a = savefactors(new_prep1(cadr(x)))
    let mut l = cddr(x)
    while !(l is Nil) {
      a = rattimes(a, savefactors(new_prep1(car(l))), sw)
      l = cdr(l)
    }
    a
  } else if eq(caar(x), q_mexpt) {
    newvarmexpt(x, caddr(x), t)
  } else if eq(caar(x), q_mquotient) {
    let a = savefactors(new_prep1(cadr(x)))
    ratquotient(a, savefactors(new_prep1(caddr(x))))
  } else if eq(caar(x), q_mminus) {
    ratminus(new_prep1(cadr(x)))
  } else if eq(caar(x), q_rat) {
    if symval(q_modulus).truthy() {
      cons(cquotient(cmod(cadr(x)), cmod(caddr(x))), Fix(1L))
    } else {
      cons(cadr(x), caddr(x))
    }
  } else if eq(caar(x), q_bigfloat) {
    bigfloat2rat(x)
  } else if eq(caar(x), q_mrat) {
    if symval(q_ear_withinratf).truthy() && memq(q_trunc, car(x)).truthy() {
      throw_tag(q_ratf, Nil)
    } else {
      let mut temp : Value = Nil
      let ok = catch_tag(q_compatvl, () => {
        temp = compatvarl(
          caddar(x),
          symval(q_varlist),
          cadddr(car(x)),
          symval(q_genvar),
        )
        t
      })
      if ok.truthy() {
        if memq(q_trunc, car(x)).truthy() {
          cdr(d_taytorat(x))
        } else if !symval(q_d_keepfloat).truthy() &&
          (pfloatp(cadr(x)).truthy() || pfloatp(cddr(x)).truthy()) {
          cdr(ratrep_star(d_ratdisrep(x)))
        } else {
          sublis(temp, cdr(x))
        }
      } else {
        cdr(ratrep_star(d_ratdisrep(x)))
      }
    }
  } else {
    let v = assolike(x, symval(q_genpairs))
    if v.truthy() {
      v
    } else {
      let x = littlefr1(x)
      let v = assolike(x, symval(q_genpairs))
      if v.truthy() {
        v
      } else {
        format(t, "%%in new-prep1", []) |> ignore
        add_newvar_to_genpairs(x)
      }
    }
  }
}

///|
fn safe_string(symb : Value) -> Value raise {
  string(symb)
}

///|
fn new_ratf(l : Value) -> Value raise {
  with_specials([(q_genpairs, Nil), (q_ear_withinratf, Nil)], () => {
    set(q_ear_withinratf, t) |> ignore
    // get the new variables onto *varlist*
    if eq(q_p_op_pct, catch_tag(q_ratf, () => new_newvar(l))) {
      set(q_ear_withinratf, Nil) |> ignore
      return srf(l)
    }
    with_specials(
      [(q_varlist, symval(q_ear_varlist)), (q_genvar, symval(q_ear_genvar))],
      () => {
        // for truncation routines
        let u = catch_tag(q_ratf, () => new_ratrep_star(l))
        if u.truthy() {
          u
        } else {
          set(q_ear_withinratf, Nil) |> ignore
          srf(l)
        }
      },
    )
  })
}

///|
fn new_newvar(l : Value) -> Value raise {
  my_newvar1(l)
}

///|
/// The ratsetup is done in my-newvar1.
fn new_ratrep_star(x : Value) -> Value raise {
  let p = new_prep1(x)
  cons(
    list_star([
      q_mrat,
      q_simp,
      symval(q_ear_varlist),
      symval(q_ear_genvar),
      if !atom(x) && memq(q_irreducible, cdar(x)).truthy() {
        list1(q_irreducible)
      } else {
        Nil
      },
    ]),
    p,
  )
}

///|
fn new_rat(x : Value) -> Value raise {
  with_special(q_genpairs, Nil, () => {
    if affine_polynomialp(x).truthy() {
      cons(x, Fix(1L))
    } else if rational_functionp(x).truthy() {
      x
    } else if listp(x) && eq(caar(x), q_mrat) {
      if memq(car(num(cdr(x))), symval(q_ear_genvar)).truthy() {
        cdr(x)
      } else {
        format(t, "~%disrepping", []) |> ignore
        new_rat(d_totaldisrep(x))
      }
    } else {
      with_special(q_ear_withinratf, Nil, () => {
        set(q_ear_withinratf, t) |> ignore
        if mbagp(x).truthy() {
          return cons(car(x), mapcar(y => new_rat(y), cdr(x)))
        }
        if eq(q_p_op_pct, catch_tag(q_ratf, () => new_newvar(x))) {
          set(q_ear_withinratf, Nil) |> ignore
          return srf(x)
        }
        with_specials(
          [(q_varlist, symval(q_ear_varlist)), (q_genvar, symval(q_ear_genvar))],
          () => {
            // truncations
            let u = catch_tag(q_ratf, () => new_prep1(x))
            if u.truthy() {
              u
            } else {
              set(q_ear_withinratf, Nil) |> ignore
              srf(x)
            }
          },
        )
      })
    }
  })
}

///|
fn my_newvar1(x : Value) -> Value raise {
  if numberp(x) {
    Nil
  } else if assolike(x, symval(q_genpairs)).truthy() {
    Nil
  } else if atom(x) {
    add_newvar_to_genpairs(x) |> ignore
    Nil
  } else if memq(
      caar(x),
      list([
        q_mplus, q_mtimes, q_rat, q_mdifference, q_mquotient, q_mminus, q_bigfloat,
      ]),
    ).truthy() {
    mapc(y => my_newvar1(y) |> ignore, cdr(x))
  } else if eq(caar(x), q_mexpt) {
    my_newvar1(second(x))
  } else if eq(caar(x), q_mrat) {
    merror(Str(" how did you get here Bill?"), Nil)
  } else if eq(caar(x), q_mnctimes) {
    add_newvar_to_genpairs(x)
  } else {
    merror(Str("What is x like ? ~A"), list1(x))
  }
}

///|
fn add_newvar_to_genpairs(va : Value) -> Value raise {
  if assolike(va, Nil).truthy() {
    ()
  } else {
    let the_gensym = add_newvar(va).0
    set(q_genpairs, cons(cons(va, rget(the_gensym)), symval(q_genpairs)))
    |> ignore
    rat_setup1(va, the_gensym) |> ignore
    rat_setup2(va, the_gensym) |> ignore
  }
  Nil
}

///|
/// If VA is not in varlist ADD-NEWVAR splices VA into the varlist and a new
/// gensym into genvar ordering and adds to genpairs.
fn add_newvar(va : Value, use__stargenpairs_star? : Value = t) -> (Value, Value) raise {
  ignore(use__stargenpairs_star)
  if symbolp(va) && !lstring(safe_string(va)).has_prefix("$") {
    merror(Str("doesn't begin with $"), Nil) |> ignore
  }
  let (after, there, _) = find_in_ordered_list(
    va,
    symval(q_ear_varlist),
    order_function=symval(q_d_order_function),
  )
  let mut the_gensym : Value = Nil
  if there is Nil {
    the_gensym = gensym_readable(va)
    safe_putprop(the_gensym, va, q_disrep) |> ignore
    set(q_ear_genvar, nsplice_in(after, the_gensym, symval(q_ear_genvar)))
    |> ignore
    set(q_ear_varlist, nsplice_in(after, va, symval(q_ear_varlist))) |> ignore
    if symval(q_ear_check_order).truthy() {
      check_order(symval(q_ear_varlist)) |> ignore
    }
    let a = to_int(after)
    let mut i = a + 1
    for v in nthcdr(if a > 0 { a } else { 0 }, symval(q_ear_genvar)).iter() {
      set(v, int(i)) |> ignore
      i += 1
    }
  } else {
    the_gensym = nth(to_int(after), symval(q_ear_genvar))
    if nc_equal(get(the_gensym, q_disrep), va) is Nil {
      fsignal(list1(Str("bad-correspondence"))) |> ignore
    }
  }
  (the_gensym, lbool(there is Nil))
}

///|
fn rat_setup1(v : Value, g : Value) -> Value raise {
  if symval(q_d_ratwtlvl) is Nil {
    return Nil
  }
  let v = assolike(v, symval(q_n_starratweights))
  if v is Nil {
    return Nil
  }
  safe_putprop(g, v, q_d_ratweight)
}

///|
fn rat_setup2(v : Value, g : Value) -> Value raise {
  if symval(q_d_algebraic).truthy() {
    let v = algpget(v)
    if v.truthy() {
      safe_putprop(g, v, q_tellrat)
    } else {
      remprop(g, q_tellrat)
    }
  } else {
    Nil
  }
}

///|
/// A debugging function (it enters the Lisp debugger with BREAK before
/// reducing, which the port does not have).
fn te(f : Value, g : Value) -> Value raise {
  let genvar = nreverse(
    sort_list(union1(listovars(f), listovars(g)), (a, b) => pointergp(a, b).truthy()),
  )
  let varlist = mapcar(v => get(v, q_disrep), genvar)
  with_specials([(q_genvar, genvar), (q_varlist, varlist)], () => {
    ratreduce(f, g)
  })
}

///|
/// Returns an alternating list: factor1 expt1 factor2 expt2 ...
fn new_pfactor(poly : Value) -> Value raise {
  let genvar = nreverse(
    sort_list(listovars(poly), (a, b) => pointergp(a, b).truthy()),
  )
  with_special(q_genvar, genvar, () => pfactor(poly))
}

///|
fn multiply_factors_with_multiplicity(a_list : Value) -> Value raise {
  let mut answer : Value = Fix(1L)
  let mut l = a_list
  while l is Cons(_) && cdr(l) is Cons(_) {
    let v = car(l)
    let mut w = cadr(l)
    while num_gt(w, Fix(0L)) {
      answer = n_star(list2(answer, v))
      w = num_sub(w, Fix(1L))
    }
    l = cddr(l)
  }
  answer
}

///|
fn copy_vgp() -> Value raise {
  set(q_ear_varlist, copy_list(symval(q_ear_varlist))) |> ignore
  set(q_ear_genvar, copy_list(symval(q_ear_genvar))) |> ignore
  Nil
}

///|
fn q__var(f : Value) -> Value raise {
  if atom(f) {
    Nil
  } else {
    aref1(f, 0)
  }
}

///|
fn ar_last(aray : Value) -> Value raise {
  aref1(aray, length(aray) - 1)
}

///|
fn ar_second_last(aray : Value) -> Value raise {
  aref1(aray, length(aray) - 2)
}

///|
fn set_fill_pointer_(aray : Value, n : Value) -> Value raise {
  set_fill_pointer(aray, to_int(n))
  aray
}

///|
fn constant_term_in_main_variable(f : Value) -> Value raise {
  // CZEROP is not defined anywhere in Maxima.
  ar_second_last(f) |> ignore
  raise LispError::SimpleError("The function CZEROP is undefined.")
}

///|
/// This works but is slow; see $projective.
fn d_gcdlist(fns : Value) -> Value raise {
  let mut fns = fns
  if length(fns) == 1 && d_listp(car(fns)).truthy() {
    fns = cdr(car(fns))
  }
  with_special(q_varlist, Nil, () => {
    if length(fns) == 1 {
      car(fns)
    } else {
      for v in fns.iter() {
        newvar(v) |> ignore
      }
      let rat_fns = mapcar(v => cdr(ratrep_star(v)), fns)
      let mut gcd_num = num(car(rat_fns))
      for w in cdr(rat_fns).iter() {
        gcd_num = pgcd(gcd_num, num(w))
      }
      let mut gcd_denom = denom(car(rat_fns))
      for w in cdr(rat_fns).iter() {
        gcd_denom = pgcd(gcd_denom, denom(w))
      }
      ratdisrep(
        cons(
          list([q_mrat, q_simp, symval(q_varlist), symval(q_genvar)]),
          cons(gcd_num, gcd_denom),
        ),
      )
    }
  })
}

///|
fn factoredp(poly : Value) -> Value raise {
  if atom(poly) {
    t
  } else {
    memq(q_factored, car(poly))
  }
}

///|
fn exponent(expr : Value, prod : Value) -> Value raise {
  if atom(prod) {
    Fix(0L)
  } else if eq(caar(prod), q_mexpt) {
    if eq(second(prod), expr) {
      third(prod)
    } else {
      Fix(0L)
    }
  } else {
    check_arg(prod, q_d_productp, Nil) |> ignore
    for v in cdr(prod).iter() {
      if equal(expr, v) {
        return Fix(1L)
      } else if numberp(v) {
        ()
      } else if atom(v) {
        ()
      } else if equal(caar(v), q_mexpt) && equal(second(v), expr) {
        return third(v)
      }
    }
    Fix(0L)
  }
}

///|
fn d_projective(vector_ : Value) -> Value raise {
  let mut factored_vector = mapcar(
    v => if factoredp(v).truthy() { v } else { d_factor(v) },
    cdr(vector_),
  )
  let mut first_one : Value = Nil
  let mut where_ : Int? = None
  let mut i = 0
  for v in factored_vector.iter() {
    if d_zerop(v) is Nil {
      first_one = v
      where_ = Some(i)
      break
    }
    i += 1
  }
  let where_ = match where_ {
    None => return q_image_not_in_projective_space
    Some(w) => w
  }
  // (delete first-one factored-vector :count 1 :test #'equal)
  factored_vector = new_rat__delete_first_equal(first_one, factored_vector)
  let proj = mapcar(w => div_star(w, first_one), factored_vector)
  let mut factors : Value = Nil
  let mut fac : Value = Nil
  for term in proj.iter() {
    if numberp(term) {
      continue
    }
    if atom(term) {
      fac = term
    } else {
      for v in cdr(term).iter() {
        if atom(v) {
          fac = v
        } else if eq(caar(v), q_mexpt) {
          fac = second(v)
        } else if eq(caar(v), q_mplus) {
          fac = v
        }
        if member_equal(fac, factors) is Nil {
          factors = cons(fac, factors)
        }
      }
    }
  }
  let mut lcm_denom : Value = Nil
  for w in factors.iter() {
    let mut expon : Value = Nil
    for v in proj.iter() {
      let tem = exponent(w, v)
      if num_lt(tem, Fix(0L)) {
        if expon is Nil || num_lt(tem, expon) {
          expon = tem
        }
      }
    }
    if expon is Nil {
      expon = Fix(0L)
    }
    if !eql(expon, Fix(0L)) {
      lcm_denom = cons(list3(list2(q_mexpt, q_simp), w, expon), lcm_denom)
    }
  }
  if lcm_denom.truthy() {
    lcm_denom = cons(list2(q_mtimes, q_simp), lcm_denom)
  } else {
    lcm_denom = Fix(1L)
  }
  let tem = mapcar(v => div_star(v, lcm_denom), proj)
  cons(
    list1(q_mlist),
    nsplice_in(int(where_ - 1), div_star(Fix(1L), lcm_denom), tem),
  )
}

///|
/// `(delete item list :count 1 :test #'equal)`
fn new_rat__delete_first_equal(item : Value, l : Value) -> Value {
  if l is Nil {
    return Nil
  }
  if equal(car(l), item) {
    return cdr(l)
  }
  let mut prev = l
  while cdr(prev) is Cons(_) {
    if equal(cadr(prev), item) {
      setf_cdr(prev, cddr(prev)) |> ignore
      break
    }
    prev = cdr(prev)
  }
  l
}

///|
fn d_zeta3_ratsimp(expr : Value) -> Value raise {
  let mut answer = new_rat(expr)
  answer = rationalize_denom_zeta3(answer)
  new_disrep(answer)
}

///|
fn rationalize_denom_zeta3(expr : Value) -> Value raise {
  let the_gen = add_newvar(q_d__pctzeta3).0
  if affine_polynomialp(expr).truthy() {
    expr
  } else if variable_in_polyp(denom(expr), the_gen).truthy() {
    let mut the_denom = denom(expr)
    let the_num = num(expr)
    the_denom = conj_zeta3(the_denom, the_gen)
    ratreduce(ptimes(the_num, the_denom), ptimes(the_denom, denom(expr)))
  } else {
    expr
  }
}

///|
fn conj_zeta3(expr : Value, the_gen : Value) -> Value raise {
  if atom(expr) {
    expr
  } else if eq(car(expr), the_gen) {
    let expr = copy_list(expr)
    setf_car(cdr(expr), Fix(2L)) |> ignore
    palgsimp(the_gen, cdr(expr), alg(expr))
  } else {
    let answer = copy_list(expr)
    let mut r = cddr(answer)
    while r is Cons(_) {
      rplaca(r, conj_zeta3(car(r), the_gen)) |> ignore
      r = cddr(r)
    }
    answer
  }
}

///|
fn variable_in_polyp(poly : Value, gen : Value) -> Value raise {
  catch_tag(q_its_in, () => variable_in_polyp1(poly, gen))
}

///|
fn variable_in_polyp1(poly : Value, gen : Value) -> Value raise {
  if atom(poly) {
    Nil
  } else if eq(car(poly), gen) {
    throw_tag(q_its_in, t)
  } else {
    let mut r = cddr(poly)
    while r is Cons(_) {
      variable_in_polyp1(car(r), gen) |> ignore
      r = cddr(r)
    }
    Nil
  }
}

///|
fn d_zeta3_factor(poly : Value) -> Value raise {
  // %zeta3^2+%zeta3+1
  d_factor(
    poly,
    mp=list([
      list1(q_mplus),
      list3(list1(q_mexpt), q_d__pctzeta3, Fix(2L)),
      q_d__pctzeta3,
      Fix(1L),
    ]),
  )
}

///|
/// When FLAG is T, the call returns a ratform.
fn new_newvarmexpt(x : Value, e : Value, flag : Value) -> Value raise {
  let mut x = x
  let mut e = e
  let flag_ = flag.truthy()
  if fixnump(e) && !flag_ {
    return newvar1(cadr(x))
  }
  let mut topexp : Value = Fix(1L)
  let mut again = true
  while again {
    again = false
    if fixnump(e) {
      // x=b^n for n a number
      topexp = num_mul(topexp, e)
      x = cadr(x)
    } else if atom(e) {
      ()
    } else if eq(caar(e), q_rat) {
      // x=b^(p/q) for p and q integers
      if minusp(cadr(e)) || num_gt(cadr(e), Fix(1L)) {
        topexp = num_mul(topexp, cadr(e))
        x = list3(list1(q_mexpt), cadr(x), list3(list1(q_rat), Fix(1L), caddr(e)))
      }
      if flag_ || numberp(cadr(x)) {
        ()
      } else if symval(q_ear_ratsimp).truthy() {
        if memalike(x, symval(q_radlist)).truthy() {
          return Nil
        } else {
          set(q_radlist, cons(x, symval(q_radlist))) |> ignore
          return newvar1(cadr(x))
        }
      } else if symval(q_d_algebraic).truthy() {
        newvar1(cadr(x)) |> ignore
      }
    } else if eq(caar(e), q_mtimes) {
      // x=b^(a*c)
      let mut hit = false
      // x=b^(n *c)
      if atom(cadr(e)) && fixnump(cadr(e)) {
        topexp = num_mul(topexp, cadr(e))
        e = cddr(e)
        hit = e.truthy()
      }
      // x=b^(p/q *c)
      if !hit &&
        !atom(cadr(e)) &&
        eq(caaadr(e), q_rat) &&
        !equal(Fix(1L), cadadr(e)) {
        topexp = num_mul(topexp, cadadr(e))
        e = cons(list3(list1(q_rat), Fix(1L), caddr(cadr(e))), cddr(e))
        hit = true
      }
      if hit {
        e = simplify(cons(list1(q_mtimes), e))
        x = list3(list1(q_mexpt), cadr(x), e)
        again = true
      }
    } else if eq(caar(e), q_mplus) && symval(q_expsumsplit).truthy() {
      // x=b^(a+c): the switch controls splitting exponent sums
      let base = cadr(x)
      let te = topexp
      x = cons(
        list1(q_mtimes),
        mapcar(
          ll => list3(
            list1(q_mexpt),
            base,
            simplify(list3(list1(q_mtimes), te, ll)),
          ),
          cdr(e),
        ),
      )
      if flag_ {
        return new_prep1(x)
      } else {
        return newvar1(x)
      }
    }
  }
  if flag_ {
    ()
  } else if equal(Fix(1L), topexp) {
    if atom(x) || !eq(caar(x), q_mexpt) {
      newvar1(x) |> ignore
    } else if memalike(x, symval(q_varlist)).truthy() ||
      memalike(x, symval(q_vlist)).truthy() {
      ()
    } else if atom(x) || !symval(q_n_starfnewvarsw).truthy() {
      putonvlist(x) |> ignore
    } else {
      x = littlefr1(x)
      mapc(y => newvar1(y) |> ignore, cdr(x)) |> ignore
      if !(memalike(x, symval(q_vlist)).truthy() ||
        memalike(x, symval(q_varlist)).truthy()) {
        putonvlist(x) |> ignore
      }
    }
  } else {
    newvar1(x) |> ignore
  }
  if !flag_ {
    Nil
  } else if equal(Fix(1L), topexp) {
    if !atom(x) && eq(caar(x), q_mexpt) {
      let v = assolike(x, symval(q_genpairs))
      if v.truthy() {
        v
      } else {
        // should only get here if called from fr1. *fnewvarsw=nil
        let x = littlefr1(x)
        let v = assolike(x, symval(q_genpairs))
        if v.truthy() {
          v
        } else {
          new_newsym(x)
        }
      }
    } else {
      new_prep1(x)
    }
  } else {
    ratexpt(new_prep1(x), topexp)
  }
}

///|
fn new_newsym(e : Value) -> Value raise {
  let g0 = assolike(e, symval(q_genpairs))
  if g0.truthy() {
    return g0
  }
  let g = gensym()
  putprop(g, e, q_disrep) |> ignore
  add_newvar(e) |> ignore
  let p = if symval(q_d_algebraic).truthy() { algpget(e) } else { Nil }
  if p.truthy() {
    putprop(g, p, q_tellrat) |> ignore
  }
  rget(g)
}

///|
/// new-rat.lisp's redefinition of TELLRAT1 (installed when the file is
/// loaded): the tellrat must be compatible with *genvar*.
fn new_rat__tellrat1(x : Value) -> Value raise {
  let bs = bind_all([
    (q_varlist, Nil),
    (q_genvar, Nil),
    (q_d_algebraic, Nil),
    (q_d_ratfac, Nil),
  ])
  defer unbind_all(bs)
  let mut x = d_totaldisrep(x)
  if !atom(x) && eq(caar(x), q_mequal) {
    newvar(cadr(x)) |> ignore
  }
  x = meqhk(x)
  newvar(x) |> ignore
  if symval(q_varlist) is Nil {
    merror(Str("Improper polynomial"), Nil) |> ignore
  }
  x = primpart(cadr(d_new_rat(x)))
  let algvar0 = if symbolp(car(x)) { get(car(x), q_disrep) } else { Nil }
  x = cdr(x)
  if !equal(cadr(x), Fix(1L)) {
    merror(Str("Minimal polynomial must be monic"), Nil) |> ignore
  }
  let mut p = cddr(x)
  while !(p is Nil) {
    rplaca(cdr(p), pdis(cadr(p))) |> ignore
    p = cddr(p)
  }
  let algvar = cons(algvar0, x)
  x = assol(car(algvar), symval(q_tellratlist))
  if x.truthy() {
    set(q_tellratlist, remove_equal(x, symval(q_tellratlist))) |> ignore
  }
  set(q_tellratlist, cons(algvar, symval(q_tellratlist)))
}

///|
fn init_share_new_rat() -> Unit raise {
  defun(q_tellrat1, args => new_rat__tellrat1(arg(args, 0)), name="tellrat1")
}
