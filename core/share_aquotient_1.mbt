// Translation of share/affine/aquotient.lisp (part 1): arithmetic, division
// and gcds of CRE polynomials for the affine package.

///|
let aquotient__q_euclidean : Value = sym("euclidean")

///|
let aquotient__q_test_divide : Value = sym("test-divide")

///|
let aquotient__q_try_multi_factor1 : Value = sym("try-multi-factor1")

///|
let aquotient__q_test_nnpfactor : Value = sym("test-nnpfactor")

///|
/// `(show form)`: prints "The value of FORM is value".
fn aquotient__show(form : String, v : Value) -> Unit raise {
  format(t, "~%The value of ~A is ~A", [Str(form), v]) |> ignore
}

///|
/// `(iassert expr)`
fn aquotient__iassert(ok : Bool) -> Unit raise {
  if !ok {
    fsignal(list1(Str("The expression ~A was not true"))) |> ignore
  }
}

///|
/// `(check-arg place pred msg)` = `(assert pred (place) msg)`.
fn aquotient__check_arg(ok : Bool, msg : String) -> Unit raise {
  if !ok {
    raise LispError::SimpleError(msg)
  }
}

///|
/// The macro WORKING-MODULO: the computations in body are done modulo the
/// list-of-monic-polynomials.
fn aquotient__working_modulo(
  list_of_monic_polynomials : Value,
  body : () -> Value raise,
) -> Value raise {
  let old_tellrats = list_previous_tellrats(list_of_monic_polynomials)
  let r = (fn() raise {
    set_tellrats(list_of_monic_polynomials) |> ignore
    body()
  })() catch {
    e => {
      undo_tellrats(old_tellrats) |> ignore
      raise e
    }
  }
  undo_tellrats(old_tellrats) |> ignore
  r
}

///|
/// TERM-OPERATION: the polynomial whose main variable is that of F with
/// coefficients (op f_i g) in degree i (+ deg-shift).
fn aquotient__term_op(
  f : Value,
  g : Value,
  op : (Value, Value) -> Value raise,
  shift? : Value = Nil,
) -> Value raise {
  psimp(p__var(f), aquotient__plain_term_op(cdr(f), g, op, shift~))
}

///|
/// PLAIN-TERM-OPERATION: the terms with coefficients (op f_i g) in degree
/// i (+ deg-shift).
fn aquotient__plain_term_op(
  terms_f : Value,
  g : Value,
  op : (Value, Value) -> Value raise,
  shift? : Value = Nil,
) -> Value raise {
  let c = Collector::new()
  let mut p = terms_f
  while p is Cons(_) {
    let deg = car(p)
    let cof = cadr(p)
    let tem = op(cof, g)
    if !pzerop(tem).truthy() {
      c.add(if shift.truthy() { num_add(deg, shift) } else { deg })
      c.add(tem)
    }
    p = cddr(p)
  }
  c.result()
}

///|
/// ADD-ONE-TERM
fn aquotient__add_one_term(deg : Value, cof : Value, terms : Value) -> Value raise {
  if pzerop(cof).truthy() {
    terms
  } else {
    cons(deg, cons(cof, terms))
  }
}

///|
/// `(make-polynomial :var var :terms terms)`
fn make_polynomial(var_? : Value = Nil, terms? : Value = Nil) -> Value raise {
  psimp(var_, terms)
}

///|
fn afc_quotient(f : Value, g : Value) -> Value raise {
  cquotient(f, g)
}

///|
/// `(error (car l))`
fn fsignal(l : Value) -> Value raise {
  let datum = car(l)
  match datum {
    Str(s) => raise LispError::SimpleError(s)
    // CL (error 'symbol) with a symbol that names no condition class.
    _ =>
      raise LispError::SimpleError(
        princ_to_string(datum) + " does not designate a condition class.",
      )
  }
}

///|
fn list_previous_tellrats(new_tellrats : Value) -> Value raise {
  let c = Collector::new()
  for v in new_tellrats.iter() {
    c.add(cons(car(v), get(car(v), q_tellrat)))
  }
  c.result()
}

///|
fn set_tellrats(new_tellrats : Value) -> Value raise {
  for v in new_tellrats.iter() {
    putprop(car(v), cdr(v), q_tellrat) |> ignore
  }
  Nil
}

///|
fn undo_tellrats(old_list : Value) -> Value raise {
  for v in old_list.iter() {
    if cdr(v) is Nil {
      remprop(car(v), q_tellrat) |> ignore
    } else {
      putprop(car(v), cdr(v), q_tellrat) |> ignore
    }
  }
  Nil
}

///|
fn afp_cquotient(a : Value, b : Value) -> Value raise {
  if eql(a, Fix(0L)) {
    Fix(0L)
  } else if symval(q_modulus) is Nil {
    let quot = quot(a, b)
    if eql(num_mul(quot, b), a) {
      quot
    } else {
      quotient_not_exact()
    }
  } else {
    ctimes(a, crecip(b))
  }
}

///|
/// Returns the terms of the polynomial which is the product of the two
/// polynomials whose terms are terms-f and terms-g.  If modulus is in
/// effect the result will have its coefficients reduced by modulus.
fn afp_terms_times(terms_f : Value, terms_g : Value) -> Value raise {
  let g_orig = terms_g
  let mut terms_g = terms_g
  let mut answ : Value = Nil
  if terms_g.truthy() {
    answ = aquotient__plain_term_op(
      terms_g,
      term_cof(terms_f),
      afp_times,
      shift=term_deg(terms_f),
    )
    let mut fp = cddr(terms_f)
    while fp is Cons(_) {
      let f_exp = car(fp)
      let f_cof = cadr(fp)
      terms_g = g_orig
      let mut prod_exp : Value = Nil
      let mut prod_cof : Value = Nil
      let mut tail : Value = Nil
      // states: 0 first-product, 1 after first-product cond (tail
      // setup), 2 tail-certain, 3 next-product, 4 done
      let mut state = 0
      while state != 4 {
        match state {
          0 => {
            if terms_g is Nil {
              state = 4
              continue
            }
            prod_exp = num_add(f_exp, term_deg(terms_g))
            prod_cof = afp_times(term_cof(terms_g), f_cof)
            if pzerop(prod_cof).truthy() {
              terms_g = cddr(terms_g)
              state = 0
            } else if answ is Nil || num_gt(prod_exp, term_deg(answ)) {
              answ = cons(prod_exp, cons(prod_cof, answ))
              tail = cdr(answ)
              state = 3
            } else if eql(prod_exp, term_deg(answ)) {
              prod_cof = pplus(term_cof(answ), prod_cof)
              if pzerop(prod_cof).truthy() {
                answ = cddr(answ)
                terms_g = cddr(terms_g)
                state = 0
              } else {
                setf_car(cdr(answ), prod_cof) |> ignore
                tail = cdr(answ)
                state = 3
              }
            } else {
              // below here assume answ not empty and (term-deg answ)
              // greater than any possible future prod-exp (until next
              // f-exp,f-cof).  Tail begins with the coefficient whose
              // corresponding degree is definitely higher than any
              // prod-exp to be encountered.
              tail = cdr(answ)
              state = 2
            }
          }
          2 => {
            if cdr(tail).truthy() && num_gt(cadr(tail), prod_exp) {
              tail = cddr(tail)
              state = 2
            } else if cdr(tail) is Nil || num_lt(cadr(tail), prod_exp) {
              setf_cdr(tail, cons(prod_exp, cons(prod_cof, cdr(tail)))) |> ignore
              tail = cddr(tail)
              state = 3
            } else {
              prod_cof = pplus(caddr(tail), prod_cof)
              if pzerop(prod_cof).truthy() {
                setf_cdr(tail, cdddr(tail)) |> ignore
              } else {
                setf_car(cddr(tail), prod_cof) |> ignore
                tail = cddr(tail)
              }
              state = 3
            }
          }
          _ => {
            // next-product
            terms_g = cddr(terms_g)
            if terms_g is Nil {
              state = 4
              continue
            }
            prod_exp = num_add(f_exp, car(terms_g))
            prod_cof = afp_times(cadr(terms_g), f_cof)
            if pzerop(prod_cof).truthy() {
              state = 3
            } else {
              state = 2
            }
          }
        }
      }
      fp = cddr(fp)
    }
  }
  answ
}

///|
/// Adds a polynomial CONSTANT to a polynomial whose main variable is higher
/// than any in F-MAIN.
fn afp_main_plus_non_main(constant : Value, f_main : Value) -> Value raise {
  psimp(p__var(f_main), afp_constant_term_plus(constant, cdr(f_main)))
}

///|
/// Adds a NUMBER to a polynomial POLY, returning the result.
fn afp_number_plus(number : Value, poly : Value) -> Value raise {
  if numberp(poly) {
    cplus(number, poly)
  } else {
    afp_main_plus_non_main(number, poly)
  }
}

///|
/// Returns the sum of the two polynomials f and g.
fn afp_plus(f : Value, g : Value) -> Value raise {
  if numberp(f) {
    afp_number_plus(f, g)
  } else if numberp(g) {
    afp_number_plus(g, f)
  } else if eq(p__var(f), p__var(g)) {
    psimp(p__var(f), afp_terms_plus(cdr(f), cdr(g)))
  } else if pointergp(p__var(f), p__var(g)).truthy() {
    afp_main_plus_non_main(g, f)
  } else {
    afp_main_plus_non_main(f, g)
  }
}

///|
/// Adds a polynomial (CONSTANT) not involving the main variable of a
/// polynomial whose terms are TERMS.  The result is the terms of the sum
/// polynomial.
fn afp_constant_term_plus(constant : Value, terms : Value) -> Value raise {
  if pzerop(constant).truthy() {
    terms
  } else if terms is Nil {
    list([Fix(0L), constant])
  } else if zerop(car(terms)) {
    let constant = afp_plus(constant, cadr(terms))
    if pzerop(constant).truthy() {
      Nil
    } else {
      list([Fix(0L), constant])
    }
  } else {
    cons(
      car(terms),
      cons(cadr(terms), afp_constant_term_plus(constant, cddr(terms))),
    )
  }
}

///|
/// Returns the terms of the polynomial which is the sum of f and g if the
/// terms of f and the terms of g are the two arguments.
fn afp_terms_plus(terms_f : Value, terms_g : Value) -> Value raise {
  if terms_f is Nil {
    terms_g
  } else if terms_g is Nil {
    terms_f
  } else if eql(car(terms_f), car(terms_g)) {
    let e = afp_plus(cadr(terms_f), cadr(terms_g))
    if pzerop(e).truthy() {
      afp_terms_plus(cddr(terms_f), cddr(terms_g))
    } else {
      cons(
        car(terms_f),
        cons(e, afp_terms_plus(cddr(terms_f), cddr(terms_g))),
      )
    }
  } else if num_gt(car(terms_f), car(terms_g)) {
    cons(car(terms_f), cons(cadr(terms_f), afp_terms_plus(terms_g, cddr(terms_f))))
  } else {
    cons(car(terms_g), cons(cadr(terms_g), afp_terms_plus(terms_f, cddr(terms_g))))
  }
}

///|
/// Makes no check that keeping in the modulus range nor that the result is
/// reduced, but the result g will satisfy (afp-plus f g) ==> 0.
fn afp_minus(f : Value) -> Value raise {
  if numberp(f) {
    cminus(f)
  } else {
    cons(car(f), afp_terms_minus(cdr(f)))
  }
}

///|
fn afp_terms_minus(terms_f : Value) -> Value raise {
  let c = Collector::new()
  let mut p = terms_f
  while p is Cons(_) {
    c.add(car(p))
    c.add(afp_minus(cadr(p)))
    p = cddr(p)
  }
  c.result()
}

///|
fn afp_difference(f : Value, g : Value) -> Value raise {
  if numberp(f) {
    if numberp(g) {
      cdifference(f, g)
    } else {
      psimp(p__var(g), afp_terms_constant_main_differ(f, cdr(g)))
    }
  } else if numberp(g) {
    psimp(p__var(f), afp_terms_main_constant_differ(cdr(f), g))
  } else if eq(p__var(f), p__var(g)) {
    psimp(p__var(f), afp_terms_differ(p__terms(f), p__terms(g)))
  } else if pointergp(p__var(f), p__var(g)).truthy() {
    psimp(p__var(f), afp_terms_main_constant_differ(cdr(f), g))
  } else {
    psimp(p__var(g), afp_terms_main_constant_differ(f, cdr(g)))
  }
}

///|
fn afp_terms_differ(terms_f : Value, terms_g : Value) -> Value raise {
  if terms_f is Nil {
    afp_terms_minus(terms_g)
  } else if terms_g is Nil {
    terms_f
  } else if eql(term_deg(terms_f), term_deg(terms_g)) {
    aquotient__add_one_term(
      term_deg(terms_f),
      afp_difference(term_cof(terms_f), term_cof(terms_g)),
      afp_terms_differ(cddr(terms_f), cddr(terms_g)),
    )
  } else if num_gt(term_deg(terms_f), term_deg(terms_g)) {
    cons(
      term_deg(terms_f),
      cons(term_cof(terms_f), afp_terms_differ(p__next_term(terms_f), terms_g)),
    )
  } else {
    cons(
      term_deg(terms_g),
      cons(
        afp_minus(term_cof(terms_g)),
        afp_terms_differ(terms_f, p__next_term(terms_g)),
      ),
    )
  }
}

///|
/// main is terms const is a polynomial
fn afp_terms_constant_main_differ(const_ : Value, main_ : Value) -> Value raise {
  if main_ is Nil {
    if pzerop(const_).truthy() {
      Nil
    } else {
      list([Fix(0L), const_])
    }
  } else if zerop(car(main_)) {
    aquotient__add_one_term(Fix(0L), afp_difference(cadr(main_), const_), Nil)
  } else {
    cons(
      car(main_),
      cons(afp_minus(cadr(main_)), afp_terms_constant_main_differ(const_, cddr(main_))),
    )
  }
}

///|
fn afp_terms_main_constant_differ(main_ : Value, const_ : Value) -> Value raise {
  if main_ is Nil {
    if pzerop(const_).truthy() {
      Nil
    } else {
      list([Fix(0L), afp_minus(const_)])
    }
  } else if zerop(car(main_)) {
    aquotient__add_one_term(Fix(0L), afp_difference(cadr(main_), const_), Nil)
  } else {
    cons(
      car(main_),
      cons(cadr(main_), afp_terms_main_constant_differ(cddr(main_), const_)),
    )
  }
}

///|
/// Tries to divide the polynomial f by g.  One has result*g=f, or else it
/// signals an error (assumes divides evenly, integer coefficients).
fn afp_quotient(f : Value, g : Value) -> Value raise {
  if numberp(f) {
    if numberp(g) {
      afp_cquotient(f, g)
    } else if zerop(f) {
      Fix(0L)
    } else {
      quotient_not_exact()
    }
  } else if numberp(g) {
    aquotient__term_op(f, g, afp_quotient)
  } else if pointergp(p__var(f), p__var(g)).truthy() {
    aquotient__term_op(f, g, afp_quotient)
  } else if eq(p__var(f), p__var(g)) {
    let main_var = p__var(f)
    let q = Collector::new()
    let mut f = f
    while true {
      let deg_dif = num_sub(p__deg(f), p__deg(g))
      if num_lt(deg_dif, Fix(0L)) {
        break
      }
      q.add(deg_dif)
      let quot = afp_quotient(p__cof(f), p__cof(g))
      q.add(quot)
      let minus_quot = pminus(quot)
      // -fn/gm
      f = pplus(
        f,
        aquotient__term_op(g, minus_quot, ptimes, shift=deg_dif),
      )
      if numberp(f) && zerop(f) {
        break
      }
      if numberp(f) ||
        !eq(main_var, p__var(f)) ||
        num_lt(p__deg(f), p__deg(g)) {
        quotient_not_exact() |> ignore
      }
    }
    make_polynomial(terms=q.result(), var_=main_var)
  } else {
    quotient_not_exact()
  }
}

///|
fn afp_test_divide(f : Value, g : Value) -> Value raise {
  with_special(q_ear_testing, t, () => {
    let mut quot : Value = Nil
    catch_tag(q_quotient_not_exact, () => {
      quot = afp_quotient(f, g)
      quot
    })
    |> ignore
    if quot.truthy() {
      quot
    } else {
      Nil
    }
  })
}

///|
fn afc_remainder(n : Value, divisor : Value) -> (Value, Value) raise {
  let (q, r) = num_truncate(n, b=divisor)
  (r, q)
}

///|
/// Pseudo division as in Knuth's book.  Returns the values: quotient,
/// remainder and creqd so that creqd*f=g*quotient+remainder.  Creqd does
/// not involve the main variable of f.  The remainder has degree lower
/// than g with respect to the main variable of f.
fn afp_pseudo_quotient(f : Value, g : Value) -> (Value, Value, Value) raise {
  if numberp(f) {
    if numberp(g) {
      let (r, q) = afc_remainder(f, g)
      (Fix(1L), r, q)
    } else {
      (Fix(0L), f, Fix(1L))
    }
  } else if numberp(g) {
    (f, Fix(0L), g)
  } else if pointergp(p__var(f), p__var(g)).truthy() {
    (f, Fix(0L), g)
  } else if eq(p__var(f), p__var(g)) {
    let main_var = p__var(f)
    let mut creqd : Value = Fix(1L)
    let mut remainder = if numberp(p__cof(g)) && symval(q_modulus).truthy() {
      f
    } else if numberp(p__cof(g)) && eql(num_abs(p__cof(g)), Fix(1L)) {
      f
    } else {
      creqd = pexpt(
        p__cof(g),
        num_add(Fix(1L), num_sub(p__deg(f), p__deg(g))),
      )
      ptimes(f, creqd)
    }
    let q = Collector::new()
    while true {
      let deg_dif = num_sub(p__deg(remainder), p__deg(g))
      if num_lt(deg_dif, Fix(0L)) {
        break
      }
      q.add(deg_dif)
      let quot = afp_quotient(p__cof(remainder), p__cof(g))
      q.add(quot)
      // -fn/gm
      remainder = pplus(
        remainder,
        aquotient__term_op(g, pminus(quot), ptimes, shift=deg_dif),
      )
      if !(!numberp(remainder) && eql(p__var(remainder), main_var)) {
        break
      }
    }
    let quot = make_polynomial(terms=q.result(), var_=main_var)
    (quot, remainder, creqd)
  } else {
    (Fix(0L), f, Fix(1L))
  }
}

///|
fn gen_pointergp(f : Value, g : Value) -> Value raise {
  if numberp(g) {
    t
  } else if numberp(f) {
    Nil
  } else {
    pointergp(p__var(f), p__var(g))
  }
}

///|
fn gen_degree(f : Value) -> Value raise {
  if numberp(f) {
    Fix(0L)
  } else {
    p__deg(f)
  }
}

///|
/// Returns the gcd of the coefficients of f (with respect to the main
/// variable) if f is a polynomial.
fn afp_content(f : Value) -> Value raise {
  if numberp(f) {
    f
  } else {
    let mut cont = p__cof(f)
    let mut p = cdddr(f)
    while p is Cons(_) {
      cont = afp_gcd(cont, cadr(p))
      p = cddr(p)
    }
    cont
  }
}

///|
fn principal_part(f : Value) -> Value raise {
  afp_quotient(f, afp_content(f))
}

///|
/// Returns the gcd of its two arguments which may be any polynomial with
/// integer coefficients.
fn afp_gcd(f : Value, g : Value) -> Value raise {
  let sw = symval(q_ear_afp_gcd)
  let answer = if eql(sw, aquotient__q_euclidean) {
    afp_euclidean_gcd(f, g)
  } else if eql(sw, q_subresultant) {
    afp_subresultant_gcd(f, g)
  } else {
    merr("~%The value of the switch *afp-gcd* ~A is not legal.", [sw])
  }
  if symval(q_modulus).truthy() {
    afp_try_make_monic(answer)
  } else {
    answer
  }
}

///|
/// This is the Euclidean gcd algorithm, as in Knuth.
fn afp_euclidean_gcd(f : Value, g : Value) -> Value raise {
  let (f, g) = if gen_pointergp(f, g).truthy() { (f, g) } else { (g, f) }
  if numberp(f) {
    num_gcd(f, g)
  } else if gen_pointergp(f, g).truthy() {
    afp_gcd(afp_content(f), g)
  } else if eq(p__var(f), p__var(g)) {
    let contf = afp_content(f)
    let contg = afp_content(g)
    let d = afp_gcd(contf, contg)
    let mut u = afp_quotient(f, contf)
    let mut v = afp_quotient(g, contg)
    if !num_ge(gen_degree(u), gen_degree(v)) {
      let x = u
      u = v
      v = x
    }
    while true {
      let (_, r, _) = afp_pseudo_quotient(u, v)
      if pzerop(r).truthy() {
        return ptimes(d, v)
      }
      if gen_pointergp(f, r).truthy() {
        return d
      }
      u = v
      v = afp_quotient(r, afp_content(r))
    }
    Nil
  } else {
    fsignal(list1(q_should_not_get_here))
  }
}

///|
/// Returns the gcd of its two arguments which may be any polynomial with
/// integer coefficients.  It uses the subresultant algorithm.
fn afp_subresultant_gcd(f : Value, g : Value) -> Value raise {
  let (f, g) = if gen_pointergp(f, g).truthy() { (f, g) } else { (g, f) }
  if numberp(f) {
    num_gcd(f, g)
  } else if gen_pointergp(f, g).truthy() {
    if pzerop(g).truthy() {
      f
    } else {
      afp_subresultant_gcd(afp_content(f), g)
    }
  } else if eq(p__var(f), p__var(g)) {
    let contf = afp_content(f)
    let contg = afp_content(g)
    let d = afp_subresultant_gcd(contf, contg)
    let mut u = afp_quotient(f, contf)
    let mut v = afp_quotient(g, contg)
    if !num_ge(gen_degree(u), gen_degree(v)) {
      let x = u
      u = v
      v = x
    }
    let mut gg : Value = Fix(1L)
    let mut h : Value = Fix(1L)
    let answ = while true {
      let delta = num_sub(p__deg(u), p__deg(v))
      let (_, r, _) = afp_pseudo_quotient(u, v)
      if pzerop(r).truthy() {
        break ptimes(d, principal_part(v))
      }
      if gen_pointergp(f, r).truthy() {
        break d
      }
      u = v
      v = afp_quotient(r, ptimes(gg, pexpt(h, delta)))
      gg = p__cof(u)
      let g_hatdelta = pexpt(gg, delta)
      h = if eql(delta, Fix(1L)) {
        g_hatdelta
      } else if num_gt(delta, Fix(1L)) {
        afp_quotient(g_hatdelta, pexpt(h, num_sub(delta, Fix(1L))))
      } else {
        // here delta=0
        ptimes(g_hatdelta, h)
      }
    } nobreak {
      Nil
    }
    afp_try_make_monic(answ)
  } else {
    Nil
  }
}

///|
fn one_ptimes(f : Value, g : Value) -> Value raise {
  if eql(f, Fix(1L)) {
    g
  } else if eql(g, Fix(1L)) {
    f
  } else {
    ptimes(f, g)
  }
}

///|
/// Exponents may be positive or negative, but assumes result is poly.
fn exponent_product(alternating_factor_exponent_list : Value) -> Value raise {
  let mut numer : Value = Fix(1L)
  let mut denom : Value = Fix(1L)
  let mut p = alternating_factor_exponent_list
  while p is Cons(_) {
    let fact = car(p)
    let deg = cadr(p)
    if num_eq(deg, Fix(1L)) {
      numer = one_ptimes(numer, fact)
    } else if num_gt(deg, Fix(1L)) {
      numer = one_ptimes(numer, pexpt(fact, deg))
    } else if num_eq(deg, Fix(-1L)) {
      denom = one_ptimes(denom, fact)
    } else if num_lt(deg, Fix(-1L)) {
      denom = one_ptimes(denom, pexpt(fact, num_neg(deg)))
    }
    p = cddr(p)
  }
  afp_quotient(numer, denom)
}

///|
fn same_main_and_degree(f : Value, g : Value) -> Value raise {
  if numberp(f) {
    lbool(numberp(g))
  } else if numberp(g) {
    lbool(numberp(f))
  } else {
    lbool(eq(car(f), car(g)) && eql(cadr(f), cadr(g)))
  }
}

///|
/// The arguments may be polynomials with integer coefficients.  Three
/// values are returned: gcd, f/gcd, and g/gcd.
fn afp_big_gcd(f : Value, g : Value) -> (Value, Value, Value) raise {
  let tem = afp_subresultant_gcd(f, g)
  let a = afp_quotient(f, tem)
  let b = afp_quotient(g, tem)
  (tem, a, b)
}

///|
fn afp_pgcdcofacts(f : Value, g : Value) -> Value raise {
  let (a, b, c) = afp_big_gcd(f, g)
  list([a, b, c])
}

///|
fn afp_square_free_with_modulus(u : Value) -> Value raise {
  let vari = list_variables(u)
  aquotient__check_arg(cdr(vari) is Nil, "univariate when modulus")
  aquotient__check_arg(primep(symval(q_modulus)).truthy(), "prime")
  if numberp(u) {
    u
  } else {
    let deriv = pderivative(u, p__var(u))
    let agcd = afp_gcd(u, deriv)
    if numberp(agcd) {
      list([u, Fix(1L)])
    } else if num_gt(p__deg(u), p__deg(agcd)) {
      let quot = afp_quotient(u, agcd)
      append(
        afp_square_free_with_modulus(quot),
        afp_square_free_with_modulus(agcd),
      )
    } else {
      // deriv is 0
      aquotient__check_arg(eql(Fix(0L), deriv), "zero")
      let c = Collector::new()
      let mut p = cdr(u)
      while p is Cons(_) {
        c.add(quot(car(p), symval(q_modulus)))
        c.add(cadr(p))
        p = cddr(p)
      }
      let root = psimp(p__var(u), c.result())
      let r = Collector::new()
      let mut q = afp_square_free_with_modulus(root)
      while q is Cons(_) {
        r.add(car(q))
        r.add(num_mul(cadr(q), symval(q_modulus)))
        q = cddr(q)
      }
      r.result()
    }
  }
}

///|
/// Returns an alternating list of factors and exponents.  In the
/// characteristic 0 case each factor is guaranteed square free and
/// relatively prime to the other factors.  Note that if modulus is not
/// zero then u should be univariate.
fn afp_square_free_factorization(u : Value) -> Value raise {
  if symval(q_modulus).truthy() {
    return afp_square_free_with_modulus(u)
  }
  if numberp(u) {
    return u
  }
  let d = afp_content(u)
  let u = aquotient__term_op(u, d, afp_quotient)
  let (tx, v1, w1) = afp_big_gcd(u, pderivative(u, p__var(u)))
  let some_factors = if eql(tx, Fix(1L)) {
    list([u, Fix(1L)])
  } else if numberp(tx) {
    fsignal(list1(q_how_did_this_happen))
  } else {
    let mut vi = v1
    let mut wi = w1
    let main_var = p__var(u)
    let mut factor_list : Value = Nil
    let mut i = 1
    while true {
      let videriv = pderivative(vi, main_var)
      if equal(wi, videriv) {
        break append(factor_list, list([vi, int(i)]))
      }
      let (ui, vi1, wi1) = afp_big_gcd(vi, pdifference(wi, videriv))
      if !eql(ui, Fix(1L)) {
        factor_list = nconc(factor_list, list([ui, int(i)]))
      }
      vi = vi1
      wi = wi1
      i = i + 1
    } nobreak {
      Nil
    }
  }
  // this is all to collect some numbers and fix the unit multiple.
  let mut answ = d
  let mut p = some_factors
  while p is Cons(_) {
    answ = ptimes(answ, pexpt(p__cof(car(p)), cadr(p)))
    p = cddr(p)
  }
  let unit = afp_quotient(p__cof(u), answ)
  if eql(unit, Fix(1L)) {
    ()
  } else if eql(unit, Fix(-1L)) {
    let mut q = some_factors
    let mut i = 0
    let mut done = false
    while q is Cons(_) {
      let pol1 = car(q)
      let deg1 = cadr(q)
      if oddp(deg1) {
        setf_car(nthcdr(i, some_factors), pminus(pol1)) |> ignore
        done = true
        break
      }
      q = cddr(q)
      i = i + 2
    }
    if !done {
      merr("no odd factors yet differs by minus ", []) |> ignore
    }
  } else {
    fsignal(list1(Str("not handled yet"))) |> ignore
  }
  if eql(d, Fix(1L)) {
    some_factors
  } else {
    append(afp_square_free_factorization(d), some_factors)
  }
}

///|
/// The two arguments are polynomials and the result is the product
/// polynomial.
fn afp_times(f : Value, g : Value) -> Value raise {
  if numberp(f) {
    if zerop(f) {
      Fix(0L)
    } else {
      afp_pctimes(g, f)
    }
  } else if numberp(g) {
    if zerop(g) {
      Fix(0L)
    } else {
      afp_pctimes(f, g)
    }
  } else if eq(p__var(f), p__var(g)) {
    palgsimp(p__var(f), afp_terms_times(cdr(f), cdr(g)), alg(f))
  } else if pointergp(p__var(f), p__var(g)).truthy() {
    psimp(p__var(f), aquotient__plain_term_op(cdr(f), g, afp_times))
  } else {
    psimp(p__var(g), aquotient__plain_term_op(cdr(g), f, afp_times))
  }
}

///|
fn test_decrease(terms : Value) -> Value raise {
  let mut d0 : Value = Fix(1000L)
  let mut p = terms
  while p is Cons(_) {
    let deg = car(p)
    if !num_gt(d0, deg) {
      fsignal(list1(q_bad_order)) |> ignore
    } else {
      d0 = deg
    }
    p = cddr(p)
  }
  Nil
}

///|
/// Its first argument must be a polynomial and second argument a number,
/// and it returns the product.
fn afp_pctimes(poly : Value, number : Value) -> Value raise {
  if atom(poly) {
    ctimes(poly, number)
  } else {
    aquotient__term_op(poly, number, afp_pctimes)
  }
}

///|
/// TIM wraps its body in CL TIME, whose report goes to *trace-output*;
/// here the body is just evaluated.
fn test_times(f : Value, g : Value, empty? : Value = Nil) -> Value raise {
  if symval(q_modulus).truthy() {
    aquotient__iassert(
      equal(afp_times(f, g), remove_zero_coefficients(ptimes(f, g))),
    )
    Nil
  } else if empty.truthy() {
    afp_times(f, g) |> ignore
    ptimes(f, g) |> ignore
    Nil
  } else {
    aquotient__iassert(equal(afp_times(f, g), ptimes(f, g)))
    Nil
  }
}

///|
fn remove_zero_coefficients(poly : Value) -> Value raise {
  if numberp(poly) {
    poly
  } else {
    let mut v = poly
    while cdr(v).truthy() {
      setf_car(cddr(v), remove_zero_coefficients(caddr(v))) |> ignore
      if pzerop(caddr(v)).truthy() {
        setf_cdr(v, cdddr(v)) |> ignore
      } else {
        v = cddr(v)
      }
    }
    if cdr(poly) is Nil {
      Fix(0L)
    } else if zerop(cadr(poly)) {
      caddr(poly)
    } else {
      poly
    }
  }
}

///|
/// Assumes that f and g are polynomials of one variable and that modulus
/// is non trivial and that deg f >= deg g.  gcd = a*f +b*g , and
/// deg a < deg g, deg b < deg f.
fn recursive_ideal_gcd1(f : Value, g : Value) -> (Value, Value, Value) raise {
  if numberp(g) {
    let g = cmod(g)
    if zerop(g) {
      (f, Fix(1L), Fix(0L))
    } else {
      (Fix(1L), Fix(0L), crecip(g))
    }
  } else if !eql(p__var(g), p__var(f)) {
    merror(q_not_function_of_one_variable, Nil) |> ignore
    (Nil, Nil, Nil)
  } else {
    let (quot, zl_rem, _) = afp_pseudo_quotient(f, g)
    let (gcd, a, b) = recursive_ideal_gcd1(g, zl_rem)
    (gcd, b, pdifference(a, ptimes(quot, b)))
  }
}

///|
/// Assumes that f and g are polynomials of one variable and that modulus
/// is non trivial.  It returns (gcd a b) such that gcd = a*f +b*g , and
/// deg a < deg g, deg b < deg f where gcd is the gcd of f and g in the
/// polynomial ring modulo modulus.
fn recursive_ideal_gcd(f : Value, g : Value) -> (Value, Value, Value) raise {
  if symval(q_modulus) is Nil {
    merr("polynomials over the integers are not a PID", []) |> ignore
  }
  let mut rev = false
  let (f, g) = if gen_pointergp(f, g).truthy() {
    (f, g)
  } else {
    rev = !rev
    (g, f)
  }
  if numberp(f) {
    (Fix(1L), crecip(f), Fix(0L))
  } else {
    let (gcd0, a0, b0) = recursive_ideal_gcd1(f, g)
    let mut gcd = gcd0
    let mut a = a0
    let mut b = b0
    let mut fact : Value = Nil
    if numberp(gcd) {
      if !equal(gcd, Fix(1L)) {
        fact = crecip(gcd)
      }
    } else if !equal(p__cof(gcd), Fix(1L)) {
      fact = crecip(p__cof(gcd))
    }
    if fact.truthy() {
      gcd = ptimes(fact, gcd)
      a = ptimes(a, fact)
      b = ptimes(b, fact)
    }
    if rev {
      (gcd, b, a)
    } else {
      (gcd, a, b)
    }
  }
}

///|
/// Do the following at macsyma level to specify which poles you want:
///    e_poles:[e^-2,e^-1]$
fn d_list_poles_of_sum(sum : Value) -> Value raise {
  if numberp(sum) {
    return list([list([q_mlist, q_simp]), Fix(0L), Fix(0L)])
  }
  aquotient__check_arg(
    consp(sum) && eql(caar(sum), q_mplus),
    "macsyma sum",
  )
  let pol = symval(q_d_e_poles)
  let c = Collector::new()
  for u in cdr(pol).iter() {
    let cof = Collector::new()
    let mut n = 0
    for v in cdr(sum).iter() {
      if equal(u, v) {
        cof.add(Fix(1L))
        n = n + 1
      } else if listp(v) && member_equal(u, cdr(v)).truthy() {
        if length(v) == 3 {
          let mut r : Value = Nil
          for vv in cdr(v).iter() {
            if !equal(vv, u) {
              r = vv
              break
            }
          }
          cof.add(r)
        } else {
          let r = Collector::new()
          for vv in v.iter() {
            if !equal(vv, u) {
              r.add(vv)
            }
          }
          cof.add(r.result())
        }
        n = n + 1
      }
    }
    let cof = cof.result()
    c.add(
      if cof is Nil {
        Fix(0L)
      } else if n == 1 {
        car(cof)
      } else {
        add_star(cof)
      },
    )
  }
  cons(car(pol), c.result())
}

///|
fn constant_psublis(alist : Value, polynomial : Value) -> Value raise {
  let alist = sort_list(alist, (a, b) => pointergp(car(a), car(b)).truthy())
  constant_psublis1(alist, polynomial)
}

///|
fn constant_psublis1(alist : Value, polynomial : Value) -> Value raise {
  if numberp(polynomial) {
    polynomial
  } else if alist is Nil {
    polynomial
  } else {
    let main_var = p__var(polynomial)
    let mut alist = alist
    while alist.truthy() && pointergp(caar(alist), main_var).truthy() {
      alist = cdr(alist)
    }
    if alist is Nil {
      polynomial
    } else if eql(caar(alist), main_var) {
      let repl = cdr(car(alist))
      let mut answ = afp_pctimes(
        constant_psublis1(cdr(alist), p__cof(polynomial)),
        cexpt(repl, p__deg(polynomial)),
      )
      let mut p = p__next_term(p__terms(polynomial))
      while p is Cons(_) {
        let deg = car(p)
        let cof = cadr(p)
        answ = pplus(
          answ,
          if zerop(deg) {
            constant_psublis1(cdr(alist), cof)
          } else {
            afp_pctimes(constant_psublis1(cdr(alist), cof), cexpt(repl, deg))
          },
        )
        p = p__next_term(p)
      }
      answ
    } else {
      let c = Collector::new()
      let mut p = p__terms(polynomial)
      while p is Cons(_) {
        let deg = car(p)
        let tem = constant_psublis1(alist, cadr(p))
        if !pzerop(tem).truthy() {
          c.add(deg)
          c.add(tem)
        }
        p = p__next_term(p)
      }
      psimp(main_var, c.result())
    }
  }
}

///|
fn my_evenp(n : Value) -> Value raise {
  let nn = ash(n, -1)
  if equal(ash(nn, 1), n) {
    nn
  } else {
    Nil
  }
}

///|
fn fast_gcd(m : Value, n : Value) -> Value raise {
  let mut m = num_abs(m)
  let mut n = num_abs(n)
  if !num_lt(n, m) {
    let x = m
    m = n
    n = x
  }
  if zerop(n) {
    m
  } else if fixnump(n) {
    m = num_mod(m, n)
    if zerop(m) {
      n
    } else {
      bin_gcd(m, n)
    }
  } else {
    num_gcd(n, num_mod(m, n))
  }
}

///|
fn bin_gcd(u : Value, v : Value) -> Value raise {
  let mut u = u
  let mut v = v
  let mut k : Value = Fix(0L)
  while true {
    let u2 = ash(u, -1)
    if !eql(ash(u2, 1), u) {
      break
    }
    let v2 = ash(v, -1)
    if !eql(ash(v2, 1), v) {
      break
    }
    u = u2
    v = v2
    k = one_plus(k)
  }
  // b2
  let mut tt = if oddp(u) { num_neg(v) } else { ash(u, -1) }
  while true {
    // b3b4
    while true {
      let t2 = ash(tt, -1)
      if eql(ash(t2, 1), tt) {
        tt = t2
      } else {
        break
      }
    }
    if num_gt(tt, Fix(0L)) {
      u = tt
    } else {
      v = num_neg(tt)
    }
    tt = num_sub(u, v)
    if zerop(tt) {
      return ash(u, to_int(k))
    }
  }
  Nil
}
