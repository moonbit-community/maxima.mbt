// Translation of share/affine/sub-proj.lisp: substitutions and pseudo
// division on CRE polynomials for the affine package.

///|
/// Does a substitution like var --> var/denom where var is a genvar and
/// denom is a poly.  It calculates the numerator after bringing a common
/// denominator of denom^(pdegree poly var).
fn rational_subst(poly : Value, var_ : Value, denom : Value) -> Value raise {
  let deg = pdegree(poly, var_)
  let poly = copy_tree(poly)
  sub_rat2(poly, var_, denom, deg)
}

///|
/// The macro SUM-OVER-POLYNOMIAL binds DEG and COF to each degree and
/// coefficient of POLY and sums the SUMMAND form.  As a function the
/// summand must be a function designator called with (deg cof).
fn sum_over_polynomial(
  deg : Value,
  cof : Value,
  poly : Value,
  summand : Value,
) -> Value raise {
  ignore(deg)
  ignore(cof)
  sub_proj__sum_over(poly, (d, c) => funcall(summand, [d, c]))
}

///|
fn sub_proj__sum_over(
  poly : Value,
  summand : (Value, Value) -> Value raise,
) -> Value raise {
  let mut tail = cdr(poly)
  let mut answer : Value = Fix(0L)
  while !(tail is Nil) {
    let c = cadr(tail)
    let d = car(tail)
    answer = pplus(answer, summand(d, c))
    tail = cddr(tail)
  }
  answer
}

///|
/// The macro REPLACE-POLYNOMIAL-COEFFICIENTS replaces each coefficient of
/// POLY (destructively) by the REPLACEMENT form evaluated with DEG and COF
/// bound.  As a function the replacement must be a function designator
/// called with (deg cof).
fn replace_polynomial_coefficients(
  deg : Value,
  cof : Value,
  poly : Value,
  replacement : Value,
) -> Value raise {
  ignore(deg)
  ignore(cof)
  sub_proj__replace_coefficients(poly, (d, c) => funcall(replacement, [d, c]))
}

///|
fn sub_proj__replace_coefficients(
  poly : Value,
  replacement : (Value, Value) -> Value raise,
) -> Value raise {
  let mut tail = cdr(poly)
  while !(tail is Nil) {
    let c = cadr(tail)
    let d = car(tail)
    rplaca(cdr(tail), replacement(d, c)) |> ignore
    tail = cddr(tail)
  }
  poly
}

///|
fn d_degree(form : Value, var_ : Value) -> Value raise {
  let form = st_rat(form)
  pdegree(form, car(st_rat(var_)))
}

///|
fn sub_rat2(poly : Value, var_ : Value, denom : Value, deg : Value) -> Value raise {
  let mut poly = poly
  if atom(poly) {
    poly = ptimes(poly, pexpt(denom, deg))
  } else if eq(car(poly), var_) {
    if pointergp(var_, car(denom)).truthy() {
      sub_proj__replace_coefficients(poly, (degree, cof) => ptimes(
        cof,
        pexpt(denom, num_sub(deg, degree)),
      ))
      |> ignore
    } else {
      let p = poly
      poly = sub_proj__sum_over(p, (degree, cof) => ptimes(
        list([car(p), degree, Fix(1L)]),
        ptimes(cof, pexpt(denom, num_sub(deg, degree))),
      ))
    }
  } else if pointergp(car(poly), var_).truthy() {
    if pointergp(car(poly), car(denom)).truthy() {
      print(q_a) |> ignore
      sub_proj__replace_coefficients(poly, (_degree, cof) => sub_rat2(
        cof, var_, denom, deg,
      ))
      |> ignore
    } else {
      print(q_b) |> ignore
      let p = poly
      poly = sub_proj__sum_over(p, (degree, cof) => ptimes(
        list([car(p), degree, Fix(1L)]),
        sub_rat2(cof, var_, denom, deg),
      ))
    }
  } else {
    poly = ptimes(poly, pexpt(denom, deg))
  }
  poly
}

///|
fn d_sub1(
  poly : Value,
  var_ : Value,
  denom : Value,
  deg? : Value = Nil,
) -> Value raise {
  ignore(deg)
  let poly = st_rat(poly)
  let var_ = car(st_rat(var_))
  let denom = st_rat(denom)
  header_poly(rational_subst(poly, var_, denom))
}

///|
/// This substitutes for var (a genvar) the repl (a poly) staying in cre form.
fn poly_subst(poly : Value, var_ : Value, repl : Value) -> Value raise {
  poly_subst1(copy_tree(poly), var_, repl)
}

///|
fn poly_subst1(poly : Value, var_ : Value, repl : Value) -> Value raise {
  let mut poly = poly
  if atom(poly) {
    ()
  } else if eq(car(poly), var_) {
    let mut tail = cdr(poly)
    let mut answer : Value = Fix(0L)
    while !(tail is Nil) {
      answer = pplus(ptimes(pexpt(repl, car(tail)), cadr(tail)), answer)
      tail = cddr(tail)
    }
    poly = answer
  } else if pointergp(car(poly), car(repl)).truthy() {
    let mut tail = cdr(poly)
    while !(tail is Nil) {
      rplaca(cdr(tail), poly_subst(cadr(tail), var_, repl)) |> ignore
      tail = cddr(tail)
    }
  } else if eql(Fix(0L), pdegree(poly, var_)) {
    ()
  } else {
    let mut tail = cdr(poly)
    let mut answer : Value = Fix(0L)
    while !(tail is Nil) {
      answer = pplus(
        answer,
        ptimes(
          list([car(poly), car(tail), Fix(1L)]),
          poly_subst(cadr(tail), var_, repl),
        ),
      )
      tail = cddr(tail)
    }
    poly = answer
  }
  poly
}

///|
fn d_polysub(poly : Value, var_ : Value, repl : Value) -> Value raise {
  let poly = st_rat(poly)
  let var_ = car(st_rat(var_))
  let repl = st_rat(repl)
  header_poly(poly_subst(poly, var_, repl))
}

///|
/// Does a general sublis: a-list of form (list (cons old-var repl-poly)...),
/// denom is a poly.
fn rsublis(
  a_list : Value,
  denom : Value,
  poly : Value,
  degree? : Value = Nil,
  vars_to_sub? : Value = Nil,
  reduce_? : Value = Nil,
) -> Value raise {
  let tem = if vars_to_sub.truthy() {
    vars_to_sub
  } else {
    mapcar(v => car(v), a_list)
  }
  if affine_polynomialp(poly).truthy() {
    let deg = if degree.truthy() { degree } else { poly_degree(poly, tem) }
    let answ = psublis1(a_list, denom, poly, deg, tem)
    if reduce_.truthy() {
      ratreduce(answ, pexpt(denom, deg))
    } else {
      cons(answ, pexpt(denom, deg))
    }
  } else if rational_functionp(poly).truthy() {
    ratquotient(
      rsublis(a_list, denom, num(poly), degree~, vars_to_sub~),
      rsublis(a_list, denom, cdr(poly), degree~, vars_to_sub~),
    )
  } else {
    merr("bad type for poly : should be ratl fn or poly", [])
  }
}

///|
/// use psublis([y=x^2,v=u^3],denom,poly)
fn d_psublis(a_list : Value, denom : Value, poly : Value) -> Value raise {
  let subs = Collector::new()
  for e in cdr(a_list).iter() {
    let u = car(e)
    let v = cadr(e)
    let repl = caddr(e)
    if !eq(car(u), q_mequal) {
      raise LispError::SimpleError("Type a=repl")
    }
    subs.add(cons(p__var(st_rat(v)), st_rat(repl)))
  }
  header_poly(psublis(subs.result(), st_rat(denom), st_rat(poly)))
}

///|
/// CL (apply 'append lists).
fn sub_proj__append_all(lists : Value) -> Value raise {
  match lists {
    Nil => Nil
    Cons({ car: x, cdr: Nil }) => x
    Cons({ car: x, cdr: more }) => {
      if !(x is Nil || x is Cons(_)) {
        raise LispError::SimpleError("The value \{princ_to_string(x)} is not of type LIST")
      }
      append(x, sub_proj__append_all(more))
    }
    _ => Nil
  }
}

///|
fn d_coll_linear(expr : Value) -> Value raise {
  let answ = if mbagp(expr).truthy() {
    mapcar(v => coll_linear(st_rat(v)), cdr(expr))
  } else {
    coll_linear(expr)
  }
  let answ = sub_proj__append_all(answ)
  cons(list1(q_mlist), mapcar(w => get(w, q_disrep), answ))
}

///|
fn psubst(repl : Value, var_ : Value, poly : Value) -> Value raise {
  psublis(list1(cons(var_, repl)), Fix(1L), poly)
}

///|
let sub_proj__q_kw_main : Value = sym(":main")

///|
/// Prints like the SHOW macro: "~%The value of NAME is VALUE".
fn sub_proj__show(name : String, v : Value) -> Unit raise {
  format(t, "~%The value of ~A is ~A", [Str(name), v]) |> ignore
}

///|
/// Prints like the MSHOW macro (amacros.lisp).
fn sub_proj__mshow(name : String, v : Value) -> Unit raise {
  format(t, "~%The value of ~A is.. ", [Str(name)]) |> ignore
  des(v) |> ignore
}

///|
fn pdiscriminant(poly : Value, var_ : Value) -> Value raise {
  let mut poly = poly
  let mut var_ = var_
  let mut main : Value = Nil
  let mut old_var : Value = Nil
  if eq(var_, sub_proj__q_kw_main) {
    var_ = p__var(poly)
  } else if !eql(var_, p__var(poly)) {
    main = gensym()
    set(main, Fix(40000000L)) |> ignore
    putprop(main, q_main_var, q_disrep) |> ignore
    sub_proj__show("MAIN", main)
    old_var = var_
    poly = psubst(list([main, Fix(1L), Fix(1L)]), var_, poly)
    print(q_hi) |> ignore
    var_ = main
  }
  sub_proj__show("POLY", poly)
  sub_proj__mshow("POLY", poly)
  let answ = resultant(poly, pderivative(poly, var_))
  if main.truthy() {
    psublis(list1(cons(main, list([old_var, Fix(1L), Fix(1L)]))), Fix(1L), answ)
  } else {
    answ
  }
}

///|
/// sub-proj.lisp's PRESULTANT, which redefines algsys.lisp's when the
/// affine package is loaded.  Installed in the function cell by
/// init_share_sub_proj.
fn sub_proj__presultant(p1 : Value, p2 : Value, var_ : Value) -> Value raise {
  if p1 is Cons(_) &&
    p2 is Cons(_) &&
    eq(p__var(p1), p__var(p2)) &&
    eq(var_, p__var(p1)) {
    resultant(p1, p2)
  } else {
    // (with-main var args t (resultant (car args) (second args)))
    let args = list([p1, p2])
    let newvar = make_symbol("zzzzzz")
    let oldmain = var_
    set(newvar, Fix(40000L)) |> ignore
    putprop(newvar, q_zzzzzzz, q_disrep) |> ignore
    let args = psublis(
      list1(cons(oldmain, list([newvar, Fix(1L), Fix(1L)]))),
      Fix(1L),
      args,
    )
    psublis(
      list1(cons(newvar, list([oldmain, Fix(1L), Fix(1L)]))),
      Fix(1L),
      resultant(car(args), cadr(args)),
    )
  }
}

///|
fn gen_vrem(b : Value, divisor : Value) -> Value raise {
  if atom(divisor) {
    Fix(0L)
  } else if atom(b) {
    b
  } else if pointergp(p__var(divisor), p__var(b)).truthy() {
    b
  } else if eq(p__var(divisor), p__var(b)) {
    cadr(vdivide(b, divisor))
  } else if pointergp(p__var(b), p__var(divisor)).truthy() {
    let lis = Collector::new()
    let mut tail = cdr(b)
    while !(tail is Nil) {
      let deg = car(tail)
      let cof = cadr(tail)
      let tem = gen_vrem(cof, divisor)
      if !pzerop(tem).truthy() {
        lis.add(deg)
        lis.add(tem)
      }
      tail = cddr(tail)
    }
    let lis = lis.result()
    if eql(car(lis), Fix(0L)) {
      cadr(lis)
    } else {
      cons(p__var(b), lis)
    }
  } else {
    Nil
  }
}

///|
fn highest_power_dividing(f : Value, divisor : Value) -> (Value, Value) raise {
  let mut prev_quot = f
  let mut i = 1L
  while true {
    let quot = testdivide(prev_quot, divisor)
    if quot is Nil {
      return (Fix(i - 1L), prev_quot)
    }
    prev_quot = quot
    i = i + 1L
  }
  (Nil, Nil)
}

///|
/// c-reqd*f=g*quot+remaind
fn gen_prem(f : Value, g : Value, var_ : Value) -> (Value, Value) raise {
  let mut remainder : Value = Nil
  let mut c_reqd : Value = Nil
  if num_lt(pdegree(f, var_), pdegree(g, var_)) {
    remainder = f
    c_reqd = Fix(1L)
  } else if eq(p__var(f), p__var(g)) && eq(p__var(f), var_) {
    remainder = vdivide(f, g)
    c_reqd = caddr(remainder)
    remainder = cadr(remainder)
  } else {
    // (with-main-variable u ...)
    let u = make_symbol("zzzzzz")
    set(u, Fix(40000L)) |> ignore
    putprop(u, q_zzzzzzz, q_disrep) |> ignore
    let f = psublis(list1(cons(var_, list([u, Fix(1L), Fix(1L)]))), Fix(1L), f)
    let g = psublis(list1(cons(var_, list([u, Fix(1L), Fix(1L)]))), Fix(1L), g)
    remainder = vdivide(f, g)
    // this should not involve main variable..
    c_reqd = caddr(remainder)
    remainder = cadr(remainder)
    remainder = psublis(
      list1(cons(u, list([var_, Fix(1L), Fix(1L)]))),
      Fix(1L),
      remainder,
    )
  }
  (remainder, c_reqd)
}

///|
/// works now c*b=q*divisor +r
fn vdivide(b : Value, divisor : Value) -> Value raise {
  let mut q : Value = Fix(0L)
  let mut c : Value = Fix(1L)
  let mut r = b
  if atom(divisor) {
    list([b, Fix(0L), divisor])
  } else if atom(b) {
    list([Fix(0L), b, Fix(1L)])
  } else if pointergp(p__var(divisor), p__var(b)).truthy() {
    list([Fix(0L), b, Fix(1L)])
  } else if pointergp(p__var(b), p__var(divisor)).truthy() {
    list([b, Fix(0L), divisor])
  } else {
    let mon = list([p__var(r), Fix(1L), Fix(1L)])
    while !(atom(r) ||
      !eql(p__var(r), p__var(divisor)) ||
      num_lt(p__le(r), p__le(divisor))) {
      let leading_gcd = pgcd(p__lc(r), p__lc(divisor))
      let rfactor = pquotient(p__lc(divisor), leading_gcd)
      // make r so that you can form r-divisor*q ==> lower degree
      let rnew = ptimes(rfactor, r)
      c = ptimes(c, rfactor)
      // want rnew-divisor*deltaq to be lower degree in main variable
      // so need (p-lc deltaq) = (p-lc rnew)/(p-lc divisor)
      // but (p-lc rnew)=(p-lc divisor) (p-lc r) /leading-gcd
      // so (p-lc r)/leading-gcd will be the right (p-lc deltaq)
      // then multiply by (p-var r)^ m where m=(difference of leading degrees)
      let deltaq = ptimes(
        pquotient(p__lc(r), leading_gcd),
        pexpt(mon, num_sub(p__le(r), p__le(divisor))),
      )
      r = pdifference(rnew, ptimes(divisor, deltaq))
      q = pplus(ptimes(rfactor, q), deltaq)
    }
    list([q, r, c])
  }
}

///|
fn coll_linear(f : Value) -> Value raise {
  with_special(q_ear_linear, Nil, () => {
    coll_linear1(f) |> ignore
    symval(q_ear_linear)
  })
}

///|
fn constant_polyp(f : Value) -> Value raise {
  if atom(f) {
    t
  } else if get(car(f), q_constant).truthy() {
    t
  } else {
    let mut tail = cdr(f)
    while !(tail is Nil) {
      if constant_polyp(cadr(f)) is Nil {
        return Nil
      }
      tail = cddr(tail)
    }
    t
  }
}

///|
fn coll_linear1(poly : Value) -> Value raise {
  // here we collect things that look linear but u*z+u would collect u
  if atom(poly) {
    ()
  } else if get(car(poly), q_constant).truthy() {
    let mut tail = cdr(poly)
    while !(tail is Nil) {
      coll_linear1(cadr(tail)) |> ignore
      tail = cddr(tail)
    }
  } else {
    if eql(p__le(poly), Fix(1L)) && constant_functionp(p__lc(poly)).truthy() {
      let v = p__var(poly)
      if memq(v, symval(q_ear_linear)) is Nil {
        set(q_ear_linear, cons(v, symval(q_ear_linear))) |> ignore
      }
    }
    if eql(Fix(0L), nth(length(poly) - 2, poly)) {
      coll_linear1(car(last(poly))) |> ignore
    }
  }
  // now must check these are really linear to remove the u collected above.
  if poly is Cons(_) {
    let ldeg : Value = if get(p__var(poly), q_constant).truthy() {
      Fix(1L)
    } else {
      Fix(0L)
    }
    for u in symval(q_ear_linear).iter() {
      let mut tail = cdr(poly)
      while !(tail is Nil) {
        let deg = car(tail)
        let cof = cadr(tail)
        if !num_gt(deg, Fix(0L)) {
          break
        }
        if num_gt(pdegree(cof, u), ldeg) {
          set(q_ear_linear, delete(u, symval(q_ear_linear))) |> ignore
        }
        tail = cddr(tail)
      }
    }
  }
  Nil
}

///|
fn gen_psublis(old : Value, new_ : Value, poly : Value) -> Value raise {
  let (subs, denom) = subs_for_psublis(old, new_)
  psublis(subs, denom, poly)
}

///|
fn gen_rat_sublis(
  old : Value,
  new_ : Value,
  f : Value,
  switch? : Value = t,
) -> Value raise {
  ignore(switch)
  simple_rat_sublis(subs_for_simple_rat_sublis(old, new_), f)
}

///|
fn subs_for_psublis(old : Value, new_ : Value) -> (Value, Value) raise {
  let mut old = old
  let mut new_ = new_
  let mut lcd : Value = Fix(1L)
  let mut a_denom = false
  if d_listp(old).truthy() {
    old = cdr(old)
  }
  if d_listp(new_).truthy() {
    new_ = cdr(new_)
  }
  for v in old.iter() {
    if get(v, q_disrep) is Nil {
      let tem = Collector::new()
      for v in old.iter() {
        let mut v = v
        if get(v, q_disrep) is Nil {
          if v is Sym(_) || v is Nil {
            v = add_newvar(v).0
          } else {
            merr("only for replacing symbols", []) |> ignore
          }
        }
        tem.add(v)
      }
      old = tem.result()
      break
    }
  }
  let coll = Collector::new()
  for v in new_.iter() {
    let mut v = v
    if v is Sym(_) || v is Nil {
      if get(v, q_disrep).truthy() {
        v = list([v, Fix(1L), Fix(1L)])
      } else {
        v = st_rat(v)
      }
    } else if affine_polynomialp(v).truthy() {
      ()
    } else {
      v = new_rat(v)
      a_denom = true
      lcd = plcm(lcd, denom(v))
    }
    coll.add(v)
  }
  new_ = coll.result()
  if a_denom {
    let mut w = new_
    while w is Cons(_) {
      if affine_polynomialp(car(w)).truthy() {
        rplaca(w, gen_ptimes(list([lcd, car(w)]))) |> ignore
      } else {
        rplaca(
          w,
          gen_ptimes(list([num(car(w)), pquotient(lcd, denom(car(w)))])),
        )
        |> ignore
      }
      w = cdr(w)
    }
  } else {
    new_ = subseq(new_, 0, end=length(old))
  }
  let mut o = old
  let mut w = new_
  while o is Cons(_) && w is Cons(_) {
    rplaca(w, cons(car(o), car(w))) |> ignore
    o = cdr(o)
    w = cdr(w)
  }
  (new_, lcd)
}

///|
fn simple_rat_sublis(subs : Value, f : Value, switch? : Value = t) -> Value raise {
  if atom(f) {
    cons(f, Fix(1L))
  } else if numberp(car(f)) && numberp(cdr(f)) {
    f
  } else if affine_polynomialp(f).truthy() {
    let mut sub = cdr(assoc_equal(p__var(f), subs))
    if sub is Nil {
      sub = cons(list([p__var(f), Fix(1L), Fix(1L)]), Fix(1L))
    }
    let mut answ = cons(Fix(0L), Fix(1L))
    let mut tail = cdr(f)
    while !(tail is Nil) {
      let deg = car(tail)
      let cof = cadr(tail)
      answ = ratplus(
        answ,
        rattimes(ratexpt(sub, deg), simple_rat_sublis(subs, cof), switch),
      )
      tail = cddr(tail)
    }
    answ
  } else if rational_functionp(f).truthy() {
    ratquotient(
      simple_rat_sublis(subs, num(f), switch~),
      simple_rat_sublis(subs, denom(f), switch~),
    )
  } else {
    mapcar(v => simple_rat_sublis(subs, v, switch~), f)
  }
}

///|
fn subs_for_simple_rat_sublis(varl : Value, subs : Value) -> Value raise {
  let out = Collector::new()
  let mut vl = varl
  let mut sl = subs
  while vl is Cons(_) && sl is Cons(_) {
    let mut v = car(vl)
    let mut w = car(sl)
    if get(v, q_disrep) is Nil {
      v = add_newvar(v).0
    }
    if affine_polynomialp(w).truthy() {
      w = cons(w, Fix(1L))
    } else if rational_functionp(w).truthy() {
      ()
    } else if get(w, q_disrep).truthy() {
      w = cons(list([w, Fix(1L), Fix(1L)]), Fix(1L))
    } else {
      w = new_rat(w)
    }
    out.add(cons(v, w))
    vl = cdr(vl)
    sl = cdr(sl)
  }
  out.result()
}

///|
/// Returns a list of all coefficients of all monomials in VARIABLES
/// occurring in POLY.
fn collect_monomial_coefficients(poly : Value, variables : Value) -> Value raise {
  if variables is Nil {
    list1(poly)
  } else if d_zerop(poly).truthy() {
    list1(poly)
  } else {
    let n = pdegree(poly, car(variables))
    let parts = Collector::new()
    let mut i : Value = Fix(0L)
    while num_le(i, n) {
      let part = if num_ge(i, Fix(1L)) {
        collect_monomial_coefficients(
          pcoeff(poly, list([car(variables), i, Fix(1L)])),
          cdr(variables),
        )
      } else {
        collect_monomial_coefficients(
          pcoeff(
            poly,
            Fix(1L),
            variables_to_exclude_from_cof=subseq(variables, 0, end=1),
          ),
          cdr(variables),
        )
      }
      for x in part.iter() {
        parts.add(x)
      }
      i = num_add(i, Fix(1L))
    }
    parts.result()
  }
}

///|
/// Returns a list of two element lists, each whose first element is the
/// monomial and whose second is the coefficient.
fn collect_monomial_coefficients_and_monomials(
  poly : Value,
  variables : Value,
  monomial? : Value = Fix(1L),
) -> Value raise {
  if variables is Nil {
    list1(list([monomial, poly]))
  } else {
    let n = pdegree(poly, car(variables))
    let parts = Collector::new()
    let mut i : Value = Fix(0L)
    while num_le(i, n) {
      let mon = list([car(variables), i, Fix(1L)])
      let part = if num_ge(i, Fix(1L)) {
        collect_monomial_coefficients_and_monomials(
          pcoeff(poly, mon),
          cdr(variables),
          monomial=ptimes(monomial, mon),
        )
      } else {
        collect_monomial_coefficients_and_monomials(
          pcoeff(
            poly,
            Fix(1L),
            variables_to_exclude_from_cof=subseq(variables, 0, end=1),
          ),
          cdr(variables),
          monomial~,
        )
      }
      for x in part.iter() {
        parts.add(x)
      }
      i = num_add(i, Fix(1L))
    }
    parts.result()
  }
}

///|
fn collect_and_verify_coefficients(poly : Value, variables : Value) -> Value raise {
  let answ = collect_monomial_coefficients_and_monomials(poly, variables)
  let mut answer : Value = Fix(0L)
  for v in answ.iter() {
    answer = pplus(answer, ptimes(car(v), cadr(v)))
  }
  // (iassert (equal answer poly))
  if !equal(answer, poly) {
    fsignal(
      list([
        Str("The expression ~A was not true"),
        Str("(EQUAL ANSWER POLY)"),
      ]),
    )
    |> ignore
  }
  mapcar(v => cadr(v), answ)
}

///|
fn va(h : Value) -> Value raise {
  list_variables(st_rat(h))
}

///|
fn init_share_sub_proj() -> Unit raise {
  // sub-proj.lisp redefines PRESULTANT (algsys.lisp) at load time.
  defun(
    q_presultant,
    args => sub_proj__presultant(arg(args, 0), arg(args, 1), arg(args, 2)),
  )
}
