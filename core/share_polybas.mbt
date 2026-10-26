// Port of share/affine/polybas.lisp: basic operations on the affine
// package's polynomials (CRE polynomials and rational functions over the
// global masterlist *varlist* / *genvar*).

///|
fn affine_polynomialp(x : Value) -> Value raise {
  if numberp(x) {
    t
  } else if atom(x) {
    Nil
  } else if atom(car(x)) && symbolp(car(x)) {
    get(car(x), q_disrep)
  } else {
    Nil
  }
}

///|
fn header_poly(expr : Value) -> Value raise {
  if numberp(expr) {
    expr
  } else if numberp(car(expr)) && numberp(cdr(expr)) {
    if zerop(car(expr)) {
      Fix(0L)
    } else {
      list([list2(q_rat, q_simp), car(expr), cdr(expr)])
    }
  } else if affine_polynomialp(expr).truthy() {
    cons(polybas__mrat_header(), cons(expr, Fix(1L)))
  } else if rational_functionp(expr).truthy() {
    cons(polybas__mrat_header(), expr)
  } else {
    expr
  }
}

///|
/// `(list 'mrat 'simp *varlist* *genvar*)`
fn polybas__mrat_header() -> Value {
  list([q_mrat, q_simp, symval(q_ear_varlist), symval(q_ear_genvar)])
}

///|
fn d_zerop(n : Value) -> Value raise {
  if numberp(n) {
    lbool(zerop(n))
  } else if atom(n) {
    Nil
  } else if affine_polynomialp(n).truthy() {
    Nil
  } else if rational_functionp(n).truthy() {
    rzerop(n)
  } else if d_bfloatp(n).truthy() {
    lbool(eql(car(n), Fix(0L)))
  } else {
    let type_of_n = caar(n)
    if memq(type_of_n, list2(q_mrat, q_rat)) is Cons(_) {
      lbool(equal(cdr(n), rzero()))
    } else {
      let tem = d_ratsimp(n, Nil)
      lbool(numberp(tem) && zerop(tem))
    }
  }
}

///|
fn rational_functionp(x : Value) -> Value raise {
  if numberp(x) {
    t
  } else if atom(x) {
    Nil
  } else if affine_polynomialp(car(x)).truthy() {
    affine_polynomialp(cdr(x))
  } else {
    Nil
  }
}

///|
/// Does a general sublis: A-LIST of form (list (cons old-var repl-poly)
/// ...); DENOM is a poly.
fn psublis(
  a_list : Value,
  denom : Value,
  poly : Value,
  degree? : Value = Nil,
  vars_to_sub? : Value = Nil,
) -> Value raise {
  let tem = if vars_to_sub.truthy() {
    vars_to_sub
  } else {
    mapcar(v => car(v), a_list)
  }
  if affine_polynomialp(poly).truthy() {
    let deg = if degree.truthy() { degree } else { poly_degree(poly, tem) }
    psublis1(a_list, denom, poly, deg, tem)
  } else if rational_functionp(poly).truthy() {
    rsublis(a_list, denom, poly, degree~, vars_to_sub~, reduce_=t)
  } else if atom(poly) {
    poly
  } else {
    mapcar(v => psublis(a_list, denom, v, degree~, vars_to_sub~), poly)
  }
}

///|
/// Should take into account when the variables don't need replacing.
fn psublis1(
  a_list : Value,
  denom : Value,
  poly : Value,
  degree : Value,
  varl : Value,
) -> Value raise {
  if atom(poly) {
    ptimes(poly, pexpt(denom, degree))
  } else if memq(p__var(poly), varl) is Cons(_) {
    let mut answer : Value = Fix(0L)
    let mut r = cdr(poly)
    while r is Cons(_) {
      let deg = car(r)
      let cof = cadr(r)
      answer = pplus(
        answer,
        ptimes(
          psublis1(a_list, denom, cof, num_sub(degree, deg), varl),
          pexpt(cdr(assoc_equal(p__var(poly), a_list)), deg),
        ),
      )
      r = cddr(r)
    }
    answer
  } else if num_gt(valget(p__var(poly)), polybas__min_valget(varl)) {
    let mut answer : Value = Fix(0L)
    let mon = list3(p__var(poly), Fix(1L), Fix(1L))
    let mut r = cdr(poly)
    while r is Cons(_) {
      let deg = car(r)
      let cof = cadr(r)
      answer = pplus(
        answer,
        ptimes(pexpt(mon, deg), psublis1(a_list, denom, cof, degree, varl)),
      )
      r = cddr(r)
    }
    answer
  } else {
    ptimes(pexpt(denom, degree), poly)
  }
}

///|
/// `(loop for v in varl minimize (valget v))`
fn polybas__min_valget(varl : Value) -> Value raise {
  let mut m : Value = Nil
  for v in varl.iter() {
    let x = valget(v)
    if m is Nil || num_lt(x, m) {
      m = x
    }
  }
  if m is Nil {
    Fix(0L)
  } else {
    m
  }
}

///|
fn zero_sublis(poly : Value, list_vars : Value) -> Value raise {
  pcoeff(poly, Fix(1L), variables_to_exclude_from_cof=list_vars)
}

///|
fn pcomplexity(poly : Value) -> Value raise {
  if atom(poly) {
    Fix(0L)
  } else {
    let mut sum : Value = Fix(0L)
    let mut r = cdr(poly)
    while r is Cons(_) {
      sum = num_add(sum, num_add(car(r), pcomplexity(cadr(r))))
      r = cddr(r)
    }
    sum
  }
}

///|
fn d_numerator(expr : Value) -> Value raise {
  if atom(expr) {
    expr
  } else if mbagp(expr).truthy() {
    cons(car(expr), mapcar(x => d_numerator(x), cdr(expr)))
  } else if d_ratp(expr).truthy() {
    cons(car(expr), cons(car(cdr(expr)), Fix(1L)))
  } else {
    d_totaldisrep(header_poly(cons(num(new_rat(expr)), Fix(1L))))
  }
}

///|
/// The ALLOW-REST-ARGUMENT macro: NEW-FUNCT and BINARY-OP are function
/// designators, REST-ARG the list of arguments.
fn allow_rest_argument(
  new_funct : Value,
  binary_op : Value,
  answer_for_null_argument : Value,
  rest_arg : Value,
) -> Value raise {
  if rest_arg is Nil {
    answer_for_null_argument
  } else {
    match length(rest_arg) {
      2 => funcall(binary_op, [first(rest_arg), second(rest_arg)])
      1 => car(rest_arg)
      _ =>
        apply(
          new_funct,
          cons(
            funcall(binary_op, [first(rest_arg), second(rest_arg)]),
            cddr(rest_arg),
          ),
        )
    }
  }
}

///|
/// The POLYOP macro as a function of function designators.
fn polyop(
  x : Value,
  y : Value,
  identity_x : Value,
  identity_y : Value,
  number_op : Value,
  poly_op : Value,
  rat_op : Value,
  rat_switch? : Value = Nil,
) -> Value raise {
  let rat_fn : (Value, Value) -> Value raise = if rat_switch.truthy() {
    (a, b) => funcall(rat_op, [a, b, t])
  } else {
    (a, b) => funcall(rat_op, [a, b])
  }
  polybas__polyop(
    x,
    y,
    identity_x,
    identity_y,
    (a, b) => funcall(number_op, [a, b]),
    (a, b) => funcall(poly_op, [a, b]),
    rat_fn,
  )
}

///|
/// Expansion of POLYOP (RAT-OP already includes the rat-switch argument).
fn polybas__polyop(
  x : Value,
  y : Value,
  identity_x : Value,
  identity_y : Value,
  number_op : (Value, Value) -> Value raise,
  poly_op : (Value, Value) -> Value raise,
  rat_op : (Value, Value) -> Value raise,
) -> Value raise {
  let mut x = x
  let mut y = y
  if numberp(x) && numberp(y) {
    return number_op(x, y)
  }
  if eq(x, identity_x) {
    return y
  }
  if eq(y, identity_y) {
    return x
  }
  let mut xx = poly_type(x)
  let mut yy = poly_type(y)
  if xx is Nil {
    x = cdr(d_new_rat(x))
    xx = q_kw_rational_function
  } else if eq(xx, polybas__kw_drat) {
    x = cdr(x)
    xx = q_kw_rational_function
  } else if eq(xx, q_kw_rat) {
    x = cons(second(x), third(x))
    xx = q_kw_rational_function
  }
  if yy is Nil {
    y = cdr(d_new_rat(y))
    yy = q_kw_rational_function
  } else if eq(yy, polybas__kw_drat) {
    y = cdr(y)
    yy = q_kw_rational_function
  } else if eq(yy, q_kw_rat) {
    y = cons(second(y), third(y))
    yy = q_kw_rational_function
  }
  if eq(xx, q_kw_rational_function) && eql(denom(x), Fix(1L)) {
    x = car(x)
    xx = q_kw_polynomial
  }
  if eq(yy, q_kw_rational_function) && eql(denom(y), Fix(1L)) {
    y = car(y)
    yy = q_kw_polynomial
  }
  let answer = if eq(xx, q_kw_number) {
    if eq(yy, q_kw_number) {
      number_op(x, y)
    } else if eq(yy, q_kw_polynomial) {
      poly_op(x, y)
    } else if eq(yy, q_kw_rational_function) {
      rat_op(cons(x, Fix(1L)), y)
    } else {
      Nil
    }
  } else if eq(xx, q_kw_polynomial) {
    if eq(yy, q_kw_number) {
      poly_op(x, y)
    } else if eq(yy, q_kw_polynomial) {
      poly_op(x, y)
    } else if eq(yy, q_kw_rational_function) {
      rat_op(cons(x, Fix(1L)), y)
    } else {
      merror(Str("unknown type for polyop "), Nil)
    }
  } else if eq(xx, q_kw_rational_function) {
    if eq(yy, q_kw_number) {
      rat_op(x, cons(y, Fix(1L)))
    } else if eq(yy, q_kw_polynomial) {
      rat_op(x, cons(y, Fix(1L)))
    } else if eq(yy, q_kw_rational_function) {
      rat_op(x, y)
    } else {
      Nil
    }
  } else {
    merror(Str("unknown arg"), Nil)
  }
  if affine_polynomialp(answer).truthy() {
    answer
  } else if rational_functionp(answer).truthy() {
    if eq(Fix(1L), cdr(answer)) {
      car(answer)
    } else {
      answer
    }
  } else {
    answer
  }
}

///|
let polybas__kw_drat : Value = kw("$rat")

///|
fn n_star(l : Value) -> Value raise {
  match length(l) {
    0 => Fix(1L)
    1 => car(l)
    2 => n1_star(car(l), second(l))
    _ => n1_star(car(l), n_star(cdr(l)))
  }
}

///|
fn n_plus(x : Value, y : Value) -> Value raise {
  polybas__polyop(
    x,
    y,
    Fix(0L),
    Fix(0L),
    (a, b) => num_add(a, b),
    pplus,
    ratplus,
  )
}

///|
fn n1_star(x : Value, y : Value) -> Value raise {
  polybas__polyop(
    x,
    y,
    Fix(1L),
    Fix(1L),
    (a, b) => num_mul(a, b),
    ptimes,
    (a, b) => rattimes(a, b, t),
  )
}

///|
fn n__(x : Value, y : Value) -> Value raise {
  polybas__polyop(
    x,
    y,
    Nil,
    Fix(0L),
    (a, b) => num_sub(a, b),
    pdifference,
    ratdifference,
  )
}

///|
fn nred(x : Value, y : Value) -> Value raise {
  let mut answer = polybas__polyop(
    x,
    y,
    Nil,
    Fix(1L),
    ratreduce,
    ratreduce,
    ratquotient,
  )
  answer = rationalize_denom_zeta3(answer)
  if numberp(answer) {
    answer
  } else if eql(denom(answer), Fix(1L)) {
    car(answer)
  } else {
    answer
  }
}

///|
fn new_disrep(expr : Value) -> Value raise {
  if atom(expr) {
    return expr
  }
  let type_ = poly_type(expr)
  if eq(type_, q_kw_number) {
    expr
  } else if eq(type_, q_kw_polynomial) {
    d_ratdisrep(header_poly(expr))
  } else if eq(type_, q_kw_rational_function) {
    if d_numberp(expr).truthy() {
      if zerop(num(expr)) {
        Fix(0L)
      } else {
        list([list2(q_rat, q_simp), num(expr), denom(expr)])
      }
    } else {
      d_ratdisrep(header_poly(expr))
    }
  } else if mbagp(expr).truthy() {
    cons(car(expr), mapcar(x => new_disrep(x), expr))
  } else if d_ratp(expr).truthy() {
    d_ratdisrep(expr)
  } else {
    expr
  }
}

///|
fn poly_degree(poly : Value, varl : Value) -> Value raise {
  if atom(poly) {
    return Fix(0L)
  }
  let in_varl = memq(p__var(poly), varl) is Cons(_)
  let mut m : Value = Nil
  let mut r = cdr(poly)
  while r is Cons(_) {
    let x = if in_varl {
      num_add(car(r), poly_degree(cadr(r), varl))
    } else {
      poly_degree(cadr(r), varl)
    }
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

///|
fn shl(l : Value) -> Value raise {
  if symval(q_d_display2d).truthy() {
    mapcar(x => sh(x), l)
  } else {
    let n = length(l)
    format(t, "~%[", []) |> ignore
    let mut i = 0
    for v in l.iter() {
      if numberp(v) {
        princ(v) |> ignore
      } else {
        sh(header_poly(v)) |> ignore
      }
      if i < n - 1 {
        format(t, ",~%", []) |> ignore
      }
      i += 1
    }
    format(t, "]", []) |> ignore
    Nil
  }
}

///|
fn sh(expr : Value, stream? : Value) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_output)
  }
  let disp : (Value) -> Value raise = if symval(q_d_display2d).truthy() {
    x => displa(x)
  } else {
    x => string_grind(x)
  }
  let fake_rat = symval(q_ear_fake_rat)
  let answ = with_special(standard_output, stream, () => {
    if numberp(expr) {
      disp(expr)
    } else if affine_polynomialp(expr).truthy() {
      disp(cons(fake_rat, cons(expr, Fix(1L))))
    } else if rational_functionp(expr).truthy() {
      disp(cons(fake_rat, expr))
    } else {
      disp(expr)
    }
  })
  if answ.truthy() {
    format(t, "~A", [answ])
  } else {
    Nil
  }
}

///|
/// The SETQ-NUM-DEN macro cannot assign the caller's variables; this
/// returns `(num . den)` of EXPR (NUM and DEN are ignored).
fn setq_num_den(num : Value, den : Value, expr : Value) -> Value raise {
  ignore(num)
  ignore(den)
  if affine_polynomialp(expr).truthy() {
    cons(expr, Fix(1L))
  } else if rational_functionp(expr).truthy() {
    cons(car(expr), cdr(expr))
  } else {
    fsignal(list1(Str("expr is supposed to be poly or rational-functionp")))
  }
}

///|
fn splice_in(after_nth : Value, item : Value, a_list : Value) -> Value raise {
  if eql(after_nth, Fix(-1L)) {
    cons(item, a_list)
  } else {
    let n = to_int(after_nth)
    nconc(subseq(a_list, 0, end=n + 1), cons(item, cdr(nthcdr(n, a_list))))
  }
}

///|
fn nsplice_in(after_nth : Value, item : Value, a_list : Value) -> Value raise {
  if eql(after_nth, Fix(-1L)) {
    cons(item, a_list)
  } else {
    let tem = nthcdr(to_int(after_nth), a_list)
    setf_cdr(tem, cons(item, cdr(tem))) |> ignore
    a_list
  }
}

///|
fn nc_equal(p1 : Value, p2 : Value) -> Value raise {
  lbool(
    (atom(p1) && eql(p1, p2)) ||
    (listp(p1) && listp(p2) && equal(cdr(p1), cdr(p2))),
  )
}

///|
fn find_in_ordered_list(
  x : Value,
  a_list : Value,
  order_function? : Value,
  order_equal? : Value,
) -> (Value, Value, Value) raise {
  let order_function = match order_function {
    Some(f) => f
    None => q_alphalessp
  }
  let order_equal = match order_equal {
    Some(f) => f
    None => q_nc_equal
  }
  let mut a_list = a_list
  let leng = length(a_list)
  let mut after = 0
  let mut already_there : Value = Nil
  let mut tem : Value = Nil
  if funcall(order_function, [x, car(a_list)]).truthy() {
    after = -1
  } else if funcall(order_equal, [x, car(a_list)]).truthy() {
    after = 0
    already_there = a_list
  } else if {
      tem = last(a_list)
      funcall(order_equal, [x, car(tem)]).truthy()
    } {
    after = leng - 1
    already_there = tem
  } else if funcall(order_function, [x, car(tem)]) is Nil {
    after = leng - 1
  } else {
    let mut offset = 0
    let lbound = 0
    let mut ub = leng - 1
    let mut done = false
    while ub - lbound > 1 {
      let mid = (ub + lbound) / 2
      tem = nthcdr(mid, a_list)
      if funcall(order_function, [x, car(tem)]).truthy() {
        ub = mid
      } else if funcall(order_equal, [car(tem), x]).truthy() {
        after = offset + mid
        already_there = tem
        done = true
        break
      } else {
        offset = mid + offset
        a_list = tem
        ub = ub - mid
      }
    }
    if !done {
      after = offset
    }
  }
  if symval(q_ear_check_order).truthy() {
    tem = member_if_test(x, a_list, (a, b) => funcall(order_equal, [a, b]).truthy())
    if tem.truthy() {
      iassert(lbool(already_there.truthy())) |> ignore
      iassert(lbool(after == leng - length(tem))) |> ignore
    }
  }
  (int(after), already_there, a_list)
}

///|
/// Just substitutes the disrep property of a symbol for the symbol.
fn disrep_list(expr : Value) -> Value raise {
  if atom(expr) {
    if symbolp(expr) {
      get(expr, q_disrep)
    } else {
      expr
    }
  } else {
    cons(disrep_list(car(expr)), disrep_list(cdr(expr)))
  }
}

///|
fn check_repeats(varl : Value) -> Value raise {
  let mut v = varl
  while v is Cons(_) {
    if member_if_test(car(v), cdr(v), (a, b) => nc_equal(a, b).truthy()).truthy() {
      show(list1(car(v))) |> ignore
      fsignal(list1(Str("repeat in varlist"))) |> ignore
    }
    v = cdr(v)
  }
  Nil
}

///|
fn check_order(varl : Value) -> Value raise {
  let mut r = varl
  while r is Cons(_) {
    let v = car(r)
    let w = cadr(r)
    if w is Nil {
      break
    }
    if funcall(symval(q_d_order_function), [v, w]) is Nil {
      fsignal(list([Str("bad order ~A and ~A "), v, w])) |> ignore
    }
    r = cdr(r)
  }
  Nil
}

///|
fn generate_new_variable_gensym(variable : Value) -> Value raise {
  let tem = gensym()
  putprop(tem, variable, q_disrep) |> ignore
  set(q_genpairs, cons(cons(variable, rget(tem)), symval(q_genpairs))) |> ignore
  tem
}

///|
/// The WITH-VG macro: runs BODY (a function value of no arguments) with
/// varlist/genvar bound to *varlist*/*genvar*, then copies them back.
fn with_vg(body : Value) -> Value raise {
  with_specials(
    [(q_varlist, symval(q_ear_varlist)), (q_genvar, symval(q_ear_genvar))],
    () => {
      funcall(body, []) |> ignore
      set(q_ear_varlist, symval(q_varlist)) |> ignore
      set(q_ear_genvar, symval(q_genvar))
    },
  )
}

///|
/// The WITH-VGP macro: BODY is a function value of no arguments.
fn with_vgp(body : Value) -> Value raise {
  with_specials(
    [
      (q_varlist, symval(q_ear_varlist)),
      (q_genvar, symval(q_ear_genvar)),
      (q_genpairs, symval(q_ear_genpairs)),
    ],
    () => {
      let r = funcall(body, [])
      set(q_ear_varlist, symval(q_varlist)) |> ignore
      set(q_ear_genpairs, symval(q_genpairs)) |> ignore
      set(q_ear_genvar, symval(q_genvar)) |> ignore
      r
    },
  )
}

///|
fn zl_union(l : Value) -> Value raise {
  match length(l) {
    1 => {
      let c = Collector::new()
      let mut v = car(l)
      while v is Cons(_) {
        if member(car(v), cdr(v)) is Nil {
          c.add(car(v))
        }
        v = cdr(v)
      }
      c.result()
    }
    2 => {
      let sec = second(l)
      let c = Collector::new()
      for v in car(l).iter() {
        if member(v, sec) is Nil {
          c.add(v)
        }
      }
      nconc(c.result(), zl_union(list1(sec)))
    }
    _ => zl_union(list2(car(l), zl_union(cdr(l))))
  }
}

///|
fn init_share_polybas() -> Unit raise {
  ()
}
