// Port of share/contrib/Grobner/grobner.lisp (part 2): postprocessing of
// Grobner bases, algorithm selection, ideal operations, conversion between
// Maxima expressions and the internal representation, the Maxima-level
// interface and the file's top-level forms.

///|
let share_grobner__q_kw_termlist : Value = sym(":termlist")

///|
let share_grobner__q_kw_poly_list : Value = sym(":poly-list")

///|
let share_grobner__q_grlex : Value = sym("grlex")

///|
let share_grobner__q_kw_grlex : Value = sym(":grlex")

///|
let share_grobner__q_grevlex : Value = sym("grevlex")

///|
let share_grobner__q_kw_grevlex : Value = sym(":grevlex")

///|
let share_grobner__q_invlex : Value = sym("invlex")

///|
let share_grobner__q_kw_invlex : Value = sym(":invlex")

///|
let share_grobner__q_kw_lex : Value = sym(":lex")

///|
let share_grobner__q_kw_elimination_order_1 : Value = sym(
  ":elimination-order-1",
)

///|
let share_grobner__q_elimination_order_1u : Value = sym("elimination_order_1")

///|
let share_grobner__q_expression_ring : Value = sym("expression-ring")

///|
let share_grobner__q_kw_expression_ring : Value = sym(":expression-ring")

///|
let share_grobner__q_ring_of_integers : Value = sym("ring-of-integers")

///|
let share_grobner__q_kw_ring_of_integers : Value = sym(":ring-of-integers")

///|
let share_grobner__head_mlist : Value = list1(q_mlist)

///|
let share_grobner__head_mplus : Value = list1(q_mplus)

// ---------------------------------------------------------------------------
// Standard postprocessing of Grobner bases

///|
/// Reduce PLIST so that no term of any polynomial is divisible by the
/// leading monomial of another polynomial.
fn reduction(ring : Value, plist : Value) -> Value raise {
  let mut q = plist
  let mut found = true
  while found {
    // Find p in Q such that p is reducible mod Q\{p}
    found = false
    for x in q.iter() {
      let q1 = remove(x, q)
      let (h, _, div_count) = normal_form(
        ring,
        x,
        q1,
        top_reduction_only=Nil, // not a top reduction!
      )
      if !zerop(div_count) {
        found = true
        q = q1
        if !share_grobner__zerop(h) {
          q = nconc(q1, list1(h))
        }
        break
      }
    }
  }
  mapcar(x => poly_primitive_part(ring, x).0, q)
}

///|
/// A sublist of P spanning the same monomial ideal as P but minimal.
fn minimization(p : Value) -> Value raise {
  let mut q = p
  let mut found = true
  while found {
    // Find p in Q such that lm(p) is in LM(Q\{p})
    found = false
    let mut next = q
    for x in q.iter() {
      let q1 = remove(x, q)
      if some(p => monom_divides_p(poly_lm(x), poly_lm(p)).truthy(), q1) {
        found = true
        next = q1
        break
      }
    }
    q = next
  }
  q
}

///|
/// Divide a polynomial by its leading coefficient (in place).
fn poly_normalize(ring : Value, p : Value) -> Value raise {
  let c = poly_lc(p)
  for term in share_grobner__poly_termlist(p).iter() {
    struct_set(
      term,
      1,
      share_grobner__rdiv(ring, share_grobner__term_coeff(term), c),
    )
    |> ignore
  }
  p
}

///|
fn poly_normalize_list(ring : Value, plist : Value) -> Value raise {
  mapcar(x => poly_normalize(ring, x), plist)
}

// ---------------------------------------------------------------------------
// Algorithm and pair heuristic selection

///|
/// The function computing Grobner bases named ALGORITHM.
fn find_grobner_function(algorithm : Value) -> Value raise {
  if eq(algorithm, q_buchberger) ||
    eq(algorithm, share_grobner__q_kw_buchberger) ||
    eq(algorithm, q_d_buchberger) {
    q_buchberger
  } else if eq(algorithm, q_parallel_buchberger) ||
    eq(algorithm, share_grobner__q_kw_parallel_buchberger) ||
    eq(algorithm, q_d_parallel_buchberger) {
    q_parallel_buchberger
  } else if eq(algorithm, q_gebauer_moeller) ||
    eq(algorithm, share_grobner__q_kw_gebauer_moeller) ||
    eq(algorithm, q_d_gebauer_moeller) {
    q_gebauer_moeller
  } else {
    raise LispError::SimpleError(
      format_to_string(
        "~S fell through ECASE expression.~%Wanted one of (BUCHBERGER :BUCHBERGER $BUCHBERGER PARALLEL-BUCHBERGER :PARALLEL-BUCHBERGER $PARALLEL_BUCHBERGER GEBAUER-MOELLER :GEBAUER_MOELLER $GEBAUER_MOELLER).",
        [algorithm],
      ),
    )
  }
}

///|
fn grobner(
  ring : Value,
  f : Value,
  start? : Value = Fix(0L),
  top_reduction_only? : Value = Nil,
) -> Value raise {
  funcall(find_grobner_function(symval(q_d_poly_grobner_algorithm)), [
    ring,
    f,
    start,
    top_reduction_only,
  ])
}

///|
fn reduced_grobner(
  ring : Value,
  f : Value,
  start? : Value = Fix(0L),
  top_reduction_only? : Value,
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  reduction(ring, grobner(ring, f, start~, top_reduction_only~))
}

///|
/// Set `*pair-key-function*` and `*pair-order*`, which determine the
/// priority of critical pairs.
fn set_pair_heuristic(method_ : Value) -> Value raise {
  let m = method_
  if eq(m, share_grobner__q_sugar) ||
    eq(m, share_grobner__q_kw_sugar) ||
    eq(m, q_d_sugar) {
    set(q_ear_pair_key_function, share_grobner__sugar_pair_key_fn) |> ignore
    set(q_ear_pair_order, share_grobner__sugar_order_fn)
  } else if eq(m, share_grobner__q_minimal_lcm) ||
    eq(m, share_grobner__q_kw_minimal_lcm) ||
    eq(m, q_d_minimal_lcm) {
    set(
      q_ear_pair_key_function,
      lfunc("minimal-lcm-key", args => monom_lcm(
        poly_lm(arg(args, 0)),
        poly_lm(arg(args, 1)),
      )),
    )
    |> ignore
    set(q_ear_pair_order, share_grobner__reverse_monomial_order_fn)
  } else if eq(m, share_grobner__q_minimal_total_degree) ||
    eq(m, share_grobner__q_kw_minimal_total_degree) ||
    eq(m, q_d_minimal_total_degree) {
    set(
      q_ear_pair_key_function,
      lfunc("minimal-total-degree-key", args => monom_total_degree(
        monom_lcm(poly_lm(arg(args, 0)), poly_lm(arg(args, 1))),
      )),
    )
    |> ignore
    set(q_ear_pair_order, share_grobner__lt_fn)
  } else if eq(m, share_grobner__q_minimal_length) ||
    eq(m, share_grobner__q_kw_minimal_length) ||
    eq(m, q_d_minimal_length) {
    set(
      q_ear_pair_key_function,
      lfunc("minimal-length-key", args => num_add(
        poly_length(arg(args, 0)),
        poly_length(arg(args, 1)),
      )),
    )
    |> ignore
    set(q_ear_pair_order, share_grobner__lt_fn)
  } else {
    raise LispError::SimpleError(
      format_to_string(
        "~S fell through ECASE expression.~%Wanted one of (SUGAR :SUGAR $SUGAR MINIMAL-LCM :MINIMAL-LCM $MINIMAL_LCM MINIMAL-TOTAL-DEGREE :MINIMAL-TOTAL-DEGREE $MINIMAL_TOTAL_DEGREE MINIMAL-LENGTH :MINIMAL-LENGTH $MINIMAL_LENGTH).",
        [m],
      ),
    )
  }
}

// ---------------------------------------------------------------------------
// Operations in ideal theory

///|
/// Does the term depend on variable number K?
fn term_depends_p(term : Value, k : Value) -> Value raise {
  monom_depends_p(share_grobner__term_monom(term), k)
}

///|
/// Does the polynomial P depend on variable number K?
fn poly_depends_p(p : Value, k : Value) -> Value raise {
  for term in share_grobner__poly_termlist(p).iter() {
    let v = term_depends_p(term, k)
    if v.truthy() {
      return v
    }
  }
  Nil
}

///|
/// Intersection of the Grobner basis PLIST with R[x[k+1],...,x[n]]:
/// discard the polynomials depending on x[0], ..., x[k].
fn ring_intersection(plist : Value, k : Value) -> Value raise {
  let mut plist = plist
  for i in 0..<to_int(k) {
    plist = remove_if(p => poly_depends_p(p, int(i)).truthy(), plist)
  }
  plist
}

///|
/// `(or *elimination-order* default)`
fn share_grobner__elim_order_or(default : () -> Value raise) -> Value raise {
  let e = symval(q_ear_elimination_order)
  if e.truthy() {
    e
  } else {
    default()
  }
}

///|
fn elimination_ideal(
  ring : Value,
  flist : Value,
  k : Value,
  top_reduction_only? : Value,
  start? : Value = Fix(0L),
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  let order = share_grobner__elim_order_or(() => elimination_order(k))
  with_special(q_ear_monomial_order, order, () => ring_intersection(
    reduced_grobner(ring, flist, start~, top_reduction_only~),
    k,
  ))
}

///|
/// The reduced Grobner basis of the colon ideal Id(F):Id(G).
fn colon_ideal(
  ring : Value,
  f : Value,
  g : Value,
  top_reduction_only? : Value,
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  if g is Nil {
    // Id(G) consists of 0 only so W*0=0 belongs to Id(F)
    if every(share_grobner__zerop, f) {
      raise LispError::SimpleError("First ideal must be non-zero.")
    } else {
      let nz = find_if(p => !share_grobner__zerop(p), f)
      // The POLY defstruct has only BOA constructors, so this MAKE-POLY is
      // the CRE macro of ratmac.lisp (as in the Lisp).
      list1(
        make_poly(
          list1(
            share_grobner__make_term(
              make_monom(monom_dimension(poly_lm(nz)), initial_element=Fix(0L)),
              share_grobner__runit(ring),
            ),
          ),
        ),
      )
    }
  } else if cdr(g) is Nil {
    colon_ideal_1(ring, f, car(g), top_reduction_only~)
  } else {
    ideal_intersection(
      ring,
      colon_ideal_1(ring, f, car(g), top_reduction_only~),
      colon_ideal(ring, f, cdr(g), top_reduction_only~),
      top_reduction_only~,
    )
  }
}

///|
/// The reduced Grobner basis of the colon ideal Id(F):Id({G}).
fn colon_ideal_1(
  ring : Value,
  f : Value,
  g : Value,
  top_reduction_only? : Value,
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  mapcar(
    x => poly_exact_divide(ring, x, g),
    ideal_intersection(ring, f, list1(g), top_reduction_only~),
  )
}

///|
fn ideal_intersection(
  ring : Value,
  f : Value,
  g : Value,
  top_reduction_only? : Value,
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  let order = share_grobner__elim_order_or(() => share_grobner__elimination_order_1_fn)
  with_special(q_ear_monomial_order, order, () => mapcar(
    p => poly_contract(p),
    ring_intersection(
      reduced_grobner(
        ring,
        append(
          mapcar(
            p => poly_extend(
              p,
              m=make_monom(Fix(1L), initial_element=Fix(1L)),
            ),
            f,
          ),
          mapcar(
            p => poly_append(
              list([
                poly_extend(
                  poly_uminus(ring, p),
                  m=make_monom(Fix(1L), initial_element=Fix(1L)),
                ),
                poly_extend(p),
              ]),
            ),
            g,
          ),
        ),
        start=Fix(0L),
        top_reduction_only~,
      ),
      Fix(1L),
    ),
  ))
}

///|
/// LCM (least common multiple) of two polynomials F and G.
fn poly_lcm(ring : Value, f : Value, g : Value) -> Value raise {
  if share_grobner__zerop(f) {
    f
  } else if share_grobner__zerop(g) {
    g
  } else if cdr(share_grobner__poly_termlist(f)) is Nil &&
    cdr(share_grobner__poly_termlist(g)) is Nil {
    let m = monom_lcm(poly_lm(f), poly_lm(g))
    share_grobner__make_poly_from_termlist(
      list1(
        share_grobner__make_term(
          m,
          share_grobner__rlcm(ring, poly_lc(f), poly_lc(g)),
        ),
      ),
    )
  } else {
    let (f, f_cont) = poly_primitive_part(ring, f)
    let (g, g_cont) = poly_primitive_part(ring, g)
    scalar_times_poly(
      ring,
      share_grobner__rlcm(ring, f_cont, g_cont),
      poly_primitive_part(
        ring,
        car(ideal_intersection(ring, list1(f), list1(g), top_reduction_only=Nil)),
      ).0,
    )
  }
}

///|
/// Do two Grobner bases yield the same ideal?
fn grobner_equal(ring : Value, g1 : Value, g2 : Value) -> Value raise {
  if grobner_subsetp(ring, g1, g2).truthy() {
    grobner_subsetp(ring, g2, g1)
  } else {
    Nil
  }
}

///|
/// T if the ideal generated by G1 is contained in that of the Grobner
/// basis G2.
fn grobner_subsetp(ring : Value, g1 : Value, g2 : Value) -> Value raise {
  lbool(every(p => grobner_member(ring, p, g2).truthy(), g1))
}

///|
/// T if P belongs to the ideal generated by the Grobner basis G.
fn grobner_member(ring : Value, p : Value, g : Value) -> Value raise {
  poly_zerop(normal_form(ring, p, g, top_reduction_only=Nil).0)
}

///|
/// Calculate F : p^inf, the saturation of the ideal F in the polynomial P.
fn ideal_saturation_1(
  ring : Value,
  f : Value,
  p : Value,
  start : Value,
  top_reduction_only? : Value,
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  let order = share_grobner__elim_order_or(() => share_grobner__elimination_order_1_fn)
  with_special(q_ear_monomial_order, order, () => mapcar(
    q => poly_contract(q),
    ring_intersection(
      reduced_grobner(
        ring,
        saturation_extension_1(ring, f, p),
        start~,
        top_reduction_only~,
      ),
      Fix(1L),
    ),
  ))
}

///|
/// Calculate F : p1^inf : p2^inf : ... : ps^inf
fn ideal_polysaturation_1(
  ring : Value,
  f : Value,
  plist : Value,
  start : Value,
  top_reduction_only? : Value,
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  if plist is Nil {
    reduced_grobner(ring, f, start~, top_reduction_only~)
  } else {
    let g = ideal_saturation_1(ring, f, car(plist), start, top_reduction_only~)
    ideal_polysaturation_1(
      ring,
      g,
      cdr(plist),
      int(length(g)),
      top_reduction_only~,
    )
  }
}

///|
/// The saturation of the ideal generated by F in the ideal generated by G.
fn ideal_saturation(
  ring : Value,
  f : Value,
  g : Value,
  start : Value,
  top_reduction_only? : Value,
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  let k = int(length(g))
  let order = share_grobner__elim_order_or(() => elimination_order(k))
  with_special(q_ear_monomial_order, order, () => mapcar(
    q => poly_contract(q, k~),
    ring_intersection(
      reduced_grobner(
        ring,
        polysaturation_extension(ring, f, g),
        start~,
        top_reduction_only~,
      ),
      k,
    ),
  ))
}

///|
/// Successive IDEAL-SATURATION of F by the ideals of IDEAL-LIST.
fn ideal_polysaturation(
  ring : Value,
  f : Value,
  ideal_list : Value,
  start : Value,
  top_reduction_only? : Value,
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  if ideal_list is Nil {
    f
  } else {
    let h = ideal_saturation(
      ring,
      f,
      car(ideal_list),
      start,
      top_reduction_only~,
    )
    ideal_polysaturation(
      ring,
      h,
      cdr(ideal_list),
      int(length(h)),
      top_reduction_only~,
    )
  }
}

// ---------------------------------------------------------------------------
// Conversion from internal to infix form

///|
/// `(mapcar fn vars exponents)` stopping at the shorter list.
fn share_grobner__map_var_powers(
  vars : Value,
  m : Value,
  f : (Value, Value) -> Value,
) -> Value raise {
  let c = Collector::new()
  let mut v = vars
  let mut e = monom_exponents(m)
  while v is Cons(_) && e is Cons(_) {
    c.add(f(car(v), car(e)))
    v = cdr(v)
    e = cdr(e)
  }
  c.result()
}

///|
fn coerce_to_infix(poly_type : Value, object_ : Value, vars : Value) -> Value raise {
  if eq(poly_type, share_grobner__q_kw_termlist) {
    cons(
      q_op_plus,
      mapcar(term => coerce_to_infix(q_kw_term, term, vars), object_),
    )
  } else if eq(poly_type, q_kw_polynomial) {
    coerce_to_infix(
      share_grobner__q_kw_termlist,
      share_grobner__poly_termlist(object_),
      vars,
    )
  } else if eq(poly_type, share_grobner__q_kw_poly_list) {
    cons(
      q_op_lb,
      mapcar(p => coerce_to_infix(q_kw_polynomial, p, vars), object_),
    )
  } else if eq(poly_type, q_kw_term) {
    cons(
      q_op_star,
      cons(
        share_grobner__term_coeff(object_),
        share_grobner__map_var_powers(
          vars,
          share_grobner__term_monom(object_),
          (v, power) => list([q_expt, v, power]),
        ),
      ),
    )
  } else {
    object_
  }
}

// ---------------------------------------------------------------------------
// Maxima expression parsing

///|
fn equal_test_p(expr1 : Value, expr2 : Value) -> Value raise {
  alike1(expr1, expr2)
}

///|
/// Convert a maxima list to lisp list.
fn coerce_maxima_list(expr : Value) -> Value raise {
  if consp(car(expr)) && eql(caar(expr), q_mlist) {
    cdr(expr)
  } else {
    expr
  }
}

///|
fn free_of_vars(expr : Value, vars : Value) -> Value raise {
  d_freeof(append(vars, list1(expr)))
}

///|
/// This function removes rational numbers from coefficients of polynomials.
fn parse_poly(expr : Value, vars : Value) -> Value raise {
  parse_poly1(d_num(sratsimp(expr)), vars)
}

///|
fn share_grobner__position_alike(x : Value, l : Value) -> Int raise {
  let mut i = 0
  for y in l.iter() {
    if equal_test_p(x, y).truthy() {
      return i
    }
    i += 1
  }
  -1
}

///|
/// Convert a maxima polynomial expression EXPR in variables VARS to
/// internal form.
fn parse_poly1(expr : Value, vars : Value) -> Value raise {
  let vars = coerce_maxima_list(vars)
  let ring = symval(q_ear_maxima_ring)
  let parse = fn(a : Value) -> Value raise { parse_poly1(a, vars) }
  if eql(expr, Fix(0L)) {
    return share_grobner__make_poly_zero()
  }
  let pos = share_grobner__position_alike(expr, vars)
  if pos >= 0 {
    share_grobner__make_variable(ring, int(length(vars)), int(pos))
  } else if free_of_vars(expr, vars).truthy() {
    // This means that variable-free CRE and Poisson forms will be converted
    // to coefficients intact
    coerce_coeff(ring, expr, vars)
  } else {
    let op = caar(expr)
    if eq(op, q_mplus) {
      share_grobner__reduce(
        (x, y) => poly_add(symval(q_ear_maxima_ring), x, y),
        mapcar(parse, cdr(expr)),
      )
    } else if eq(op, q_mminus) {
      poly_uminus(ring, parse(cadr(expr)))
    } else if eq(op, q_mtimes) {
      if cddr(expr) is Nil { // unary
        parse(cdr(expr))
      } else {
        share_grobner__reduce(
          (p, q) => poly_mul(symval(q_ear_maxima_ring), p, q),
          mapcar(parse, cdr(expr)),
        )
      }
    } else if eq(op, q_mexpt) {
      let bpos = share_grobner__position_alike(cadr(expr), vars)
      if bpos >= 0 {
        // Special handling of (expt var pow)
        share_grobner__make_variable(
          ring,
          int(length(vars)),
          int(bpos),
          power=caddr(expr),
        )
      } else if !(integerp(caddr(expr)) && plusp(caddr(expr))) {
        // Negative power means division in coefficient ring
        // Non-integer power means non-polynomial coefficient
        mtell(
          list([
            Str(
              "~%Warning: Expression ~%~M~%contains power which is not a positive integer. Parsing as coefficient.~%",
            ),
            expr,
          ]),
        )
        |> ignore
        coerce_coeff(ring, expr, vars)
      } else {
        poly_expt(ring, parse(cadr(expr)), caddr(expr))
      }
    } else if eq(op, q_mrat) {
      parse(d_ratdisrep(expr))
    } else if eq(op, q_mpois) {
      parse(d_outofpois(expr))
    } else {
      coerce_coeff(ring, expr, vars)
    }
  }
}

///|
fn parse_poly_list(expr : Value, vars : Value) -> Value raise {
  if eq(caar(expr), q_mlist) {
    mapcar(p => parse_poly(p, vars), cdr(expr))
  } else {
    merror(
      Str("Expression ~M is not a list of polynomials in variables ~M."),
      list([expr, vars]),
    )
  }
}

///|
fn parse_poly_list_list(poly_list_list : Value, vars : Value) -> Value raise {
  mapcar(g => parse_poly_list(g, vars), coerce_maxima_list(poly_list_list))
}

// ---------------------------------------------------------------------------
// Order utilities

///|
/// The order function named ORDER.
fn find_order(order : Value) -> Value raise {
  if order is Nil {
    Nil
  } else if symbolp(order) {
    if eq(order, q_lex) ||
      eq(order, share_grobner__q_kw_lex) ||
      eq(order, q_d_lex) {
      share_grobner__lex_fn
    } else if eq(order, share_grobner__q_grlex) ||
      eq(order, share_grobner__q_kw_grlex) ||
      eq(order, q_d_grlex) {
      share_grobner__grlex_fn
    } else if eq(order, share_grobner__q_grevlex) ||
      eq(order, share_grobner__q_kw_grevlex) ||
      eq(order, q_d_grevlex) {
      share_grobner__grevlex_fn
    } else if eq(order, share_grobner__q_invlex) ||
      eq(order, share_grobner__q_kw_invlex) ||
      eq(order, q_d_invlex) {
      share_grobner__invlex_fn
    } else if eq(order, q_elimination_order_1) ||
      eq(order, share_grobner__q_kw_elimination_order_1) ||
      eq(order, share_grobner__q_elimination_order_1u) {
      share_grobner__elimination_order_1_fn
    } else {
      mtell(list([Str("~%Warning: Order ~M not found. Using default.~%"), order]))
    }
  } else {
    mtell(
      list([
        Str("~%Order specification ~M is not recognized. Using default.~%"),
        order,
      ]),
    )
    |> ignore
    Nil
  }
}

///|
/// The ring structure named RING.
fn find_ring(ring : Value) -> Value raise {
  if ring is Nil {
    Nil
  } else if symbolp(ring) {
    if eq(ring, share_grobner__q_expression_ring) ||
      eq(ring, share_grobner__q_kw_expression_ring) ||
      eq(ring, q_d_expression_ring) {
      symval(q_ear_expression_ring)
    } else if eq(ring, share_grobner__q_ring_of_integers) ||
      eq(ring, share_grobner__q_kw_ring_of_integers) ||
      eq(ring, q_d_ring_of_integers) {
      symval(q_ear_ring_of_integers)
    } else {
      mtell(list([Str("~%Warning: Ring ~M not found. Using default.~%"), ring]))
    }
  } else {
    mtell(
      list([
        Str("~%Ring specification ~M is not recognized. Using default.~%"),
        ring,
      ]),
    )
    |> ignore
    Nil
  }
}

///|
fn share_grobner__or(a : Value, b : Value) -> Value {
  if a.truthy() {
    a
  } else {
    b
  }
}

// ---------------------------------------------------------------------------
// Conversion from internal form to Maxima general form

///|
fn maxima_head() -> Value raise {
  if symval(q_d_poly_return_term_list).truthy() {
    share_grobner__head_mlist
  } else {
    share_grobner__head_mplus
  }
}

///|
fn coerce_to_maxima(
  poly_type : Value,
  object_ : Value,
  vars : Value,
) -> Value raise {
  if eq(poly_type, q_kw_polynomial) {
    cons(
      maxima_head(),
      mapcar(
        term => coerce_to_maxima(q_kw_term, term, vars),
        share_grobner__poly_termlist(object_),
      ),
    )
  } else if eq(poly_type, share_grobner__q_kw_poly_list) {
    cons(
      list1(q_mlist),
      mapcar(p => coerce_to_maxima(q_kw_polynomial, p, vars), object_),
    )
  } else if eq(poly_type, q_kw_term) {
    cons(
      list1(q_mtimes),
      cons(
        share_grobner__term_coeff(object_),
        share_grobner__map_var_powers(
          vars,
          share_grobner__term_monom(object_),
          (v, power) => list([list1(q_mexpt), v, power]),
        ),
      ),
    )
  } else {
    object_
  }
}

// ---------------------------------------------------------------------------
// Macro facility for Maxima-level wrappers

///|
/// macro `with-parsed-polynomials`: bind the coefficient ring, monomial
/// order and elimination orders from the Maxima option variables, run BODY
/// (which parses its arguments with the coerced VARS) and convert the result
/// back with VALUE-TYPE.
fn share_grobner__with_parsed(
  maxima_vars : Value,
  maxima_new_vars : Value?,
  value_type : Value,
  body : (Value) -> Value raise,
) -> Value raise {
  let vars = coerce_maxima_list(maxima_vars)
  let new_vars = match maxima_new_vars {
    Some(v) => Some(coerce_maxima_list(v))
    None => None
  }
  let ring = share_grobner__or(
    find_ring(symval(q_d_poly_coefficient_ring)),
    symval(q_ear_maxima_ring),
  )
  let result = with_special(q_ear_maxima_ring, ring, () => {
    let order = share_grobner__or(
      find_order(symval(q_d_poly_monomial_order)),
      symval(q_ear_monomial_order),
    )
    with_special(q_ear_monomial_order, order, () => {
      let primary = share_grobner__or(
        find_order(symval(q_d_poly_primary_elimination_order)),
        symval(q_ear_primary_elimination_order),
      )
      let secondary = share_grobner__or(
        find_order(symval(q_d_poly_secondary_elimination_order)),
        symval(q_ear_secondary_elimination_order),
      )
      let elim = share_grobner__or(
        find_order(symval(q_d_poly_elimination_order)),
        symval(q_ear_elimination_order),
      )
      with_specials(
        [
          (q_ear_primary_elimination_order, primary),
          (q_ear_secondary_elimination_order, secondary),
          (q_ear_elimination_order, elim),
        ],
        () => body(vars),
      )
    })
  })
  coerce_to_maxima(value_type, result, match new_vars {
    Some(nv) => append(vars, nv)
    None => vars
  })
}

///|
fn share_grobner__ring() -> Value raise {
  symval(q_ear_maxima_ring)
}

///|
/// macro `(define-unop maxima-name fun-name &optional documentation)`:
/// define the Lisp function MAXIMA-NAME (P VARS) applying FUN-NAME.
fn define_unop(
  maxima_name : Value,
  fun_name : Value,
  documentation? : Value,
) -> Value raise {
  ignore(documentation)
  defun(maxima_name, args => {
    let vars = coerce_maxima_list(arg(args, 1))
    let p = parse_poly(arg(args, 0), vars)
    coerce_to_maxima(
      q_kw_polynomial,
      funcall(fun_name, [share_grobner__ring(), p]),
      vars,
    )
  })
  maxima_name
}

///|
/// macro `(define-binop maxima-name fun-name &optional documentation)`:
/// define the Maxima function MAXIMA-NAME (P Q VARS) applying FUN-NAME.
fn define_binop(
  maxima_name : Value,
  fun_name : Value,
  documentation? : Value,
) -> Value raise {
  ignore(documentation)
  let name = symbol_name(maxima_name)
  defun(maxima_name, args => {
    check_arity_range(name, args, 3, 3)
    let vars = coerce_maxima_list(arg(args, 2))
    let p = parse_poly(arg(args, 0), vars)
    let q = parse_poly(arg(args, 1), vars)
    coerce_to_maxima(
      q_kw_polynomial,
      funcall(fun_name, [share_grobner__ring(), p, q]),
      vars,
    )
  })
  putprop(maxima_name, t, q_translated) |> ignore
  maxima_name
}

// ---------------------------------------------------------------------------
// Maxima-level interface functions

///|
/// Auxiliary function for removing zero polynomials. The Lisp is
/// `(remove #'poly-zerop plist)`, which removes the elements EQL to the
/// function object, i.e. none: the result is a copy of PLIST.
fn remzero(plist : Value) -> Value raise {
  copy_list(plist)
}

///|
/// Equivalent to EXPAND(P) if P parses correctly to a polynomial.
fn d_poly_expand(p : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, q_kw_polynomial, vars => parse_poly(
    p, vars,
  ))
}

///|
fn d_poly_expt(p : Value, n : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, q_kw_polynomial, vars => {
    let p = parse_poly(p, vars)
    poly_expt(share_grobner__ring(), p, n)
  })
}

///|
fn d_poly_content(p : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, Nil, vars => {
    let p = parse_poly(p, vars)
    poly_content(share_grobner__ring(), p)
  })
}

///|
fn d_poly_pseudo_divide(f : Value, fl : Value, vars : Value) -> Value raise {
  let vars = coerce_maxima_list(vars)
  let f = parse_poly(f, vars)
  let fl = parse_poly_list(fl, vars)
  let (quot, rem, c, division_count) = poly_pseudo_divide(
    share_grobner__ring(),
    f,
    fl,
  )
  list([
    list1(q_mlist),
    coerce_to_maxima(share_grobner__q_kw_poly_list, quot, vars),
    coerce_to_maxima(q_kw_polynomial, rem, vars),
    c,
    division_count,
  ])
}

///|
fn d_poly_exact_divide(f : Value, g : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, q_kw_polynomial, vars => {
    let g = parse_poly(g, vars)
    let f = parse_poly(f, vars)
    poly_exact_divide(share_grobner__ring(), f, g)
  })
}

///|
fn d_poly_normal_form(f : Value, fl : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, q_kw_polynomial, vars => {
    let fl = parse_poly_list(fl, vars)
    let f = parse_poly(f, vars)
    normal_form(share_grobner__ring(), f, remzero(fl), top_reduction_only=Nil).0
  })
}

///|
fn d_poly_buchberger_criterion(g : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, Nil, vars => {
    let g = parse_poly_list(g, vars)
    buchberger_criterion(share_grobner__ring(), g)
  })
}

///|
fn d_poly_buchberger(fl : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let fl = parse_poly_list(fl, vars)
    buchberger(share_grobner__ring(), remzero(fl), Fix(0L), top_reduction_only=Nil)
  })
}

///|
fn d_poly_reduction(plist : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let plist = parse_poly_list(plist, vars)
    reduction(share_grobner__ring(), plist)
  })
}

///|
fn d_poly_minimization(plist : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let plist = parse_poly_list(plist, vars)
    minimization(plist)
  })
}

///|
fn d_poly_normalize_list(plist : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let plist = parse_poly_list(plist, vars)
    poly_normalize_list(share_grobner__ring(), plist)
  })
}

///|
fn d_poly_grobner(f : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let f = parse_poly_list(f, vars)
    grobner(share_grobner__ring(), remzero(f))
  })
}

///|
fn d_poly_reduced_grobner(f : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let f = parse_poly_list(f, vars)
    reduced_grobner(share_grobner__ring(), remzero(f))
  })
}

///|
fn d_poly_depends_p(p : Value, var_ : Value, mvars : Value) -> Value raise {
  let vars = coerce_maxima_list(mvars)
  let pos = position(var_, vars)
  if pos < 0 {
    merror(
      Str("~%Variable ~M not in the list of variables ~M."),
      list([var_, mvars]),
    )
  } else {
    poly_depends_p(parse_poly(p, vars), int(pos))
  }
}

///|
fn d_poly_elimination_ideal(flist : Value, k : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let flist = parse_poly_list(flist, vars)
    elimination_ideal(
      share_grobner__ring(),
      flist,
      k,
      top_reduction_only=Nil,
      start=Fix(0L),
    )
  })
}

///|
fn d_poly_colon_ideal(f : Value, g : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let g = parse_poly_list(g, vars)
    let f = parse_poly_list(f, vars)
    colon_ideal(share_grobner__ring(), f, g, top_reduction_only=Nil)
  })
}

///|
fn d_poly_ideal_intersection(f : Value, g : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let g = parse_poly_list(g, vars)
    let f = parse_poly_list(f, vars)
    ideal_intersection(share_grobner__ring(), f, g, top_reduction_only=Nil)
  })
}

///|
fn d_poly_lcm(f : Value, g : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, q_kw_polynomial, vars => {
    let g = parse_poly(g, vars)
    let f = parse_poly(f, vars)
    poly_lcm(share_grobner__ring(), f, g)
  })
}

///|
fn d_poly_gcd(f : Value, g : Value, vars : Value) -> Value raise {
  d_first(d_divide(m_star(list([f, g])), d_poly_lcm(f, g, vars), Nil))
}

///|
fn d_poly_grobner_equal(g1 : Value, g2 : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, Nil, vars => {
    let g2 = parse_poly_list(g2, vars)
    let g1 = parse_poly_list(g1, vars)
    grobner_equal(share_grobner__ring(), g1, g2)
  })
}

///|
fn d_poly_grobner_subsetp(g1 : Value, g2 : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, Nil, vars => {
    let g2 = parse_poly_list(g2, vars)
    let g1 = parse_poly_list(g1, vars)
    grobner_subsetp(share_grobner__ring(), g1, g2)
  })
}

///|
fn d_poly_grobner_member(p : Value, g : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, Nil, vars => {
    let g = parse_poly_list(g, vars)
    let p = parse_poly(p, vars)
    grobner_member(share_grobner__ring(), p, g)
  })
}

///|
fn d_poly_ideal_saturation1(f : Value, p : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let f = parse_poly_list(f, vars)
    let p = parse_poly(p, vars)
    ideal_saturation_1(share_grobner__ring(), f, p, Fix(0L))
  })
}

///|
fn d_poly_saturation_extension(
  f : Value,
  plist : Value,
  vars : Value,
  new_vars : Value,
) -> Value raise {
  share_grobner__with_parsed(
    vars,
    Some(new_vars),
    share_grobner__q_kw_poly_list,
    vars => {
      let plist = parse_poly_list(plist, vars)
      let f = parse_poly_list(f, vars)
      saturation_extension(share_grobner__ring(), f, plist)
    },
  )
}

///|
fn d_poly_polysaturation_extension(
  f : Value,
  plist : Value,
  vars : Value,
  new_vars : Value,
) -> Value raise {
  share_grobner__with_parsed(
    vars,
    Some(new_vars),
    share_grobner__q_kw_poly_list,
    vars => {
      let plist = parse_poly_list(plist, vars)
      let f = parse_poly_list(f, vars)
      polysaturation_extension(share_grobner__ring(), f, plist)
    },
  )
}

///|
fn d_poly_ideal_polysaturation1(
  f : Value,
  plist : Value,
  vars : Value,
) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let plist = parse_poly_list(plist, vars)
    let f = parse_poly_list(f, vars)
    ideal_polysaturation_1(
      share_grobner__ring(),
      f,
      plist,
      Fix(0L),
      top_reduction_only=Nil,
    )
  })
}

///|
fn d_poly_ideal_saturation(f : Value, g : Value, vars : Value) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let g = parse_poly_list(g, vars)
    let f = parse_poly_list(f, vars)
    ideal_saturation(share_grobner__ring(), f, g, Fix(0L), top_reduction_only=Nil)
  })
}

///|
fn d_poly_ideal_polysaturation(
  f : Value,
  ideal_list : Value,
  vars : Value,
) -> Value raise {
  share_grobner__with_parsed(vars, None, share_grobner__q_kw_poly_list, vars => {
    let ideal_list = parse_poly_list_list(ideal_list, vars)
    let f = parse_poly_list(f, vars)
    ideal_polysaturation(
      share_grobner__ring(),
      f,
      ideal_list,
      Fix(0L),
      top_reduction_only=Nil,
    )
  })
}

// ---------------------------------------------------------------------------
// Top-level forms

///|
fn init_share_grobner() -> Unit raise {
  defvar_init(q_ear_monomial_order, share_grobner__lex_fn)
  defvar_init(q_ear_primary_elimination_order, share_grobner__lex_fn)
  defvar_init(q_ear_secondary_elimination_order, share_grobner__lex_fn)
  // defparameter
  set(q_ear_ring_of_integers, share_grobner__ring_of_integers()) |> ignore
  defvar_init(q_ear_pair_key_function, share_grobner__sugar_pair_key_fn)
  defvar_init(q_ear_pair_order, share_grobner__sugar_order_fn)
  // defparameter
  set(q_ear_expression_ring, share_grobner__expression_ring()) |> ignore
  defvar_init(q_ear_maxima_ring, symval(q_ear_expression_ring))
  // Simple operators
  define_binop(q_d_poly_add, q_poly_add) |> ignore
  define_binop(q_d_poly_subtract, q_poly_sub) |> ignore
  define_binop(q_d_poly_multiply, q_poly_mul) |> ignore
  define_binop(q_d_poly_s_polynomial, q_spoly) |> ignore
  define_unop(q_d_poly_primitive_part, q_poly_primitive_part) |> ignore
  define_unop(q_d_poly_normalize, q_poly_normalize) |> ignore
}
