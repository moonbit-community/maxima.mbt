// Port of share/logic/logic.lisp: logic algebra package (Alexey
// Beshenov, 2008--2009).

///|
let share_logic__q_and_op : Value = sym("*and-op*")

///|
let share_logic__q_or_op : Value = sym("*or-op*")

///|
fn init_share_logic() -> Unit raise {
  if symval(q_use_maxima_logic_operators).truthy() {
    defvar_init(q_ear_not_op, q_mnot)
    d_texput(Str("not"), Str(" \\neg "), tx=q_d_prefix) |> ignore
    defvar_init(share_logic__q_and_op, q_mand)
    d_texput(Str("and"), Str(" \\wedge "), tx=q_d_nary) |> ignore
    defvar_init(share_logic__q_or_op, q_mor)
    d_texput(Str("or"), Str(" \\vee "), tx=q_d_nary) |> ignore
  } else {
    d_prefix(Str("log-not"), rbp=Fix(70L)) |> ignore
    defvar_init(q_ear_not_op, sym("$log-not"))
    d_texput(Str("log-not"), Str(" \\neg "), tx=q_d_prefix) |> ignore
    d_nary(Str("log-and"), bp=Fix(65L)) |> ignore
    defvar_init(share_logic__q_and_op, sym("$log-and"))
    d_texput(Str("log-and"), Str(" \\wedge "), tx=q_d_nary) |> ignore
    d_nary(Str("log-or"), bp=Fix(60L)) |> ignore
    defvar_init(share_logic__q_or_op, sym("$log-or"))
    d_texput(Str("log-or"), Str(" \\vee "), tx=q_d_nary) |> ignore
  }
  d_nary(Str("nand"), bp=Fix(62L)) |> ignore
  d_texput(Str("nand"), Str(" \\mid "), tx=q_d_nary) |> ignore
  d_nary(Str("nor"), bp=Fix(61L)) |> ignore
  d_texput(Str("nor"), Str(" \\downarrow "), tx=q_d_nary) |> ignore
  d_infix(Str("implies"), lbp=Fix(59L)) |> ignore
  d_texput(Str("implies"), Str(" \\rightarrow "), tx=q_d_infix) |> ignore
  d_nary(Str("eq"), bp=Fix(58L)) |> ignore
  d_texput(Str("eq"), Str(" \\sim "), tx=q_d_nary) |> ignore
  d_nary(Str("xor"), bp=Fix(58L)) |> ignore
  d_texput(Str("xor"), Str(" \\oplus "), tx=q_d_nary) |> ignore
}

///|
fn share_logic__op(s : Value) -> Value raise {
  symval(s)
}

///|
fn get_maxima_operator(expr : Value) -> Value raise {
  if listp(expr) && expr.truthy() && listp(car(expr)) && car(expr).truthy() {
    caar(expr)
  } else {
    Nil
  }
}

///|
fn contains_operator(expr : Value, op : Value) -> Value raise {
  let o = get_maxima_operator(expr)
  let args = if o.truthy() { cdr(expr) } else { Nil }
  if eq(o, op) {
    t
  } else {
    member(t, mapcar(e => contains_operator(e, op), args))
  }
}

///|
fn replicate(n : Value, e : Value) -> Value raise {
  if integerp(n) && num_ge(n, Fix(0L)) {
    if num_eq(n, Fix(0L)) {
      Nil
    } else {
      cons(e, replicate(num_sub(n, Fix(1L)), e))
    }
  } else {
    raise LispError::SimpleError("Invalid arguments to 'replicate'")
  }
}

///|
fn zip(l1 : Value, l2 : Value) -> Value raise {
  if !listp(l1) || !listp(l2) || length(l1) != length(l2) {
    raise LispError::SimpleError("Invalid arguments to 'zip'")
  }
  if l1 is Nil {
    l1
  } else {
    cons(cons(car(l1), car(l2)), zip(cdr(l1), cdr(l2)))
  }
}

///|
fn remove_h_nth(n : Value, l : Value) -> Value raise {
  if !integerp(n) || num_lt(n, Fix(0L)) {
    raise LispError::SimpleError("Invalid argumet to 'remove-nth'")
  } else if num_eq(n, Fix(0L)) {
    cdr(l)
  } else {
    cons(car(l), remove_h_nth(num_sub(n, Fix(1L)), cdr(l)))
  }
}

///|
fn multiset_to_hash(l : Value) -> Value raise {
  mapcar(
    e => {
      let mut c = 0L
      for x in l.iter() {
        if equal(e, x) {
          c += 1L
        }
      }
      list([e, Fix(c)])
    },
    remove_duplicates(l, pred2=(a, b) => equal(a, b)),
  )
}

///|
fn hash_to_multiset(h : Value) -> Value raise {
  mapcan(he => replicate(cadr(he), car(he)), h)
}

///|
fn cancel_pairs_in_hash(h : Value) -> Value raise {
  mapcar(he => list([car(he), num_mod(cadr(he), Fix(2L))]), h)
}

///|
fn cancel_pairs(l : Value) -> Value raise {
  hash_to_multiset(cancel_pairs_in_hash(multiset_to_hash(l)))
}

///|
fn subst_recursive(expr : Value, pairs : Value) -> Value raise {
  if pairs.truthy() {
    let p = car(pairs)
    subst(cdr(p), car(p), subst_recursive(expr, cdr(pairs)))
  } else {
    expr
  }
}

///|
fn disjoin_list(pred : Value, lst : Value) -> Value raise {
  if lst is Nil {
    list([Nil, Nil])
  } else {
    let dl = disjoin_list(pred, cdr(lst))
    if funcall(pred, [car(lst)]).truthy() {
      list([cons(car(lst), car(dl)), cadr(dl)])
    } else {
      list([car(dl), cons(car(lst), cadr(dl))])
    }
  }
}

///|
/// t or nil
fn booleanp(x : Value) -> Value raise {
  lbool(eq(x, t) || x is Nil)
}

///|
fn logic_sort_comparator(x : Value, y : Value) -> Value raise {
  let bx = booleanp(x).truthy()
  let by = booleanp(y).truthy()
  if !bx && by {
    t
  } else if bx && !by {
    Nil
  } else if !listp(x) && listp(y) {
    Nil
  } else if listp(x) && !listp(y) {
    t
  } else if listp(x) && listp(y) && length(x) < length(y) {
    Nil
  } else if listp(x) && listp(y) && length(x) > length(y) {
    t
  } else {
    d_orderlessp(x, y)
  }
}

///|
fn sort_symbols(seq : Value) -> Value raise {
  sort_list(seq, (a, b) => logic_sort_comparator(a, b).truthy())
}

///|
/// op (x_1, ..., f(y_1, ..., y_m), ..., x_n) =>
///                                       op (x_1, ..., y_1, ..., y_m, ..., x_n)
fn flatten_nested(args : Value, op : Value) -> Value raise {
  let mut nested_exprs : Value = Nil
  let mut other : Value = Nil
  let mut args = args
  while args.truthy() {
    if eq(get_maxima_operator(car(args)), op) {
      nested_exprs = cons(car(args), nested_exprs)
    } else {
      other = cons(car(args), other)
    }
    args = cdr(args)
  }
  nested_exprs = mapcar(e => flatten_nested(cdr(e), op), nested_exprs)
  if nested_exprs.truthy() {
    let mut acc : Value = Nil
    for l in nested_exprs.iter() {
      acc = append(acc, l)
    }
    append(other, acc)
  } else {
    other
  }
}

///|
/// Implication
fn simp_implies(x : Value, y : Value) -> Value raise {
  if x is Nil {
    t
  } else if eq(x, t) && eq(y, t) {
    t
  } else if eq(x, t) && y is Nil {
    Nil
  } else {
    list([list([share_logic__op(q_ear_implies_op), q_simp]), x, y])
  }
}

///|
/// Webb-operation or Peirce arrow (Quine's dagger, NOR)
fn simp_nor(args : Value) -> Value raise {
  if member(t, args).truthy() {
    return Nil
  }
  let args = remove_duplicates(remove(Nil, args), pred2=(a, b) => equal(a, b))
  if args is Nil {
    t
  } else if length(args) == 1 {
    simp_not(car(args))
  } else {
    cons(list([share_logic__op(q_ear_nor_op), q_simp]), sort_symbols(args))
  }
}

///|
/// Sheffer stroke (alternative denial, NAND)
fn simp_nand(args : Value) -> Value raise {
  if member(Nil, args).truthy() {
    return t
  }
  let args = remove_duplicates(remove(t, args), pred2=(a, b) => equal(a, b))
  if args is Nil {
    Nil
  } else if length(args) == 1 {
    simp_not(car(args))
  } else {
    cons(list([share_logic__op(q_ear_nand_op), q_simp]), sort_symbols(args))
  }
}

///|
/// Equivalence
fn simp_eq(args : Value) -> Value raise {
  let args = cancel_pairs(
    remove(t, flatten_nested(args, share_logic__op(q_ear_eq_op))),
  )
  if args is Nil {
    t
  } else if length(args) == 1 {
    car(args)
  } else {
    cons(list([share_logic__op(q_ear_eq_op), q_simp]), sort_symbols(args))
  }
}

///|
/// Sum modulo 2 (exclusive or)
fn simp_xor(args : Value) -> Value raise {
  let args = cancel_pairs(
    remove(Nil, flatten_nested(args, share_logic__op(q_ear_xor_op))),
  )
  if args is Nil {
    Nil
  } else if length(args) == 1 {
    car(args)
  } else {
    cons(list([share_logic__op(q_ear_xor_op), q_simp]), sort_symbols(args))
  }
}

///|
/// returns t if args = (... x ... not x ...)
/// used in simp-and and simp-or
fn x_not_x(args : Value) -> Value raise {
  let not_op = share_logic__op(q_ear_not_op)
  let neg = disjoin_list(
    lfunc("x-not-x", a => lbool(eq(get_maxima_operator(a[0]), not_op))),
    args,
  )
  lbool(
    intersection(mapcar(x => cadr(x), car(neg)), cadr(neg), pred2=(a, b) => equal(
      a, b,
    )).truthy(),
  )
}

///|
/// Logical AND (conjunction)
fn simp_and(args : Value) -> Value raise {
  let args = flatten_nested(args, share_logic__op(share_logic__q_and_op))
  if member(Nil, args).truthy() {
    return Nil
  }
  let args = remove_duplicates(remove(t, args), pred2=(a, b) => equal(a, b))
  if args is Nil {
    t
  } else if length(args) == 1 {
    car(args)
  } else if x_not_x(args).truthy() {
    Nil
  } else {
    cons(list([share_logic__op(share_logic__q_and_op), q_simp]), sort_symbols(args))
  }
}

///|
/// Logical OR (disjunction)
fn simp_or(args : Value) -> Value raise {
  let args = flatten_nested(args, share_logic__op(share_logic__q_or_op))
  if member(t, args).truthy() {
    return t
  }
  let args = remove_duplicates(remove(Nil, args), pred2=(a, b) => equal(a, b))
  if args is Nil {
    Nil
  } else if length(args) == 1 {
    car(args)
  } else if x_not_x(args).truthy() {
    t
  } else {
    cons(list([share_logic__op(share_logic__q_or_op), q_simp]), sort_symbols(args))
  }
}

///|
/// Logical NOT (negation)
fn simp_not(x : Value) -> Value raise {
  let not_op = share_logic__op(q_ear_not_op)
  if eq(get_maxima_operator(x), not_op) {
    cadr(x)
  } else if x is Nil {
    t
  } else if eq(x, t) {
    Nil
  } else {
    list([list([not_op, q_simp]), x])
  }
}

///|
/// (apply 'simp-not args) / (apply 'simp-implies args) with the arity
/// check of APPLY.
fn share_logic__apply_fixed(name : Value, args : Value) -> Value raise {
  apply(name, args)
}

///|
fn apply_op(op : Value, args : Value) -> Value raise {
  if eq(op, share_logic__op(share_logic__q_and_op)) {
    simp_and(args)
  } else if eq(op, share_logic__op(q_ear_xor_op)) {
    simp_xor(args)
  } else if eq(op, share_logic__op(q_ear_not_op)) {
    share_logic__apply_fixed(q_simp_not, args)
  } else if eq(op, share_logic__op(share_logic__q_or_op)) {
    simp_or(args)
  } else if eq(op, share_logic__op(q_ear_nor_op)) {
    simp_nor(args)
  } else if eq(op, share_logic__op(q_ear_nand_op)) {
    simp_nand(args)
  } else if eq(op, share_logic__op(q_ear_eq_op)) {
    simp_eq(args)
  } else if eq(op, share_logic__op(q_ear_implies_op)) {
    share_logic__apply_fixed(q_simp_implies, args)
  } else {
    cons(list1(op), args)
  }
}

///|
fn logic_simp(expr : Value) -> Value raise {
  let op = get_maxima_operator(expr)
  let args = if op.truthy() { mapcar(e => logic_simp(e), cdr(expr)) } else { Nil }
  if op.truthy() {
    apply_op(op, args)
  } else {
    expr
  }
}

///|
fn d_logic_simp(expr : Value) -> Value raise {
  logic_simp(expr)
}

///|
/// (all-charfuns 2) => ((nil nil) (nil t) (t nil) (t t))
fn all_charfuns(n : Value) -> Value raise {
  if !(integerp(n) && num_ge(n, Fix(1L))) {
    raise LispError::SimpleError("Invalid argument to 'all-charfuns'")
  }
  if num_eq(n, Fix(1L)) {
    list([list1(Nil), list1(t)])
  } else {
    let pre = all_charfuns(num_sub(n, Fix(1L)))
    append(mapcar(l => cons(Nil, l), pre), mapcar(l => cons(t, l), pre))
  }
}

///|
/// List of values for all-charfuns, 2^n elements
fn characteristic_vector(expr : Value, args : Value) -> Value raise {
  let args = if args is Nil { list_of_variables(expr) } else { args }
  if args is Nil {
    list1(expr)
  } else {
    let n = length(args)
    let vals = mapcar(l => zip(args, l), all_charfuns(int(n)))
    mapcar(v => logic_simp(subst_recursive(expr, v)), vals)
  }
}

///|
fn list_of_variables(expr : Value) -> Value raise {
  sort_symbols(cdr(d_listofvars(expr)))
}

///|
fn d_characteristic_vector(expr : Value, args : Value) -> Value raise {
  cons(list([q_mlist, q_simp]), characteristic_vector(expr, args))
}

///|
/// Conversion to the Zhegalkin basis {and, xor}
fn zhegalkin_basis_substitute(expr : Value) -> Value raise {
  let op = get_maxima_operator(expr)
  let mut args = if op.truthy() {
    mapcar(e => zhegalkin_basis_substitute(e), cdr(expr))
  } else {
    Nil
  }
  if eq(op, share_logic__op(q_ear_not_op)) {
    // not x => x xor t
    simp_xor(list([car(args), t]))
  } else if eq(op, share_logic__op(q_ear_implies_op)) {
    // x implies y => (x and y) xor x xor t
    simp_xor(list([simp_and(args), car(args), t]))
  } else if eq(op, share_logic__op(q_ear_nand_op)) {
    // x1 nand x2 nand x3 ... nand xn => (x1 and x2 and x3 ... and xn) xor t
    simp_xor(list([simp_and(args), t]))
  } else if eq(op, share_logic__op(q_ear_nor_op)) {
    // x nor y => (x or y) xor t
    simp_xor(
      list([
        zhegalkin_basis_substitute(simp_or(list([car(args), cadr(args)]))),
        t,
      ]),
    )
  } else if eq(op, share_logic__op(share_logic__q_or_op)) {
    // x or y => (x and y) xor x xor y
    let mut zhegform = simp_xor(
      list([simp_and(list([car(args), cadr(args)])), car(args), cadr(args)]),
    )
    args = cddr(args)
    while args.truthy() {
      zhegform = simp_xor(
        list([simp_and(list([zhegform, car(args)])), zhegform, car(args)]),
      )
      args = cdr(args)
    }
    zhegform
  } else if eq(op, share_logic__op(q_ear_eq_op)) {
    // a eq b => a xor b xor t
    // a eq b eq c => a xor b xor c
    simp_xor(if length(args) % 2 == 0 { cons(t, args) } else { args })
  } else if op.truthy() {
    apply_op(op, args)
  } else {
    expr
  }
}

///|
/// acts like Maxima "expand" on ordinary polynomial ring,
/// but on Zhegalkin polynomials
fn zhegalkin_basis_expand(expr : Value) -> Value raise {
  let op = get_maxima_operator(expr)
  let args = if op.truthy() {
    mapcar(e => zhegalkin_basis_expand(e), cdr(expr))
  } else {
    Nil
  }
  let xor_op = share_logic__op(q_ear_xor_op)
  if eq(op, share_logic__op(share_logic__q_and_op)) {
    let xor_expression = find_if(
      e => eq(get_maxima_operator(e), xor_op),
      cdr(expr),
    )
    if xor_expression.truthy() {
      let xor_args = cdr(xor_expression)
      let and_args = remove_if(e => equal(xor_expression, e), cdr(expr))
      zhegalkin_basis_expand(
        simp_xor(mapcar(e => simp_and(cons(e, and_args)), xor_args)),
      )
    } else {
      expr
    }
  } else if eq(op, xor_op) {
    simp_xor(args)
  } else {
    expr
  }
}

///|
fn d_zhegalkin_form(expr : Value) -> Value raise {
  zhegalkin_basis_expand(zhegalkin_basis_substitute(expr))
}

///|
fn d_logic_equiv(expr1 : Value, expr2 : Value) -> Value raise {
  lbool(equal(d_zhegalkin_form(expr1), d_zhegalkin_form(expr2)))
}

///|
fn subst_not(expr : Value) -> Value raise {
  let op = get_maxima_operator(expr)
  if op.truthy() {
    cons(list1(op), mapcar(e => subst_not(e), cdr(expr)))
  } else {
    simp_not(expr)
  }
}

///|
/// f^* (x_1, ..., x_n) = not f (not x_1, ..., not x_n)
fn d_dual_function(expr : Value) -> Value raise {
  logic_simp(simp_not(subst_not(expr)))
}

///|
/// f = f^*
fn d_self_dual(expr : Value) -> Value raise {
  d_logic_equiv(expr, d_dual_function(expr))
}

///|
fn closed_under(expr : Value, x : Value) -> Value raise {
  let args = list_of_variables(expr)
  let n = length(args)
  let val = zip(args, replicate(int(n), x))
  lbool(eq(logic_simp(subst_recursive(expr, val)), x))
}

///|
/// f (nil, ..., nil) = nil
fn d_closed_under_f(expr : Value) -> Value raise {
  closed_under(expr, Nil)
}

///|
/// f (t, ..., t) = t
fn d_closed_under_t(expr : Value) -> Value raise {
  closed_under(expr, t)
}

///|
fn d_monotonic(expr : Value, args : Value) -> Value raise {
  let mut charvec = characteristic_vector(expr, args)
  if charvec.truthy() {
    let mut prev_value = car(charvec)
    charvec = cdr(charvec)
    while charvec.truthy() {
      if car(charvec) is Nil && eq(prev_value, t) {
        return Nil
      }
      prev_value = car(charvec)
      charvec = cdr(charvec)
    }
    t
  } else {
    t
  }
}

///|
fn d_linear(expr : Value) -> Value raise {
  lbool(
    !contains_operator(d_zhegalkin_form(expr), share_logic__op(share_logic__q_and_op)).truthy(),
  )
}

///|
/// Post's theorem
fn post_table(expressions : Value) -> Value raise {
  let fns : Array[(Value) -> Value raise] = [
    d_self_dual,
    d_closed_under_f,
    d_closed_under_t,
    d_linear,
    e => d_monotonic(e, Nil),
  ]
  list(fns.map(f => mapcar(e => f(e), expressions)))
}

///|
fn functionally_complete(table : Value) -> Value raise {
  if table is Nil {
    return Nil
  }
  let mut table = table
  while table.truthy() {
    if !member(Nil, car(table)).truthy() {
      return Nil
    }
    table = cdr(table)
  }
  t
}

///|
fn d_functionally_complete(expressions : Value) -> Value raise {
  functionally_complete(post_table(expressions))
}

///|
/// Basis is a complete system without redundant functions
fn d_logic_basis(expressions : Value) -> Value raise {
  let table = post_table(expressions)
  let n = length(expressions)
  if functionally_complete(table).truthy() {
    if n == 1 {
      return t
    }
  } else {
    return Nil
  }
  for i in 0..<n {
    if functionally_complete(mapcar(e => remove_h_nth(int(i), e), table)).truthy() {
      return Nil
    }
  }
  t
}

///|
/// Logic differentiation of a Zhegalkin form:
///   dy/dx = false (y independent of x), dx/dx = true,
///   d/dx1 [x1 and ... and xn] = x2 and ... and xn,
///   d/dx [g xor f] = dg/dx xor df/dx.
fn diff_zhegalkin_form(expr : Value, x : Value) -> Value raise {
  let op = get_maxima_operator(expr)
  if op is Nil {
    lbool(eq(expr, x))
  } else if eq(op, share_logic__op(q_ear_xor_op)) {
    simp_xor(mapcar(e => diff_zhegalkin_form(e, x), cdr(expr)))
  } else if eq(op, share_logic__op(share_logic__q_and_op)) {
    let args = cdr(expr)
    if member(x, args).truthy() {
      simp_and(remove(x, args))
    } else {
      Nil
    }
  } else {
    raise LispError::SimpleError(
      format_to_string("Not a Zhegalkin form in diff-zhegalkin-form: '~s'", [
        expr,
      ]),
    )
  }
}

///|
fn d_logic_diff(expr : Value, x : Value) -> Value raise {
  diff_zhegalkin_form(d_zhegalkin_form(expr), x)
}

///|
/// Coversion to the Boolean basis {and, or, not}
fn boolean_basis_substitute(expr : Value) -> Value raise {
  let op = get_maxima_operator(expr)
  let mut args = if op.truthy() {
    mapcar(e => boolean_basis_substitute(e), cdr(expr))
  } else {
    Nil
  }
  if eq(op, share_logic__op(q_ear_implies_op)) {
    // x implies y => (not x) or y
    simp_or(list([simp_not(car(args)), cadr(args)]))
  } else if eq(op, share_logic__op(q_ear_nand_op)) {
    // x1 nand ... nand xn => not (x1 and ... and xn)
    simp_not(simp_and(args))
  } else if eq(op, share_logic__op(q_ear_nor_op)) {
    // x1 nor ... not xn => not (x1 or ... or xn)
    simp_not(simp_or(args))
  } else if eq(op, share_logic__op(q_ear_eq_op)) {
    // x eq b => ((not x) or y) and ((not y) or x)
    let mut boolform = simp_and(
      list([
        simp_or(list([simp_not(car(args)), cadr(args)])),
        simp_or(list([simp_not(cadr(args)), car(args)])),
      ]),
    )
    args = cddr(args)
    while args.truthy() {
      boolform = simp_and(
        list([
          simp_or(list([simp_not(boolform), car(args)])),
          simp_or(list([simp_not(car(args)), boolform])),
        ]),
      )
      args = cdr(args)
    }
    boolform
  } else if eq(op, share_logic__op(q_ear_xor_op)) {
    // x xor y => ((not x) and y) or ((not y) and x)
    let mut boolform = simp_or(
      list([
        simp_and(list([simp_not(car(args)), cadr(args)])),
        simp_and(list([simp_not(cadr(args)), car(args)])),
      ]),
    )
    args = cddr(args)
    while args.truthy() {
      boolform = simp_or(
        list([
          simp_and(list([simp_not(boolform), car(args)])),
          simp_and(list([simp_not(car(args)), boolform])),
        ]),
      )
      args = cdr(args)
    }
    boolform
  } else if op.truthy() {
    apply_op(op, args)
  } else {
    expr
  }
}

///|
fn d_boolean_form(expr : Value) -> Value raise {
  boolean_basis_substitute(expr)
}

///|
/// De Morgan's rules
fn d_demorgan(expr : Value) -> Value raise {
  let op = get_maxima_operator(expr)
  let args = if op.truthy() { mapcar(e => d_demorgan(e), cdr(expr)) } else { Nil }
  if eq(op, share_logic__op(q_ear_not_op)) {
    let op_op = get_maxima_operator(car(args))
    if eq(op_op, share_logic__op(share_logic__q_and_op)) {
      simp_or(mapcar(e => simp_not(e), cdar(args)))
    } else if eq(op_op, share_logic__op(share_logic__q_or_op)) {
      simp_and(mapcar(e => simp_not(e), cdar(args)))
    } else {
      share_logic__apply_fixed(q_simp_not, args)
    }
  } else if op is Nil {
    expr
  } else {
    apply_op(op, args)
  }
}

///|
/// Perfect disjunctive normal forms
fn elementary_conjunct_disjunct(vars_vals : Value, b : Value) -> Value raise {
  if vars_vals is Nil {
    Nil
  } else {
    cons(
      if eq(cdar(vars_vals), b) {
        caar(vars_vals)
      } else {
        list([list([share_logic__op(q_ear_not_op), q_simp]), caar(vars_vals)])
      },
      elementary_conjunct_disjunct(cdr(vars_vals), b),
    )
  }
}

///|
fn pdnf_pcnf(expr : Value, b : Value) -> Value raise {
  let args = list_of_variables(expr)
  if args is Nil {
    expr
  } else {
    let n = length(args)
    let mut result : Value = Nil
    let mut vals = mapcar(l => zip(args, l), all_charfuns(int(n)))
    while vals.truthy() {
      if eq(logic_simp(subst_recursive(expr, car(vals))), b) {
        let ecd = elementary_conjunct_disjunct(car(vals), b)
        result = cons(if b.truthy() { simp_and(ecd) } else { simp_or(ecd) }, result)
      }
      vals = cdr(vals)
    }
    if b.truthy() {
      simp_or(result)
    } else {
      simp_and(result)
    }
  }
}

///|
/// Perfect disjunctive normal form
fn d_pdnf(expr : Value) -> Value raise {
  pdnf_pcnf(expr, t)
}

///|
/// Perfect conjunctive normal form
fn d_pcnf(expr : Value) -> Value raise {
  pdnf_pcnf(expr, Nil)
}
