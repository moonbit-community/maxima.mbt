// Port of share/contrib/format/miller-format.lisp (Bruce R. Miller, NIST):
// FORMAT, a package for restructuring expressions in Macsyma.
//
// The file's own MRELATIONP is identical to the one of compar.lisp, which
// is used instead.

///|
/// format(expr,template,...)
/// Formats EXPR according to the TEMPLATEs given:
fn d_format(expr : Value, templates : Value) -> Value raise {
  format_from_chain(expr, ear_templates=templates)
}

///|
/// format according to chain in *templates*
fn format_from_chain(expr : Value, ear_templates? : Value) -> Value raise {
  let v = match ear_templates {
    Some(v) => v
    None => symval(q_ear_templates)
  }
  let b = bind(q_ear_templates, v)
  defer unbind(b)
  let tl = symval(q_ear_templates)
  if tl is Nil {
    expr
  } else {
    set(q_ear_templates, cdr(tl)) |> ignore
    format_one(expr, car(tl))
  }
}

///|
/// format according to tmp, then pieces according to *templates*
fn format_one(expr : Value, tmp : Value) -> Value raise {
  let (template, formatter, parms, subtemplates) = share_miller_format__parse_template_mv(
    tmp,
  )
  let b = bind(q_ear_template, template)
  defer unbind(b)
  let b2 = bind(q_ear_subtemplates, subtemplates)
  defer unbind(b2)
  if formatter.truthy() {
    mfuncall(formatter, cons(expr, parms))
  } else if symbolp(tmp) ||
    (
      listp(tmp) &&
      (eq(caar(tmp), q_lambda) || memq(q_array, cdar(tmp)).truthy())
    ) {
    // Apply SPEC as function, if it CAN be
    let r = with_special(q_ear_templates, Nil, () => mfuncall(tmp, list1(expr)))
    format_from_chain(r)
  } else {
    merr("FORMAT: template ~M must be a template or function.", [tmp])
  }
}

///|
/// If %ditto form, return repeated template
fn share_miller_format__dittop(ptrn : Value) -> Value {
  if listp(ptrn) && eq(caar(ptrn), q_d__pctditto) {
    cadr(ptrn)
  } else {
    Nil
  }
}

///|
/// Format a `piece' of an expression, accounting for any current
/// subtemplates. If NTH is given, use NTH subtemplate for this piece, else
/// use next subtemplate. Account for %DITTO'd templates.
fn d_format_piece(piece : Value, nth_? : Value = Nil) -> Value raise {
  let subs = symval(q_ear_subtemplates)
  let subtmp : Value = if subs is Nil {
    // no piecewise templates.
    Nil
  } else if nth_ is Nil {
    // next one %ditto's
    let d = share_miller_format__dittop(car(subs))
    if d.truthy() {
      d
    } else {
      // otherwise, remove next one.
      set(q_ear_subtemplates, cdr(subs)) |> ignore
      car(subs)
    }
  } else {
    let n = nth(to_int(num_sub(nth_, Fix(1L))), subs)
    if n.truthy() {
      // nth subtemplate? strip off possible %ditto
      let d = share_miller_format__dittop(n)
      if d.truthy() {
        d
      } else {
        n
      }
    } else {
      // last dittos, reuse it
      share_miller_format__dittop(car(last(subs)))
    }
  }
  if subtmp.truthy() {
    format_one(piece, subtmp)
  } else {
    format_from_chain(piece)
  }
}

///|
/// Format expr according to remaining chain, but disallowing subtemplates.
fn format_w_slo_subtemplates(expr : Value) -> Value raise {
  if symval(q_ear_subtemplates).truthy() {
    merr("FORMAT: Template ~M was given subtemplates ~M", [
      symval(q_ear_template),
      mlist_star(symval(q_ear_subtemplates), Nil),
    ])
    |> ignore
  }
  format_from_chain(expr)
}

///|
/// given a candidate format template, return:
/// template name, formatter function, parameters (if any) and subtemplates
/// (if any),
fn share_miller_format__parse_template_mv(
  template : Value,
) -> (Value, Value, Value, Value) raise {
  let mut name : Value = Nil
  let mut formatter : Value = Nil
  let getform = fn(symbol : Value) raise {
    formatter = {
      let f = d_get(symbol, q_d_formatter)
      if f.truthy() {
        f
      } else {
        get(symbol, q_share_formatter)
      }
    }
    if formatter.truthy() {
      name = symbol
      name
    } else {
      Nil
    }
  }
  if d_numberp(template).truthy() {
    (Nil, Nil, Nil, Nil)
  } else if atom(template) {
    let g = getform(template)
    (g, formatter, Nil, Nil)
  } else if eq(caar(template), q_mqapply) {
    // Template w/ subtemplates AND parms
    let op = cadr(template)
    if listp(op) &&
      getform(caar(op)).truthy() &&
      !memq(q_array, cdar(op)).truthy() {
      // but not T[...][...]
      (name, formatter, cdr(op), cddr(template))
    } else {
      (Nil, Nil, Nil, Nil)
    }
  } else if getform(caar(template)).truthy() {
    // Template w/ parameters OR subtemplates
    if memq(q_array, cdar(template)).truthy() {
      (name, formatter, Nil, cdr(template))
    } else {
      (name, formatter, cdr(template), Nil)
    }
  } else {
    (Nil, Nil, Nil, Nil)
  }
}

///|
fn parse_template(template : Value) -> Value raise {
  share_miller_format__parse_template_mv(template).0
}

///|
/// Defining format commands: (def-formatter names parms . body) puts the
/// formatter function on the SHARE-FORMATTER property of each name. The
/// function of a formatter with a lambda list is an uninterned symbol named
/// after the first name.
fn share_miller_format__def_formatter(
  names : Array[Value],
  body : (Array[Value]) -> Value raise,
) -> Unit raise {
  let fmtr = make_symbol(symbol_name(names[0]) + "-share-formatter")
  defun(fmtr, body)
  share_miller_format__def_formatter_fn(names, fmtr)
}

///|
/// (def-formatter names fn): FN is an existing function name.
fn share_miller_format__def_formatter_fn(
  names : Array[Value],
  fmtr : Value,
) -> Unit {
  for name in names {
    setf_get(name, q_share_formatter, fmtr) |> ignore
  }
}

///|
/// Arithmetic template: eg.  a*%p(x)-b
/// is there a template in expr?
fn template_p(expr : Value) -> Value raise {
  if listp(expr) && memq(caar(expr), list([q_mplus, q_mtimes, q_mexpt])).truthy() {
    // for arithmetic, find a `real' format in args
    lbool(some(x => template_p(x).truthy(), cdr(expr)))
  } else {
    parse_template(expr)
  }
}

///|
fn partition_arithmetic_template(op : Value, args : Value) -> (Value, Value) raise {
  // Find the 1 (!) term or factor with a regular template in it.
  let pat = remove_if(x => !template_p(x).truthy(), args) // find arg with template in it
  if pat is Nil || cdr(pat).truthy() {
    merr("FORMAT: Pattern must contain exactly 1 template ~M", [
      cons(list1(op), args),
    ])
    |> ignore
  }
  (car(pat), simplify(cons(list1(op), remove(car(pat), args))))
}

///|
/// $%if: IF ... ELSEIF ... ELSE
fn share_miller_format__if(expr : Value, predicates : Value) -> Value raise {
  let mut ps = predicates
  let mut i = 1L
  while !(ps is Nil) &&
        !d_is_boole_eval(mfuncall(car(ps), list1(expr))).truthy() {
    ps = cdr(ps)
    i += 1L
  }
  d_format_piece(expr, nth_=Fix(i))
}

///|
/// Bag & Relation templates.
/// This function tries to get OPER at the top level of EXPR.
/// OPER must be a BAG or RELATION, as must the top layers of EXPR
/// (down to wherever OPER is found).
/// The interpretation is that a list of equations is equivalent to an
/// equation whose rhs & lhs are lists.  (and ditto for all permutations).
fn d_coerce_bag(oper : Value, expr : Value) -> Value raise {
  if !(mbagp(expr).truthy() || mrelationp(expr).truthy()) {
    merr(
      "Error: ~M is not a relation, list or array: can't be made into an ~M",
      [expr, oper],
    )
    |> ignore
  }
  let oper = getopr(oper)
  let swap = fn(op : Value, x : Value) raise {
    cons(
      list1(op),
      mapcar(
        l => simplify(cons(car(x), l)),
        transpose(mapcar(y => cdr(d_coerce_bag(op, y)), cdr(x))),
      ),
    )
  }
  if eq(caar(expr), oper) {
    // oper is already at top level.
    expr
  } else if eq(caar(expr), q_d_matrix) {
    // swap levels 2 & 3 (mlist & oper), then 1&2
    swap(
      oper,
      map1(list2(lfunc("swap", args => swap(oper, arg(args, 0))), expr)),
    )
  } else if eq(oper, q_d_matrix) {
    // swap level 1 & 2 (oper & matrix), then 2 & 3.
    map1(list2(lfunc("swap", args => swap(q_mlist, arg(args, 0))), swap(oper, expr)))
  } else {
    // swap 1st & 2nd levels.
    swap(oper, expr)
  }
}

///|
fn format_bag(expr : Value, op : Value) -> Value raise {
  map1(list2(q_d_format_piece, d_coerce_bag(op, expr)))
}

///|
/// Targeting templates.
/// mostly shorthand for things which can be done using subtemplates, but
/// more concise.
fn format_nth(expr : Value, n : Value) -> Value raise {
  if !(
      d_integerp(n).truthy() &&
      plusp(n) &&
      num_lt(n, Fix(length(expr).to_int64()))
    ) {
    merr("FORMAT ~M: ~M doesn't have an argument #~M", [
      symval(q_ear_template),
      expr,
      n,
    ])
    |> ignore
  }
  let new_ = copy_list(expr)
  let k = to_int(n)
  setf_car(nthcdr(k, new_), format_w_slo_subtemplates(nth(k, expr))) |> ignore
  simplify(new_)
}

///|
/// Polynomial, Trig & Series templates.
fn format_clist(clist : Value, function? : Value) -> Value raise {
  let call = fn(c : Value) raise {
    match function {
      Some(f) => funcall(f, [c])
      None => d_format_piece(c)
    }
  }
  let mp1 = fn(l : Value) raise {
    mapcar(p => mlist_star(call(cadr(p)), list1(cddr(p))), l)
  }
  let kind = cadr(cadr(clist))
  let tail = if eq(kind, q_d__pctpoly) ||
    eq(kind, share_miller_format__q_series) ||
    eq(kind, share_miller_format__q_taylor) {
    mp1(cddr(clist))
  } else if eq(kind, share_miller_format__q_trig) {
    mapcar(l => mlist_star(mp1(cdr(l)), Nil), cddr(clist))
  } else {
    Nil
  }
  d_uncoef(mlist_star(cadr(clist), list1(tail)))
}

///|
/// Sums
fn format_sum(sum : Value) -> Value raise {
  if atom(sum) {
    d_format_piece(sum)
  } else if specrepp(sum).truthy() {
    format_sum(specdisrep(sum))
  } else if eq(caar(sum), q_mplus) {
    simplify(map1(list2(q_format_sum, sum)))
  } else if eq(caar(sum), q_p_sum) {
    cons(car(sum), cons(d_format_piece(cadr(sum)), cddr(sum)))
  } else {
    d_format_piece(sum)
  }
}

///|
/// Products
fn format_product(prod : Value) -> Value raise {
  if atom(prod) {
    d_format_piece(prod)
  } else if specrepp(prod).truthy() {
    format_product(specdisrep(prod))
  } else {
    let op = caar(prod)
    if eq(op, q_mtimes) {
      simplify(map1(list2(q_format_product, prod)))
    } else if eq(op, q_mexpt) {
      power(format_product(second(prod)), third(prod))
    } else if eq(op, q_p_product) {
      cons(car(prod), cons(d_format_piece(cadr(prod)), cddr(prod)))
    } else {
      d_format_piece(prod)
    }
  }
}

///|
/// Fractions
fn format_fraction(frac : Value) -> Value raise {
  let n = d_format_piece(d_num(frac))
  div(n, d_format_piece(d_denom(frac)))
}

///|
/// (delete n coefs :test #'alike1 :key #'caddr)
fn share_miller_format__delete_coef(n : Value, coefs : Value) -> Value raise {
  remove_if(c => alike1(n, caddr(c)).truthy(), coefs)
}

///|
fn share_miller_format__sym(s : String) -> Value {
  sym(s)
}

///|
let share_miller_format__q_series : Value = share_miller_format__sym("$%series")

///|
let share_miller_format__q_taylor : Value = share_miller_format__sym("$%taylor")

///|
let share_miller_format__q_trig : Value = share_miller_format__sym("$%trig")

///|
fn init_share_miller_format() -> Unit raise {
  let s = share_miller_format__sym
  let df = share_miller_format__def_formatter
  // Subtemplate aids.
  // merge elements w/ following chain.
  df([q_mlist], args => format_from_chain(
    arg(args, 0),
    ear_templates=append(rest_args(args, 1), symval(q_ear_templates)),
  ))
  // preformat using template chain
  df([s("$%preformat")], args => format_w_slo_subtemplates(
    format_from_chain(arg(args, 0), ear_templates=rest_args(args, 1)),
  ))
  // subtemplate filler.
  share_miller_format__def_formatter_fn(
    [s("$%noop")],
    q_format_w_slo_subtemplates,
  )
  // Arithmetic templates
  df([q_mplus], args => {
    let expr = arg(args, 0)
    let (template, rest) = partition_arithmetic_template(
      q_mplus,
      rest_args(args, 1),
    )
    add2(format_one(sub(expr, rest), template), rest)
  })
  df([q_mtimes], args => {
    let expr = arg(args, 0)
    let (template, rest) = partition_arithmetic_template(
      q_mtimes,
      rest_args(args, 1),
    )
    mul2(format_one(div(expr, rest), template), rest)
  })
  // b^p
  df([q_mexpt], args => {
    let expr = arg(args, 0)
    let b = arg(args, 1)
    let p = arg(args, 2)
    if template_p(b).truthy() {
      power(format_one(power(expr, inv(p)), b), p)
    } else if template_p(p).truthy() {
      power(
        b,
        format_one(
          div(ftake(q_p_log, [expr]), ftake(q_p_log, [b])),
          p,
        ),
      )
    } else {
      merr("FORMAT: Pattern must contain exactly 1 template ~M", [power(b, p)])
    }
  })
  // Control templates
  // IF ... ELSEIF ... ELSE
  df([q_d__pctif], args => share_miller_format__if(
    arg(args, 0),
    rest_args(args, 1),
  ))
  // format arguments/operands
  df([s("$%expr"), s("$%expression")], args => {
    let expr = arg(args, 0)
    if d_atom(expr).truthy() {
      merr("FORMAT %EXPR: ~M doesn't have parts", [expr]) |> ignore
    }
    map1(list2(q_d_format_piece, expr))
  })
  // Convenience templates
  df([s("$%subst")], args => format_w_slo_subtemplates(
    d_substitute(mlist_star(rest_args(args, 1), Nil), arg(args, 0)),
  ))
  df([s("$%ratsubst")], args => format_w_slo_subtemplates(
    mfuncall(
      q_d_lratsubst,
      list2(mlist_star(rest_args(args, 1), Nil), arg(args, 0)),
    ),
  ))
  // `Bag' & Relation templates.
  df(
    [s("$%eq"), s("$%equation"), s("$%rel"), s("$%relation")],
    args => format_bag(
      arg(args, 0),
      if args.length() > 1 {
        args[1]
      } else {
        q_mequal
      },
    ),
  )
  df([s("$%list")], args => format_bag(arg(args, 0), q_mlist))
  // Note: %matrix subtemplates apply to ROWS. To target elements, use %list
  // for rows.
  df([s("$%matrix")], args => format_bag(arg(args, 0), q_d_matrix))
  // Targeting templates.
  share_miller_format__def_formatter_fn([s("$%arg")], q_format_nth)
  df([s("$%lhs")], args => format_nth(
    d_coerce_bag(
      if args.length() > 1 {
        args[1]
      } else {
        q_mequal
      },
      arg(args, 0),
    ),
    Fix(1L),
  ))
  df([s("$%rhs")], args => format_nth(
    d_coerce_bag(
      if args.length() > 1 {
        args[1]
      } else {
        q_mequal
      },
      arg(args, 0),
    ),
    Fix(2L),
  ))
  df([s("$%el"), s("$%element")], args => {
    let indices = rest_args(args, 1)
    let array = d_copymatrix(d_coerce_bag(q_d_matrix, arg(args, 0)))
    let v = d_format_piece(marrayref(array, car(indices), cdr(indices)))
    marrayset(v, array, indices) |> ignore
    array
  })
  df([s("$%num")], args => {
    let frac = arg(args, 0)
    let n = format_w_slo_subtemplates(d_num(frac))
    div(n, d_denom(frac))
  })
  df([s("$%denom")], args => {
    let frac = arg(args, 0)
    let n = d_num(frac)
    div(n, format_w_slo_subtemplates(d_denom(frac)))
  })
  df([s("$%match")], args => {
    let predicate = arg(args, 1)
    fn rec(xpr : Value) -> Value raise {
      if d_is_boole_eval(mfuncall(predicate, list1(xpr))).truthy() {
        format_w_slo_subtemplates(xpr)
      } else if atom(xpr) {
        xpr
      } else {
        recur_apply(lfunc("rec", a => rec(arg(a, 0))), xpr)
      }
    }
    rec(arg(args, 0))
  })
  // Actually, more like bothcoeff
  df([s("$%coeff")], args => {
    let expr = arg(args, 0)
    let mut var_ = arg(args, 1)
    let mut n = if args.length() > 2 { args[2] } else { Fix(1L) }
    if listp(var_) && eq(caar(var_), q_mexpt) {
      // (setq var (cadr var) n (mul n (caddr var))): sequential, so the
      // exponent is taken from the new VAR (a Lisp error for an atom).
      var_ = cadr(var_)
      if !listp(var_) {
        raise type_error(var_, "list")
      }
      n = mul2(n, caddr(var_))
    }
    let coefs = d_coeffs(expr, list1(var_))
    let a = mul2(
      d_format_piece(d_get_coef(coefs, list1(n))),
      power(car(cddr(cadr(coefs))), n),
    )
    add2(
      a,
      d_format_piece(d_uncoef(share_miller_format__delete_coef(n, coefs))),
    )
  })
  // Polynomial, Trig & Series templates.
  // %POLY(vars,...) : express EXPR as a polynomial in VARS, format the
  // coeffs.
  df([q_d__pctpoly, s("$%p")], args => {
    autoldchk(q_d_coeffs) |> ignore
    format_clist(d_coeffs(arg(args, 0), rest_args(args, 1)))
  })
  // %MONICPOLY : format leading coeff, then poly/lc.
  df([s("$%monicpoly"), s("$%mp")], args => {
    autoldchk(q_d_coeffs) |> ignore
    let cl = d_coeffs(arg(args, 0), rest_args(args, 1))
    let c0 = cadr(car(last(cl)))
    let a = d_format_piece(c0)
    mul2(
      a,
      format_clist(
        cl,
        function=lfunc("monic", a => d_format_piece(div(arg(a, 0), c0))),
      ),
    )
  })
  // %TRIG(vars,...): express EXPR as trig. series in VARS, format the
  // coeffs.
  df([share_miller_format__q_trig, s("$%t")], args => {
    autoldchk(q_d_trig_coeffs) |> ignore
    format_clist(d_trig_coeffs(arg(args, 0), rest_args(args, 1)))
  })
  // %SERIES(var,order), %TAYLOR(var,order): expand EXPR as series in VAR
  // to order ORDER, formats the coeffs.  %SERIES only expands arithmetic
  // expressions.
  df([share_miller_format__q_series, s("$%s")], args => {
    autoldchk(q_d_series_coeffs) |> ignore
    format_clist(d_series_coeffs(arg(args, 0), arg(args, 1), arg(args, 2)))
  })
  df([share_miller_format__q_taylor], args => {
    autoldchk(q_d_taylor_coeffs) |> ignore
    format_clist(d_taylor_coeffs(arg(args, 0), arg(args, 1), arg(args, 2)))
  })
  // Sums
  share_miller_format__def_formatter_fn([s("$%sum")], q_format_sum)
  df([s("$%partfrac"), s("$%pf")], args => format_sum(
    d_partfrac(arg(args, 0), arg(args, 1)),
  ))
  // Products
  share_miller_format__def_formatter_fn(
    [s("$%product"), s("$%prod")],
    q_format_product,
  )
  df([s("$%sqfr"), s("$%sf")], args => format_product(d_sqfr(arg(args, 0))))
  df([s("$%factor"), s("$%f")], args => {
    let expr = arg(args, 0)
    let minpoly = arg(args, 1)
    format_product(
      if d_numberp(expr).truthy() {
        expr
      } else if minpoly.truthy() {
        d_factor(expr, mp=minpoly)
      } else {
        d_factor(expr)
      },
    )
  })
  // Fractions
  share_miller_format__def_formatter_fn([s("$%frac")], q_format_fraction)
  df([s("$%ratsimp"), s("$%r")], args => format_fraction(
    d_ratsimp(arg(args, 0), Nil),
  ))
  // Complex number templates.
  // Express EXPR = A+%I*B; format A & B.
  df([s("$%rectform"), s("$%g")], args => {
    let pair = trisplit(arg(args, 0))
    let a = d_format_piece(car(pair))
    add2(a, mul2(d_format_piece(cdr(pair)), q_d__pcti))
  })
  // Express EXPR = R*exp(%I*P); format R & P.
  df([s("$%polarform")], args => {
    let pair = absarg(arg(args, 0))
    let a = d_format_piece(car(pair))
    mul2(a, power(q_d__pcte, mul2(q_d__pcti, d_format_piece(cdr(pair)))))
  })
}
