// Port of share/contrib/altsimp/altsimp.lisp (Barton Willis with help from
// Richard Fateman): an alternative SIMPLUS that simplifies a sum of n terms
// with O(n log n) calls to GREAT, optionally adding the extended reals
// (minf, inf, infinity, und, ind) "infinity correctly"
// (use_extended_real_arithmetic).
//
// Loading the Lisp file redefines SIMPLUS, PLS and PLUSIN. The port
// installs the replacements (share_altsimp__simplus, __pls, __plusin) in
// those symbols' function cells when altsimp is loaded. SIMPLIFYA reaches
// SIMPLUS through the OPERATORS property of MPLUS (a FUNCALL of the symbol),
// so every sum simplified by SIMPLIFYA uses the new code; MoonBit code that
// calls `simplus`, `pls` or `plusin` directly (combin, laplac, schatc,
// sprdet, ...) keeps calling the standard versions.

///|
/// Return true iff z = 0, z = 0.0, z = -0.0, or is a bigfloat zero.
fn mzerop(z : Value) -> Value raise {
  if integerp(z) {
    lbool(eql(z, int(0)))
  } else if bigfloatp(z).truthy() {
    lbool(eql(cadr(z), int(0)))
  } else if floatp(z) {
    // allow negative zero to pass
    lbool(eql(z, Flo(0.0)) || eql(z, Flo(-0.0)))
  } else {
    Nil
  }
}

///|
/// Return true iff x = integer^(rational)
fn surd_p(x : Value) -> Value raise {
  if mexptp(x).truthy() && integerp(cadr(x)) {
    d_ratnump(caddr(x))
  } else {
    Nil
  }
}

///|
/// Return true iff x = integer^(rational + ...)
fn generalized_surd_p(x : Value) -> Value raise {
  if mexptp(x).truthy() && integerp(cadr(x)) && mplusp(caddr(x)).truthy() {
    let r = d_ratnump(second(caddr(x)))
    if r.truthy() {
      r
    } else {
      lbool(integerp(second(caddr(x))))
    }
  } else {
    Nil
  }
}

///|
fn surd_convert(x : Value) -> Value raise {
  if integerp(x) || mnump(x).truthy() {
    cons(int(1), x)
  } else if surd_p(x).truthy() {
    // x = a^(p/q) = a^n * a^(p/q - n), where n = floor(p/q).
    let a = cadr(x)
    let p = caddr(x)
    let q = d_denom(p)
    let p = d_num(p)
    let n = floor1(num_div(p, q))
    cons(ftake(q_mexpt, [a, sub(caddr(x), n)]), ftake(q_mexpt, [a, n]))
  } else if generalized_surd_p(x).truthy() {
    // x = ((mexpt) a ((mplus) n a1 a2 ...)))
    let a = second(x)
    let n = second(third(x))
    let p = d_num(n)
    let q = d_denom(n)
    let n = floor1(num_div(p, q))
    cons(ftake(q_mexpt, [a, sub(third(x), n)]), ftake(q_mexpt, [a, n]))
  } else {
    cons(x, int(1))
  }
}

///|
/// Convert a term (a non sum expression) to the form (e . coefficient),
/// where coefficient is a rational or floating point number. Factors of the
/// form integer^(rational) are converted by surd-convert.
fn convert_to_coeff_form(x : Value) -> Value raise {
  let mut c = int(1)
  let mut qq = int(1)
  if mnump(x).truthy() {
    cons(int(1), x)
  } else if surd_p(x).truthy() || generalized_surd_p(x).truthy() {
    surd_convert(x)
  } else if mtimesp(x).truthy() {
    let mut x = cdr(x) // remove (car x) which is (mtimes ..)
    while mnump(car(x)).truthy() ||
          surd_p(car(x)).truthy() ||
          generalized_surd_p(car(x)).truthy() {
      let xx = surd_convert(car(x))
      c = mul2(c, cdr(xx))
      qq = mul2(qq, car(xx))
      x = cdr(x)
    }
    if !eql(qq, int(1)) {
      x = cons(qq, x)
    }
    if x is Nil {
      x = cons(int(1), x)
    }
    if cdr(x) is Nil {
      // if only one more item, that's it.
      cons(car(x), c)
    } else {
      cons(fapply(q_mtimes, x), c)
    }
  } else {
    cons(x, int(1))
  }
}

///|
/// Sometimes the second argument isn't simplified, so this calls ftake*.
fn number_times_expr(cf : Value, e : Value) -> Value raise {
  ftake_star(q_mtimes, [cf, e])
}

///|
/// Add an expression x to a list of equalities l.
fn add_expr_mequal(x : Value, l : Value) -> Value raise {
  let mut l = mapcar(e => cdr(e), l)
  l = cons(list([x, x]), l)
  l = list([
    share_altsimp__reduce_add(mapcar(e => first(e), l)),
    share_altsimp__reduce_add(mapcar(e => second(e), l)),
  ])
  fapply(q_mequal, l)
}

///|
/// (reduce #'add l)
fn share_altsimp__reduce_add(l : Value) -> Value raise {
  match l {
    Nil => addn(Nil, t)
    _ => {
      let mut acc = car(l)
      for x in cdr(l).iter() {
        acc = add2(acc, x)
      }
      acc
    }
  }
}

///|
/// (reduce #'addmx l) for a list of at least two members.
fn share_altsimp__reduce_addmx(l : Value) -> Value raise {
  let mut acc = car(l)
  for x in cdr(l).iter() {
    acc = addmx(acc, x)
  }
  acc
}

///|
fn add_expr_mrat(x : Value, l : Value) -> Value raise {
  ratf(cons(list1(q_mplus), cons(ratf(x), l)))
}

///|
fn add_expr_taylor(x : Value, l : Value) -> Value raise {
  d_taylor(cons(list1(q_mplus), cons(x, l)), Nil)
}

///|
fn add_expr_mlist(x : Value, l : Value) -> Value raise {
  let l = if cdr(l).truthy() {
    share_altsimp__reduce_addmx(l)
  } else {
    car(l)
  }
  fapply(q_mlist, mapcar(s => add2(x, s), cdr(l)))
}

///|
/// Simple demo showing how to define addition for a new object.
/// We could append simplification rules for intervals:
///  (a) interval(a,a) --> a,
///  (b) if p > q then interval(p,q) --> standardized empty interval?
fn add_expr_interval(x : Value, l : Value) -> Value raise {
  let l = mapcar(s => cons(list1(q_mlist), cdr(s)), l)
  let l = if cdr(l).truthy() {
    share_altsimp__reduce_addmx(l)
  } else {
    car(l)
  }
  fapply(q_d_interval, mapcar(s => add2(x, s), cdr(l)))
}

///|
/// The Lisp ERRCATCH macro: (value) on success, NIL after a Maxima or
/// Lisp error.
fn share_altsimp__errcatch(f : () -> Value raise) -> Value? raise {
  let ec = cons(symval(q_bindlist), symval(q_loclist))
  with_specials([(q_errcatch, ec), (q_ear_mdebug, Nil)], () => {
    let r = f() catch {
      LispError::Throw(tag, _) as e =>
        if eq(tag, q_macsyma_quit) || eq(tag, q_errorsw) || eq(tag, q_rat_err) {
          errlfun1(ec) |> ignore
          return None
        } else {
          raise e
        }
      LispError::ReturnFrom(_, _) as e => raise e
      LispError::Go(_) as e => raise e
      e => {
        if !is_maxima_error(e) {
          let msg = match e {
            LispError::SimpleError(m) => m
            LispError::Condition(_, m, _) => m
            _ => e.to_string()
          }
          set(q_d_error, mk_simp(q_mlist, [Str(msg)])) |> ignore
          if symval(q_d_errormsg).truthy() {
            d_errormsg() |> ignore
          }
        }
        errlfun1(ec) |> ignore
        return None
      }
    }
    Some(r)
  })
}

///|
/// Add expression x to a CL list of matrices l.
fn add_expr_matrix(x : Value, l : Value) -> Value raise {
  let l = if cdr(l).truthy() {
    let r = with_special(q_d_errormsg, Nil, () => share_altsimp__errcatch(() => share_altsimp__reduce_addmx(
      l,
    )))
    match r {
      Some(v) => v
      None => merror(Str("Attempt to add noncomformable matrices"), Nil)
    }
  } else {
    car(l)
  }
  if symval(q_d_listarith).truthy() && d_matrixp(l).truthy() {
    fapply(q_d_matrix, cdr(add2(x, d_args(l))))
  } else {
    list([get(q_mplus, q_msimpind), x, l])
  }
}

///|
/// Using hash table look up, add two extended real numbers. The supported
/// extended real numbers are 'minf', 'ind', 'und', 'inf', and 'infinity'.
/// If (a,b) isn't a hashtable key, this function looks for the key (b,a).
fn add_extended_real(a : Value, b : Value) -> Value raise {
  let table = symval(q_ear_extended_real_add_table)
  let dflt = {
    let (v, found) = gethash2(list([b, a]), table)
    if found {
      v
    } else {
      q_d_und
    }
  }
  let (v, found) = gethash2(list([a, b]), table)
  if found {
    v
  } else {
    dflt
  }
}

///|
/// Add an expression 'x' to a nonempty list `l` of extended real numbers.
/// When it is certain that 'x' cannot be an extended real, return the sum
/// of the members of l; otherwise, return a sum nounform.
fn add_expr_infinities(x : Value, l : Value) -> Value raise {
  let mut acc = car(l)
  for y in cdr(l).iter() {
    acc = add_extended_real(acc, y)
  }
  // Arguably, we don't want to do 1/x + inf = inf (what if x = 0?). So
  // when it is certain that x is not an extended real, return l; otherwise
  // return x + l. Here "certain" means a number.
  if mnump(x).truthy() {
    acc
  } else {
    cons(
      get(q_mplus, q_msimpind),
      sort_list(list([x, acc]), (p, q) => great(p, q).truthy()),
    )
  }
}

///|
/// PLS of altsimp.lisp: the standard simplus helpers are not used.
fn share_altsimp__pls(x : Value, out : Value) -> Value raise {
  mtell(list([Str("in pls; x = ~M,  out = ~M ~%"), x, out])) |> ignore
  merror(Str("Error: called pls ~%"), Nil)
}

///|
/// PLUSIN of altsimp.lisp.
fn share_altsimp__plusin(x : Value, fm : Value) -> Value raise {
  mtell(list([Str("in plusin; x = ~M,  fm = ~M ~%"), x, fm])) |> ignore
  merror(Str("Error: called plusin ~%"), Nil)
}

///|
/// SIMPLUS of altsimp.lisp.
///
/// In the main loop, each term of the sum is converted to coefficient form
/// N . E, where N is a Maxima number and E is the base expression. These
/// pairs are inserted into a hash table (test EQUAL) keyed on E, which
/// combines literally identical base expressions. The entries are then
/// sorted with GREAT, so that alike1 expressions are adjacent, and the
/// WHILE loop combines the remaining common terms using ALIKE1.
///
/// The DO-OVER mechanism handles the case where combining coefficients
/// produces +-1 times an expression that is itself an MPLUS, for example
/// 5*(a+b) - 4*(a+b) + a.
fn share_altsimp__simplus(l : Value, w : Value, z : Value) -> Value raise {
  let _ = w
  let mut acc : Value = Nil
  let mut num_sum = int(0)
  let mut do_over = false
  let mut mequal_terms : Value = Nil
  let mut mrat_terms : Value = Nil
  let mut inf_terms : Value = Nil
  let mut matrix_terms : Value = Nil
  let mut mlist_terms : Value = Nil
  let mut taylor_terms : Value = Nil
  let mut interval_terms : Value = Nil
  let expr_hash = make_hash_table(kind=Equal)
  let mut l = margs(l)
  // simplify and flatten
  for li0 in l.iter() {
    let mut li = simplifya(li0, z)
    // When numer is true, simplifya converts %pi & %phi to their binary64
    // values, but only converts %e when both numer & %enumer are true. Here
    // we convert %e to its binary64 value.
    if symval(q_d_numer).truthy() && atom(li) && eq(li, q_d__pcte) {
      li = symval(q_p_e_float64)
    }
    if mplusp(li).truthy() {
      acc = append(acc, cdr(li))
    } else {
      acc = cons(li, acc)
    }
  }
  l = acc
  acc = Nil
  for li0 in l.iter() {
    let li = li0
    if mnump(li).truthy() {
      num_sum = addk(num_sum, li)
    } else if consp(li) &&
      consp(car(li)) &&
      memq(
        caar(li),
        list([q_mequal, q_mrat, q_d_matrix, q_mlist, q_d_interval]),
      ).truthy() {
      // factor out infrequent cases.
      let op = caar(li)
      if eq(op, q_mequal) {
        mequal_terms = cons(li, mequal_terms)
      } else if d_taylorp(li).truthy() {
        taylor_terms = cons(li, taylor_terms)
      } else if eq(op, q_mrat) {
        mrat_terms = cons(li, mrat_terms)
      } else if eq(op, q_d_matrix) {
        matrix_terms = cons(li, matrix_terms)
      } else if eq(op, q_d_interval) {
        interval_terms = cons(li, interval_terms)
      } else if eq(op, q_mlist) {
        if symval(q_d_listarith).truthy() {
          mlist_terms = cons(li, mlist_terms)
        } else {
          acc = cons(convert_to_coeff_form(li), acc)
        }
      }
    } else if symval(q_d_use_extended_real_arithmetic).truthy() &&
      memq(li, list([q_d_minf, q_d_inf, q_d_infinity, q_d_und, q_d_ind])).truthy() {
      inf_terms = cons(li, inf_terms)
    } else {
      let li = convert_to_coeff_form(li)
      let (cf, found) = gethash2(car(li), expr_hash)
      let cf = if found { cf } else { int(0) }
      sethash(car(li), expr_hash, add2(cdr(li), cf)) |> ignore
    }
  }
  // push expressions in the hashtable into the accumulator acc; sort acc.
  maphash((cf, a) => acc = cons(cons(cf, a), acc), expr_hash)
  l = sort_list(acc, (p, q) => great(car(p), car(q)).truthy())
  // common term crunch: when the new coefficient is -1 or 1 (for example,
  // 5*a - 4*a), set the "do-over" flag to true.
  acc = Nil
  while l.truthy() {
    let mut x = car(l)
    l = cdr(l)
    let mut cf = cdr(x)
    x = car(x)
    while l.truthy() && alike1(x, caar(l)).truthy() {
      cf = addk(cf, cdr(car(l)))
      l = cdr(l)
    }
    if (eql(cf, int(1)) || eql(cf, int(-1))) && mplusp(x).truthy() {
      do_over = true
    }
    x = number_times_expr(cf, x)
    if mnump(x).truthy() {
      num_sum = addk(num_sum, x)
    } else if !mzerop(x).truthy() {
      acc = cons(x, acc)
    }
  }
  // Do x + 0 --> x, x + 0.0 --> x, and x + 0.0b0 --> x.
  if !mzerop(num_sum).truthy() {
    acc = cons(num_sum, acc)
  }
  acc = if do_over {
    fapply(q_mplus, acc)
  } else if acc is Nil {
    num_sum
  } else if cdr(acc) is Nil {
    car(acc)
  } else {
    cons(get(q_mplus, q_msimpind), acc)
  }
  // special case dispatch
  if mequal_terms.truthy() {
    acc = add_expr_mequal(acc, mequal_terms)
  }
  if taylor_terms.truthy() {
    acc = add_expr_taylor(acc, taylor_terms)
  }
  if mrat_terms.truthy() {
    acc = add_expr_mrat(acc, mrat_terms)
  }
  if mlist_terms.truthy() {
    acc = add_expr_mlist(acc, mlist_terms)
  }
  if interval_terms.truthy() {
    acc = add_expr_interval(acc, interval_terms)
  }
  if matrix_terms.truthy() {
    acc = add_expr_matrix(acc, matrix_terms)
  }
  if inf_terms.truthy() {
    acc = add_expr_infinities(acc, inf_terms)
  }
  acc
}

///|
fn init_share_altsimp() -> Unit raise {
  // The addition table for extended reals {minf, inf, ind, und, infinity}:
  // only the "upper half" of the table; add-extended-real uses
  // commutativity.
  defvar_init(q_ear_extended_real_add_table, make_hash_table(kind=Equal))
  let table = symval(q_ear_extended_real_add_table)
  let entries = [
    (q_d_minf, q_d_minf, q_d_minf),
    (q_d_minf, q_d_inf, q_d_und),
    (q_d_minf, q_d_infinity, q_d_und),
    (q_d_minf, q_d_und, q_d_und),
    (q_d_minf, q_d_ind, q_d_minf),
    (q_d_inf, q_d_inf, q_d_inf),
    (q_d_inf, q_d_infinity, q_d_und),
    (q_d_inf, q_d_und, q_d_und),
    (q_d_inf, q_d_ind, q_d_inf),
    (q_d_infinity, q_d_infinity, q_d_und),
    (q_d_infinity, q_d_und, q_d_und),
    (q_d_infinity, q_d_ind, q_d_infinity),
    (q_d_ind, q_d_ind, q_d_ind),
    (q_d_ind, q_d_und, q_d_und),
    (q_d_und, q_d_und, q_d_und),
  ]
  for e in entries {
    sethash(list([e.0, e.1]), table, e.2) |> ignore
  }
  // The binary64 value of %e.
  defvar_init(q_p_e_float64, lexp(Flo(1.0)))
  // The redefinitions of SIMPLUS, PLS and PLUSIN.
  defun(q_pls, args => share_altsimp__pls(arg(args, 0), arg(args, 1)), name="pls")
  defun(q_plusin, args => share_altsimp__plusin(arg(args, 0), arg(args, 1)), name="plusin")
  defun(
    q_simplus,
    args => share_altsimp__simplus(arg(args, 0), arg(args, 1), arg(args, 2)),
    name="simplus",
  )
}
