// Port of share/pdiff/pdiff.lisp (Barton Willis, 2002, 2008): a
// positional derivative package.

///|
/// (make-list n :initial-element x)
fn share_pdiff__make_list(n : Int, x : Value) -> Value {
  let mut r : Value = Nil
  for _ in 0..<n {
    r = cons(x, r)
  }
  r
}

///|
/// (mapcan #'list a b): (a1 b1 a2 b2 ...), stopping at the shorter list.
fn share_pdiff__interleave(a : Value, b : Value) -> Value {
  let c = Collector::new()
  let mut a = a
  let mut b = b
  while consp(a) && consp(b) {
    c.add(car(a))
    c.add(car(b))
    a = cdr(a)
    b = cdr(b)
  }
  c.result()
}

///|
/// Return the number of arguments (arity) for f; when the arity is
/// unknown or the arity is variable (for example addition), return false.
/// To attempt to find the arity, we check if f is a user-defined function
/// (examine the $functions list), check if f has a gradef property, check
/// if f is a trig, inverse trig, log or abs function.
///
/// Subscripted functions aren't members of $functions; for this and
/// other reasons, we disallow subscripted functions from being
/// positionally differentiated.
fn get_number_args(f : Value) -> Value raise {
  let mut z : Value = Nil
  for d in cdr(symval(q_d_functions)).iter() {
    if eql(caar(d), f) {
      z = cdr(d)
      break
    }
  }
  if z.truthy() && z.iter().all(s => symbolp(s)) {
    int(length(z))
  } else if atom(f) &&
    (
      trigp(f).truthy() ||
      arcp(f).truthy() ||
      memq(f, list([q_p_log, q_p_gamma, q_p_erf, q_p_sqrt, q_mabs])).truthy()
    ) {
    Fix(1L)
  } else if memq(
      f,
      list([q_d_bessel_i, q_d_bessel_j, q_d_bessel_k, q_d_bessel_y]),
    ).truthy() {
    Fix(2L)
  } else if equal(f, Str("^")) || equal(f, Str(".")) || equal(f, Str("^^")) {
    Fix(2L)
  } else if op_equalp(f, list1(q_lambda)).truthy() &&
    margs(second(f)).iter().all(s => symbolp(s)) {
    d_length(second(f))
  } else if symbolp(f) && get(f, q_grad).truthy() {
    int(length(first(get(f, q_grad))))
  } else if eq(t, d_constantp(f)) {
    q_constant_function
  } else {
    Nil
  }
}

///|
/// pderivop(f,n1,n2,...np) returns the function whose formula is
/// (x1,x2,...,xn) --> diff(f(x1,x2,..xn),x1,n1,x2,n2,...).
fn simp_pderivop(x : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let mut f = simplifya(cadr(x), z)
  let n = mapcar(s => simplifya(s, z), cddr(x))
  let nbr_args = get_number_args(f)
  fn pos_int(s : Value) -> Bool raise {
    integerp(s) && plusp(s)
  }

  if eq(nbr_args, q_constant_function) {
    if n.iter().any(s => pos_int(s)) {
      list([
        list2(q_lambda, q_simp),
        list2(list1(q_mlist), list2(list1(q_mlist), q_d_x)),
        Fix(0L),
      ])
    } else if n.iter().all(s => integerp(s) && zerop(s)) {
      list([
        list2(q_lambda, q_simp),
        list2(list1(q_mlist), list2(list1(q_mlist), q_d_x)),
        f,
      ])
    } else {
      cons(list2(q_d_pderivop, q_simp), cons(f, n))
    }
    // When every derivative is 0 (this includes the case that there are no
    // derivatives), return f (even when f is not a function---for example
    // pderivop(a < b) --> a < b).
  } else if n.iter().all(s => equal(Fix(0L), s)) {
    f
  } else if integerp(nbr_args) {
    if !num_eq(nbr_args, int(length(n))) {
      merror(
        Str("~:M expected ~:M derivative argument(s), but it received ~:M"),
        list([f, nbr_args, int(length(n))]),
      )
    } else {
      let mut gen_args : Value = Nil
      for _ in 0..<to_int(nbr_args) {
        gen_args = cons(gensym(), gen_args)
      }
      gen_args = cons(list1(q_mlist), gen_args)
      f = d_apply(f, gen_args)
      gen_args = cdr(gen_args)
      f = d_diff(cons(f, share_pdiff__interleave(gen_args, n)))
      list([list1(q_lambda), cons(list1(q_mlist), gen_args), f])
    }
    // pderivop(pderivop(m1,m2,...mk),n1,n2,...,nk) -->
    // pderivop(m1+n1,m2+n2,...mk+nk), provided all the m1..nk are explicit
    // nonnegative integers.
  } else if op_equalp(f, list1(q_d_pderivop)).truthy() &&
    symval(q_d_commute_partial_derivatives).truthy() &&
    n.iter().all(s => integerp(s) && num_gt(s, Fix(-1L))) &&
    cdr(margs(f)).iter().all(s => integerp(s) && num_gt(s, Fix(-1L))) &&
    length(n) == length(margs(f)) - 1 {
    let c = Collector::new()
    let mut a = cddr(f)
    let mut b = n
    while consp(a) && consp(b) {
      c.add(add2(car(a), car(b)))
      a = cdr(a)
      b = cdr(b)
    }
    cons(list2(q_d_pderivop, q_simp), cons(cadr(f), c.result()))
  } else {
    cons(list2(q_d_pderivop, q_simp), cons(f, n))
  }
}

///|
/// Extension to mapply1.
fn mapply_pdiff(
  fn_ : Value,
  args : Value,
  fnname : Value,
  form : Value,
) -> Value raise {
  ignore(fnname)
  ignore(form)
  if symval(q_d_use_pdiff).truthy() && eq(mop(fn_), q_d_pderivop) {
    if length(cddr(fn_)) == length(args) {
      cons(list2(q_mqapply, q_simp), cons(fn_, args))
    } else {
      merror(
        Str("The function ~:M expected ~:M argument(s), but it received ~:M"),
        list([cadr(fn_), int(length(cddr(fn_))), int(length(args))]),
      )
    }
  } else {
    Nil
  }
}

///|
/// Extension to sdiffgrad.
fn sdiffgrad_pdiff(e : Value, x : Value) -> Value raise {
  fn pderivop(f : Value, x : Value, n : Value) -> Value raise {
    simplify(
      cons(list1(q_mqapply), cons(cons(list1(q_d_pderivop), cons(f, n)), x)),
    )
  }

  fn incf_ith(i : Int, e : Value) -> Value raise {
    let k = nth(i, e)
    let q = copy_list(e)
    rplaca(nthcdr(i, q), add2(Fix(1L), k)) |> ignore
    q
  }

  fn i_list(i : Int, n : Int) -> Value raise {
    incf_ith(i, share_pdiff__make_list(n, Fix(0L)))
  }

  let fun = caar(e)
  if symval(q_d_use_pdiff).truthy() &&
    eq(fun, q_mqapply) &&
    eq(caaadr(e), q_d_pderivop) {
    let args = cddr(e)
    let fun = cadadr(e)
    let mut de : Value = Fix(0L)
    let n = length(args)
    let d_order = cddr(cadr(e))
    for i in 0..<n {
      de = add2(
        de,
        mul2(
          d_diff(list([nth(i, args), x])),
          pderivop(fun, args, incf_ith(i, d_order)),
        ),
      )
    }
    de
    // We disallow positional derivatives of subscripted functions and
    // lambda forms.
  } else if symval(q_d_use_pdiff).truthy() &&
    zl_get(fun, q_grad) is Nil &&
    !d_subvarp(cadr(e)).truthy() &&
    !memq(
      fun,
      list([q_mlessp, q_mleqp, q_mequal, q_mgeqp, q_mgreaterp, q_mcond, q_lambda]),
    ).truthy() {
    let args = cdr(e)
    let fun = caar(e)
    let mut de : Value = Fix(0L)
    let n = length(args)
    for i in 0..<n {
      de = add2(
        de,
        mul2(
          d_diff(list([nth(i, args), x])),
          pderivop(fun, args, i_list(i, n)),
        ),
      )
    }
    de
  } else {
    Nil
  }
}

///|
/// Display support for positional derivatives. Indicate the derivative
/// order with a subscript surrounded by parenthesis.
fn dimension_pderiv(form : Value, result : Value) -> Value raise {
  let form = cdr(form)
  let form = list2(
    list3(car(form), q_simp, q_array),
    cons(list1(Str("")), cdr(form)),
  )
  dimension_array(form, result)
}

///|
/// Extend tex to handle positional derivatives.
fn tex_pderivop(x : Value, l : Value, r : Value) -> Value raise {
  let lop = symval(q_lop)
  let rop = symval(q_rop)
  if symval(q_d_tex_uses_prime_for_derivatives).truthy() && length(x) == 3 {
    let n = car(last(x))
    let p = if num_le(n, symval(q_d_tex_prime_limit)) {
      share_pdiff__make_list(to_int(n), Str("\\prime"))
    } else {
      list([Str("("), n, Str(")")])
    }
    // We need to avoid double tex superscripts; when rop is mexpt, use parens.
    if eq(rop, q_mexpt) {
      append(
        l,
        append(
          list1(Str("\\left(")),
          append(
            tex(cadr(x), Nil, Nil, lop, rop),
            append(
              list1(Str("^{")),
              append(
                p,
                append(list1(Str("}")), append(list1(Str("\\right)")), r)),
              ),
            ),
          ),
        ),
      )
    } else {
      append(
        l,
        append(
          tex(cadr(x), Nil, Nil, lop, rop),
          append(list1(Str("^{")), append(p, append(list1(Str("}")), r))),
        ),
      )
    }
  } else if symval(q_d_tex_uses_named_subscripts_for_derivatives).truthy() &&
    num_lt(
      cddr(x).iter().fold(init=Fix(0L), (a, b) => num_add(a, b)),
      symval(q_d_tex_prime_limit),
    ) {
    let n = cddr(x)
    let v = mapcar(s => stripdollar(s), cdr(symval(q_d_tex_diff_var_names)))
    let mut p : Value = Nil
    if length(n) > length(v) {
      merror(
        Str("Not enough elements in tex_diff_var_names to tex the expression"),
        Nil,
      )
      |> ignore
    }
    for i in 0..<length(n) {
      p = append(p, share_pdiff__make_list(to_int(nth(i, n)), nth(i, v)))
    }
    append(
      l,
      append(
        tex(cadr(x), Nil, Nil, lop, rop),
        append(list1(Str("_{")), append(p, append(list1(Str("}")), r))),
      ),
    )
  } else {
    append(
      l,
      append(
        tex(cadr(x), Nil, Nil, lop, rop),
        append(
          list1(Str("_{")),
          append(
            tex_matchfix(cons(list1(q_mprogn), cddr(x)), Nil, Nil),
            append(list1(Str("}")), r),
          ),
        ),
      ),
    )
  }
}

///|
/// Convert from positional derivatives to non-positional derivatives.
fn d_convert_to_diff(e : Value) -> Value raise {
  let e = d_totaldisrep(e)
  if d_mapatom(e).truthy() {
    e
  } else if consp(e) && eq(caar(e), q_mqapply) && eq(caaadr(e), q_d_pderivop) {
    let f = second(second(e))
    let n = rest(rest(second(e)))
    let mut v = rest(rest(e))
    with_special(q_d_use_pdiff, Nil, () => {
      let mut g : Value = Nil
      let mut at_list : Value = Nil
      for _ in v.iter() {
        g = cons(gensym(), g)
      }
      let mut e = mapply(f, g, Nil)
      e = d_diff(cons(e, share_pdiff__interleave(g, n)))
      while v.truthy() {
        let vk = car(v)
        v = cdr(v)
        let gk = car(g)
        g = cdr(g)
        if symbolp(vk) {
          e = d_substitute(vk, gk, expr=e)
        } else {
          at_list = cons(take(list1(q_mequal), [gk, vk]), at_list)
        }
      }
      if at_list.truthy() {
        d_at(e, simplify(cons(list1(q_mlist), at_list)))
      } else {
        e
      }
    })
  } else {
    mapply(mop(e), mapcar(a => d_convert_to_diff(a), margs(e)), Nil)
  }
}

///|
/// The MAYBE-RESET part of DEFMVAR: record the initial value of a
/// variable so that `reset` restores it.
fn share_pdiff__defmvar_reset(var_ : Value, val : Value) -> Unit raise {
  let table = symval(q_ear_variable_initial_values)
  if hash_table_p(table) && gethash(var_, table) is Nil {
    sethash(var_, table, val) |> ignore
  }
}

///|
fn init_share_pdiff() -> Unit raise {
  share_pdiff__defmvar_reset(q_d_use_pdiff, Nil)
  share_pdiff__defmvar_reset(q_d_commute_partial_derivatives, t)
  share_pdiff__defmvar_reset(q_d_tex_uses_prime_for_derivatives, Nil)
  share_pdiff__defmvar_reset(q_d_tex_prime_limit, Fix(3L))
  share_pdiff__defmvar_reset(q_d_tex_uses_named_subscripts_for_derivatives, Nil)
  share_pdiff__defmvar_reset(
    q_d_tex_diff_var_names,
    list([list1(q_mlist), q_d_x, q_d_y, q_d_z]),
  )
  d_put(q_d_pdiff, Flo(1.4), q_d_version) |> ignore
  // Required for wxMaxima display.
  setf_get(q_d_pderivop, q_wxxml, q_wxxml_pderivop) |> ignore
  putprop(q_d_pderivop, q_simp_pderivop, q_operators) |> ignore
  set(q_d_use_pdiff, t) |> ignore
  setf_get(q_d_pderivop, q_mapply1_extension, q_mapply_pdiff) |> ignore
  setf_get(q_d_pderivop, q_dimension, q_dimension_pderiv) |> ignore
  if !boundp(q_d_tex_diff_var_names) {
    set(q_d_tex_diff_var_names, list([list1(q_mlist), q_d_x, q_d_y, q_d_z]))
    |> ignore
  }
  setf_get(q_d_pderivop, q_tex, q_tex_pderivop) |> ignore
}
