// Port of src/maxmin.lisp: max, min, compare, rationalize.

///|
/// Text of a Lisp error, like `(princ-to-string e)` on a condition.
fn maxmin__error_text(e : Error) -> String {
  match e {
    LispError::SimpleError(m) => m
    LispError::Condition(_, m, _) => m
    _ => e.to_string()
  }
}

///|
/// Expansion of the `errcatch` macro (errset.lisp): evaluate `f`; on
/// success return `(list value)`, on a Maxima or Lisp error clean up and
/// return nil.
fn maxmin__errcatch(f : () -> Value raise) -> Value raise {
  let ec = cons(symval(q_bindlist), symval(q_loclist))
  with_specials([(q_errcatch, ec), (q_ear_mdebug, Nil)], () => {
    let r = maxmin__with_errcatch_tag_errors(f) catch {
      e if is_maxima_error(e) => {
        errlfun1(ec) |> ignore
        return Nil
      }
      LispError::Throw(_, _) as e => raise e
      LispError::ReturnFrom(_, _) as e => raise e
      LispError::Go(_) as e => raise e
      e => {
        set(
          q_d_error,
          list2(list2(q_mlist, q_simp), Str(maxmin__error_text(e))),
        )
        |> ignore
        if symval(q_d_errormsg).truthy() {
          d_errormsg() |> ignore
        }
        errlfun1(ec) |> ignore
        return Nil
      }
    }
    list1(r)
  })
}

///|
/// Expansion of `with-errcatch-tag-$errors` / `rat-error-to-merror`.
fn maxmin__with_errcatch_tag_errors(f : () -> Value raise) -> Value raise {
  let caught = f() catch {
    LispError::Throw(tag, args) if eq(tag, q_rat_err) => {
      apply(q_merror, args) |> ignore
      return Nil
    }
    LispError::Throw(tag, _) if eq(tag, q_macsyma_quit) || eq(tag, q_errorsw) =>
      None
    e => raise e
  } noraise {
    v => Some(v)
  }
  match caught {
    Some(v) => v
    None =>
      with_special(q_ear_merror_signals__dolerror_p, t, () => merr(
        "An error was caught by errcatch.",
        [],
      ))
  }
}

///|
fn maxmin_effort_assign(xx : Value, y : Value) -> Value raise {
  ignore(xx)
  if integerp(y) && num_gt(y, int(-1)) {
    set(q_d_maxmin_effort, y)
  } else {
    merr(
      "The value of maxmin_effort must be a nonnegative integer; found ~M ~%",
      [y],
    )
  }
}

///|
fn betweenp(x : Value, p : Value) -> Value raise {
  let mut p = p
  while !(p is Nil) {
    let pk = car(p)
    p = cdr(p)
    let mut q = p
    while !(q is Nil) {
      let qk = car(q)
      q = cdr(q)
      let s = csign(d_factor(mul2(sub(x, pk), sub(qk, x))))
      if eq(s, q_d_pos) || eq(s, q_d_pz) {
        return t
      }
    }
  }
  Nil
}

///|
fn simplim_dolmax(expr : Value, var_ : Value, val : Value) -> Value raise {
  simplifya(
    cons(list1(q_d_max), mapcar(e => limit(e, var_, val, q_think), cdr(expr))),
    t,
  )
}

///|
fn max_p(e : Value) -> Value raise {
  lbool(consp(e) && eq(caar(e), q_d_max))
}

///|
fn min_p(e : Value) -> Value raise {
  lbool(consp(e) && eq(caar(e), q_d_min))
}

///|
fn maxmin__sort(l : Value) -> Value raise {
  sort_list(l, (a, b) => d_orderlessp(a, b).truthy())
}

///|
fn maxmin__effort_gt(n : Int) -> Bool raise {
  num_gt(symval(q_d_maxmin_effort), int(n))
}

///|
fn simp_max(l : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  let mut acc : Value = Nil
  let mut num_max : Value = Nil
  let mut issue_warning = false
  // L is sorted and pruned destructively below, so copy the argument lists
  // of the input and of any nested max.
  let mut l = copy_list(cdr(l))

  // When maxmin_effort > 0, simplify each member of l and flatten.
  // Additionally, we accumulate the largest real number.
  if maxmin__effort_gt(0) {
    for li0 in l.iter() {
      let li = maybe_simplifya(specrepcheck(li0), z)
      if max_p(li).truthy() {
        acc = append(acc, copy_list(cdr(li)))
      } else if mnump(li).truthy() {
        num_max = if num_max is Nil || mgrp(li, num_max).truthy() {
          li
        } else {
          num_max
        }
      } else {
        acc = cons(li, acc)
      }
    }
    if num_max.truthy() {
      acc = cons(num_max, acc)
    }
    l = acc
  }

  // Sort and remove duplicates.
  if maxmin__effort_gt(0) {
    l = sorted_remove_duplicates(maxmin__sort(l))
  }

  // When every member of `l` appears to be real, set `all-real` to true.
  let all_real = every(x => lenient_extended_realp(x).truthy(), l)
  // When maxmin_effort > 2 and all-real is true, if e and -e are members of
  // l, replace e & -e by abs(e).
  if maxmin__effort_gt(2) && all_real {
    let mut pp = simplifya(cons(list1(q_d_set), l), t)
    let qq = simplifya(cons(list1(q_d_set), mapcar(x => limitneg(x), l)), t)
    let mut nn = d_intersection(pp, list1(qq))
    pp = d_setdifference(pp, nn)
    if !d_emptyp(nn).truthy() {
      nn = mapcar(s => take(list1(q_mabs), [s]), cdr(nn))
      nn = simplifya(cons(list1(q_d_set), nn), t)
      pp = d_union(list2(pp, nn))
    }
    l = cdr(pp)
  }

  // Accumulate the maximum in the list acc.
  if maxmin__effort_gt(1) && all_real {
    acc = Nil
    for x in l.iter() {
      let mut done = false
      for ai in list_to_array(acc) {
        let sgn = d_compare(x, ai)
        if equal(sgn, Str(">")) || equal(sgn, Str(">=")) {
          acc = maxmin__delete_last_eq(ai, acc)
        } else if eq(sgn, q_d_notcomparable) {
          issue_warning = true
        } else if equal(sgn, Str("<")) ||
          equal(sgn, Str("=")) ||
          equal(sgn, Str("<=")) {
          done = true
          break
        }
      }
      if !done {
        acc = cons(x, acc)
      }
    }
    l = acc
  }

  // When issue-warning is false, all-real is true, and maxmin_effort > 2,
  // use the betweenp simplification.
  if !issue_warning && maxmin__effort_gt(2) && all_real {
    acc = Nil
    let mut sgn = cdr(l)
    for ai in l.iter() {
      if !betweenp(ai, sgn).truthy() {
        acc = cons(ai, acc)
      }
      sgn = append(cdr(sgn), list1(ai))
    }
    l = acc
  }

  // Finally, do a few clean ups:
  l = if all_real && !issue_warning { delete(q_d_minf, l) } else { l }
  if l is Nil {
    q_d_minf
  } else if all_real && !issue_warning && memq(q_d_inf, l).truthy() {
    q_d_inf
  } else if cdr(l) is Nil && lenient_extended_realp(car(l)).truthy() {
    car(l)
  } else {
    cons(get(q_d_max, q_msimpind), maxmin__sort(l))
  }
}

///|
/// `(delete x l :test #'eq :from-end t :count 1)`
fn maxmin__delete_last_eq(x : Value, l : Value) -> Value {
  let arr = list_to_array(l)
  let mut idx = -1
  for i, v in arr {
    if eq(v, x) {
      idx = i
    }
  }
  if idx < 0 {
    return l
  }
  let r = []
  for i, v in arr {
    if i != idx {
      r.push(v)
    }
  }
  list(r)
}

///|
fn limitneg(x : Value) -> Value raise {
  if eq(x, q_d_minf) {
    q_d_inf
  } else if eq(x, q_d_inf) {
    q_d_minf
  } else if eq(x, q_d_und) || eq(x, q_d_ind) || eq(x, q_d_infinity) {
    x
  } else {
    with_special(q_d_negdistrib, t, () => mul2(int(-1), x))
  }
}

///|
fn simplim_dolmin(expr : Value, var_ : Value, val : Value) -> Value raise {
  simplifya(
    cons(list1(q_d_min), mapcar(e => limit(e, var_, val, q_think), cdr(expr))),
    t,
  )
}

///|
fn simp_min(l : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  let mut acc : Value = Nil
  for li0 in cdr(l).iter() {
    let li = maybe_simplifya(specrepcheck(li0), z)
    // convert min(a, min(b,c)) --> min(a,b,c)
    if min_p(li).truthy() {
      acc = append(acc, cdr(li))
    } else {
      acc = cons(li, acc)
    }
  }
  let mut l = mapcar(x => limitneg(x), acc)
  l = simplifya(cons(list1(q_d_max), l), t)
  if max_p(l).truthy() {
    cons(get(q_d_min, q_msimpind), maxmin__sort(mapcar(x => limitneg(x), cdr(l))))
  } else {
    limitneg(l)
  }
}

///|
fn maximin(l : Value, op : Value) -> Value raise {
  simplify(cons(list1(op), l))
}

///|
fn d_lmax(e : Value) -> Value raise {
  simplify(cons(list1(q_d_max), require_list_or_set(e, q_d_lmax)))
}

///|
fn d_lmin(e : Value) -> Value raise {
  simplify(cons(list1(q_d_min), require_list_or_set(e, q_d_lmin)))
}

///|
fn d_compare(a : Value, b : Value) -> Value raise {
  // Simplify expressions with infinities.
  let mut a = ratdisrep(a)
  let mut b = ratdisrep(b)
  let infs = list([q_d_inf, q_d_minf, q_d_infinity])
  if amongl(infs, a).truthy() {
    a = d_limit(list1(a))
  }
  if amongl(infs, b).truthy() {
    b = d_limit(list1(b))
  }
  let bad = list([q_d_infinity, q_d_ind, q_d_und])
  if amongl(bad, a).truthy() || amongl(bad, b).truthy() {
    q_d_notcomparable
  } else if !lenient_extended_realp(a).truthy() ||
    !lenient_extended_realp(b).truthy() {
    if eq(t, meqp(a, b)) {
      Str("=")
    } else {
      q_d_notcomparable
    }
  } else {
    a = sub(a, b)
    if num_ge(symval(q_d_maxmin_effort), int(10)) &&
      amongl(list2(q_d_minf, q_d_inf), a).truthy() &&
      lenient_extended_realp(a).truthy() {
      a = d_limit(list1(a))
    }
    if num_ge(symval(q_d_maxmin_effort), int(10)) {
      a = sratsimp(d_trigreduce(a))
    }
    let sgn = csign(a)
    if eq(sgn, q_d_neg) {
      Str("<")
    } else if eq(sgn, q_d_nz) {
      Str("<=")
    } else if eq(sgn, q_d_pz) {
      Str(">=")
    } else if eq(sgn, q_d_pos) {
      Str(">")
    } else if eq(sgn, q_d_pn) {
      Str("#")
    } else if eq(sgn, q_d_zero) {
      Str("=")
    } else {
      q_d_unknown
    }
  }
}

///|
fn lenient_extended_realp(e : Value) -> Value raise {
  if mbagp(e).truthy() ||
    d_featurep(e, q_d_nonscalar).truthy() ||
    mrelationp(e).truthy() ||
    arrayp(e) ||
    d_member(e, symval(q_d_arrays)).truthy() ||
    amongl(
      list([
        q_d_infinity,
        q_d__pcti,
        q_d_und,
        q_d_ind,
        q_d_false,
        q_d_true,
        t,
        Nil,
        q_d_conjugate,
      ]),
      e,
    ).truthy() {
    return Nil
  }
  let s = with_special(q_d_errormsg, Nil, () => maxmin__errcatch(() => d_sign(
    e,
  )))
  memq(
    car(s),
    list([q_d_pnz, q_d_neg, q_d_nz, q_d_zero, q_d_pz, q_d_pos, q_d_pn]),
  )
}

///|
fn lenient_realp(e : Value) -> Value raise {
  if d_freeof(list([q_d_inf, q_d_minf, e])).truthy() {
    lenient_extended_realp(e)
  } else {
    Nil
  }
}

///|
/// The definition of $RATIONALIZE installed by
/// share/numeric/decfp-core.lisp, which redefines it when loaded.
let maxmin__redefined_rationalize : Ref[((Value) -> Value raise)?] = Ref::new(None)

///|
fn d_rationalize(e : Value) -> Value raise {
  if maxmin__redefined_rationalize.val is Some(redefined) {
    return redefined(e)
  }
  let e = ratdisrep(e)
  match e {
    Flo(d) => {
      let (significand, expon, sign) = integer_decode_float(d)
      cl_rat_to_maxima(
        num_mul(
          num_mul(int(sign), from_big(significand)),
          expt(int(2), int(expon)),
        ),
      )
    }
    _ =>
      if d_bfloatp(e).truthy() {
        cl_rat_to_maxima(
          num_mul(
            cadr(e),
            expt(int(2), num_sub(caddr(e), third(car(e)))),
          ),
        )
      } else if d_mapatom(e).truthy() {
        e
      } else if d_subvarp(mop(e)).truthy() {
        // subscripted function
        subfunmake(
          subfunname(e),
          mapcar(x => d_rationalize(x), subfunsubs(e)),
          mapcar(x => d_rationalize(x), subfunargs(e)),
        )
      } else {
        recur_apply(q_d_rationalize, e)
      }
  }
}

///|
fn init_maxmin() -> Unit raise {
  d_put(q_d_maxmin, int(2), q_d_version) |> ignore
  set(q_d_props, remove(q_d_maxmin, symval(q_d_props))) |> ignore
  putprop(q_d_max, q_d_max, q_verb) |> ignore
  putprop(q_d_min, q_d_min, q_verb) |> ignore
  setf_get(q_d_max, q_msimpind, list2(q_d_max, q_simp)) |> ignore
  setf_get(q_d_min, q_msimpind, list2(q_d_min, q_simp)) |> ignore
  putprop(q_d_maxmin_effort, q_maxmin_effort_assign, q_assign) |> ignore
  putprop(q_d_max, q_simplim_dolmax, q_simplim_pctfunction) |> ignore
  putprop(q_d_max, q_simp_max, q_operators) |> ignore
  putprop(q_d_min, q_simplim_dolmin, q_simplim_pctfunction) |> ignore
  putprop(q_d_min, q_simp_min, q_operators) |> ignore
}
