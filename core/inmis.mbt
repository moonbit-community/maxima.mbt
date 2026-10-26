// Port of src/inmis.lisp: $unknown, $listofvars, $reset.

///|
fn d_unknown(f : Value) -> Value raise {
  catch_tag(q_unknown, () => unknown(specrepcheck(f)))
}

///|
fn unknown(f : Value) -> Value raise {
  if mapatom(f).truthy() {
    Nil
  } else if eq(caar(f), q_mqapply) && !zl_get(caaadr(f), q_specsimp).truthy() {
    throw_tag(q_unknown, t)
  } else if !zl_get(caar(f), q_operators).truthy() {
    throw_tag(q_unknown, t)
  } else {
    mapc(x => unknown(x) |> ignore, cdr(f)) |> ignore
    Nil
  }
}

///|
fn d_listofvars(e : Value) -> Value raise {
  with_special(q_listofvars, list1(list1(q_mlist)), fn() {
    let mut e = e
    if d_ratp(e).truthy() {
      if memq(q_trunc, cddar(e)).truthy() {
        e = d_taytorat(e)
      }
      e = cons(
        list1(q_mlist),
        sublis(
          // GENSYMLIST
          mapcar2((a, b) => cons(a, b), car(cdr(cddar(e))), caddar(e)),
          // VARLIST
          union_star(listovars(cadr(e)), listovars(cddr(e))),
        ),
      )
    }
    atomvars(e) |> ignore
    if !symval(q_d_listdummyvars).truthy() {
      for u in cdr(symval(q_listofvars)).iter() {
        if freeof(u, e).truthy() {
          set(q_listofvars, inmis__delete1_equal(u, symval(q_listofvars)))
          |> ignore
        }
      }
    }
    symval(q_listofvars)
  })
}

///|
/// `(delete x l :count 1 :test #'equal)`, non-destructively.
fn inmis__delete1_equal(x : Value, l : Value) -> Value {
  let c = Collector::new()
  let mut p = l
  while p is Cons(cell) {
    if equal(cell.car, x) {
      c.append_list(cell.cdr)
      return c.result()
    }
    c.add(cell.car)
    p = cell.cdr
  }
  c.result()
}

///|
fn atomvars(e : Value) -> Value raise {
  if symbolp(e) &&
    (
      symval(q_d_listconstvars).truthy() ||
      // Do not add constants or boolean values to list of vars.
      (!d_constantp(e).truthy() &&
      !(eq(e, t) || eq(e, q_d_true) || e is Nil || eq(e, q_d_false)))
    ) {
    add2lnc(e, symval(q_listofvars))
  } else if atom(e) {
    t
  } else if specrepp(e).truthy() {
    atomvars(specdisrep(e))
  } else if memq(q_array, car(e)).truthy() {
    myadd2lnc(e, symval(q_listofvars))
  } else {
    mapc(x => atomvars(x) |> ignore, margs(e))
  }
}

///|
fn myadd2lnc(item : Value, list_ : Value) -> Value raise {
  if memalike(item, list_).truthy() {
    Nil
  } else {
    nconc(list_, list1(item))
  }
}

///|
/// Bind a variable declared with DEFMVAR to its initial value. Initial values
/// that are not Maxima expressions, e.g. (2 3 5 7), are compared with EQUALP.
fn maybe_reset(
  key : Value,
  val : Value,
  actually_reset : Value,
  reset_verbose : Value,
) -> Value raise {
  let non_maxima = consp(val) && !consp(car(val))
  if boundp(key) &&
    (if non_maxima {
      !equalp(symval(key), val)
    } else {
      !alike1(symval(key), val).truthy()
    }) {
    if reset_verbose.truthy() {
      let displa_val = if non_maxima {
        cons(list1(q_mprogn), val)
      } else {
        val
      }
      displa(mk(q_mtext, [Str("reset: bind "), key, Str(" to "), displa_val]))
      |> ignore
    }
    nconc(actually_reset, list1(key)) |> ignore
    // Bind a copy: code like ADD2LNC changes some of these lists in place,
    // which must not change the stored initial value.
    with_special(q_munbindp, t, () => meval(
      mk(q_msetq, [key, mk(q_mquote, [copy_tree(val)])]),
    ))
  } else {
    Nil
  }
}

///|
fn d_reset_verbosely(l : Value) -> Value raise {
  reset_do_the_work(cdr(l), t)
}

///|
fn d_reset(l : Value) -> Value raise {
  reset_do_the_work(cdr(l), Nil)
}

///|
fn reset_do_the_work(args : Value, reset_verbose : Value) -> Value raise {
  let actually_reset = list1(list1(q_mlist))
  with_special(q_d_lispdisp, t, fn() {
    let table = symval(q_ear_variable_initial_values)
    if args.truthy() {
      for key in args.iter() {
        let (val, found_p) = gethash2(key, table)
        if found_p {
          maybe_reset(key, val, actually_reset, reset_verbose) |> ignore
        }
      }
    } else {
      maphash(
        (key, val) => maybe_reset(key, val, actually_reset, reset_verbose)
          |> ignore,
        table,
      )
    }
    actually_reset
  })
}
