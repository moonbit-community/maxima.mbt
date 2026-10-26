// Port of src/mrgmac.lisp: the MODE package used by db.lisp and compar.lisp
// (DEFMODE, SEL, STO, ...).
//
// These are compile-time macros: DEFMODE defines accessor macros C-<mode>,
// S-<mode>, A-<mode> from a structure description, and SEL / STO / PUSH+STO
// expand into nested accessor calls selected by the declared mode of a
// variable. The port has no Lisp compiler, so the code-building functions
// here return the Lisp code (as data) that the macros would produce; the
// call sites in db.lisp/compar.lisp are expanded by hand. The plain accessor
// macros C-MODE, S-MODE and A-MODE are implemented with their run-time
// meaning.

///|
let mrgmac__q_c_mode : Value = sym("c-mode")

///|
let mrgmac__q_c_atom : Value = sym("c-atom")

///|
let mrgmac__q_amp_optional : Value = sym("&optional")

///|
fn mrgmac__quote(x : Value) -> Value {
  list2(q_quote, x)
}

///|
/// `(list 'op ,bas)`
fn mrgmac__list_op(op : Value, bas : Value) -> Value {
  list3(q_list, mrgmac__quote(op), bas)
}

///|
/// `(setf (macro-function name) lambda-exp)`: the port records the expander
/// (a function, or the LAMBDA form built by DEFC/DEFS/DEFA) on the
/// MACRO-FUNCTION property.
fn define_macro(name : Value, lambda_exp : Value) -> Value raise {
  let lambda_exp = if symbolp(lambda_exp) {
    symbol_function(lambda_exp)
  } else {
    lambda_exp
  }
  putprop(name, lambda_exp, q_macro_function)
}

///|
fn define_mode(name : Value, desc : Value) -> Value raise {
  // NAME is a special variable (declare-top (special name bas selector)).
  with_special(q_name, name, fn() raise {
    let n = symbol_name(name)
    let c = sym("c-" + n)
    let s = sym("s-" + n)
    let a = sym("a-" + n)
    define_macro(c, defc(desc)) |> ignore
    define_macro(s, defs(desc)) |> ignore
    define_macro(a, defa(desc)) |> ignore
    putprop(name, c_mode(list3(c, s, a)), q_mode)
  })
}

///|
/// The lambda list and declaration of the generated expanders:
/// (lambda (x &optional env) (declare (ignore env)) . body)
fn mrgmac__expander(body : Value) -> Value {
  list_star(
    [
      q_lambda,
      list3(q_x, mrgmac__q_amp_optional, q_env),
      list2(q_declare, list2(q_ignore, q_env)),
      body,
    ],
  )
}

///|
fn defc(desc : Value) -> Value raise {
  with_special(q_bas, q_x, fn() raise {
    mrgmac__expander(list1(defc1(desc)))
  })
}

///|
fn defc1(desc : Value) -> Value raise {
  if atom(desc) {
    mrgmac__quote(desc)
  } else if eq(q_selector, car(desc)) {
    if cdddr(desc).truthy() {
      mrgmac__quote(fourth(desc))
    } else {
      set(q_bas, list2(q_cdr, symval(q_bas))) |> ignore
      list2(q_car, symval(q_bas))
    }
  } else if eq(q_atom, car(desc)) {
    list4(
      q_list,
      mrgmac__quote(mrgmac__q_c_atom),
      mrgmac__quote(mrgmac__quote(mapcar(x => second(x), cdr(desc)))),
      list3(q_cons, mrgmac__quote(q_list), list2(q_cdr, q_x)),
    )
  } else if eq(q_cons, car(desc)) {
    list4(
      q_list,
      mrgmac__quote(q_cons),
      defc1(second(desc)),
      defc1(third(desc)),
    )
  } else if eq(q_list, car(desc)) {
    let nl = Collector::new()
    for x in cdr(desc).iter() {
      nl.add(defc1(x))
    }
    list_star([q_list, mrgmac__quote(q_list), nl.result()])
  } else if eq(q_struct, car(desc)) {
    defc1(cons(q_list, cdr(desc)))
  } else {
    mrgmac__quote(desc)
  }
}

///|
fn defs(desc : Value) -> Value raise {
  mrgmac__expander(
    list1(cons(q_cond, nreverse(defs1(desc, list2(q_second, q_x), Nil)))),
  )
}

///|
fn mrgmac__note_selector(sel_ : Value, mode_ : Value) -> Unit raise {
  let name = symval(q_name)
  putprop(sel_, cons(cons(name, mode_), zl_get(sel_, q_modes)), q_modes)
  |> ignore
  putprop(name, cons(cons(sel_, mode_), zl_get(name, q_sels)), q_sels)
  |> ignore
  if symval(q_selector).truthy() {
    define_macro(sel_, q_selector) |> ignore
  }
}

///|
fn defs1(desc : Value, bas : Value, result : Value) -> Value raise {
  if atom(desc) {
    result
  } else if eq(q_selector, car(desc)) {
    mrgmac__note_selector(second(desc), third(desc))
    cons(
      list2(
        list3(q_eq, mrgmac__quote(second(desc)), list2(q_third, q_x)),
        bas,
      ),
      result,
    )
  } else if eq(q_atom, car(desc)) {
    for l in cdr(desc).iter() {
      mrgmac__note_selector(second(l), third(l))
    }
    cons(
      list2(
        list(
          [
            q_member,
            list2(q_third, q_x),
            mrgmac__quote(mapcar(x => second(x), cdr(desc))),
            kw("test"),
            list2(q_function, q_eq),
          ],
        ),
        list4(
          q_list,
          mrgmac__quote(q_zl_get),
          bas,
          list3(q_list, mrgmac__quote(q_quote), list2(q_third, q_x)),
        ),
      ),
      result,
    )
  } else if eq(q_cons, car(desc)) {
    let result = defs1(second(desc), mrgmac__list_op(q_car, bas), result)
    defs1(third(desc), mrgmac__list_op(q_cdr, bas), result)
  } else if eq(q_list, car(desc)) {
    let mut result = result
    let mut bas = bas
    for x in cdr(desc).iter() {
      result = defs1(x, mrgmac__list_op(q_car, bas), result)
      bas = mrgmac__list_op(q_cdr, bas)
    }
    result
  } else if eq(q_struct, car(desc)) {
    defs1(cons(q_list, cdr(desc)), bas, result)
  } else {
    result
  }
}

///|
fn defa(desc : Value) -> Value raise {
  mrgmac__expander(
    list1(cons(q_cond, nreverse(defa1(desc, list2(q_second, q_x), Nil, Nil)))),
  )
}

///|
fn defa1(desc : Value, bas : Value, cdr_ : Value, result : Value) -> Value raise {
  if atom(desc) {
    result
  } else if eq(q_selector, car(desc)) {
    let bas = if cdr_ is Nil {
      mrgmac__list_op(
        q_car,
        list4(q_list, mrgmac__quote(q_rplaca), third(bas), list2(q_fourth, q_x)),
      )
    } else {
      mrgmac__list_op(
        q_cdr,
        list4(q_list, mrgmac__quote(q_rplacd), third(bas), list2(q_fourth, q_x)),
      )
    }
    cons(
      list2(
        list3(q_eq, mrgmac__quote(second(desc)), list2(q_third, q_x)),
        bas,
      ),
      result,
    )
  } else if eq(q_atom, car(desc)) {
    list1(
      list2(
        t,
        list(
          [
            q_list,
            mrgmac__quote(q_cput),
            list2(q_second, q_x),
            list2(q_fourth, q_x),
            list3(q_list, mrgmac__quote(q_quote), list2(q_third, q_x)),
          ],
        ),
      ),
    )
  } else if eq(q_cons, car(desc)) {
    let result = defa1(second(desc), mrgmac__list_op(q_car, bas), Nil, result)
    defa1(third(desc), mrgmac__list_op(q_cdr, bas), t, result)
  } else if eq(q_list, car(desc)) {
    let mut result = result
    let mut bas = bas
    for x in cdr(desc).iter() {
      result = defa1(x, mrgmac__list_op(q_car, bas), Nil, result)
      bas = mrgmac__list_op(q_cdr, bas)
    }
    result
  } else if eq(q_struct, car(desc)) {
    defa1(cons(q_list, cdr(desc)), bas, cdr_, result)
  } else {
    result
  }
}

///|
fn mode(x : Value) -> Value raise {
  cdr(assoc_equal(x, symval(q_ear_mobjects)))
}

///|
fn modedeclare_internal(x : Value) -> Value raise {
  for l in x.iter() {
    for v in cdr(l).iter() {
      set(q_ear_mobjects, cons(cons(v, car(l)), symval(q_ear_mobjects)))
      |> ignore
    }
  }
  x
}

///|
/// `(modedeclare . l)`. (The Lisp macro expands into a call of the misspelt,
/// undefined MODECLARE-INTERNAL; the port calls MODEDECLARE-INTERNAL.)
fn modedeclare(l : Value) -> Value raise {
  modedeclare_internal(l)
}

///|
/// `(c-mode . l)` = `(list . l)`
fn c_mode(l : Value) -> Value raise {
  copy_list(l)
}

///|
/// `(s-mode obj sel)`: read the component selected by C, SEL or PUSH+STO.
fn s_mode(x : Value) -> Value raise {
  let obj = car(x)
  let s = cadr(x)
  if eq(s, sym("c")) {
    first(obj)
  } else if eq(s, q_sel) {
    second(obj)
  } else if eq(s, q_push_plussto) {
    third(obj)
  } else {
    Nil
  }
}

///|
/// `(a-mode obj sel val)`: store VAL in the component selected by C, SEL or
/// PUSH+STO.
fn a_mode(x : Value) -> Value raise {
  let obj = car(x)
  let s = cadr(x)
  let v = caddr(x)
  if eq(s, sym("c")) {
    rplaca(obj, v)
  } else if eq(s, q_sel) {
    rplaca(cdr(obj), v)
  } else if eq(s, q_push_plussto) {
    rplaca(cddr(obj), v)
  } else {
    Nil
  }
}

///|
/// `(defmode name nil desc . options)`. Defines the accessor macros of the
/// mode; the OPTIONS forms (Lisp code evaluated by the macro) are not
/// evaluated in the port. Returns `'name`.
fn defmode(x : Value) -> Value raise {
  let name = car(x)
  let desc = caddr(x)
  let options = cdddr(x)
  with_special(q_selector, memq(q_selector, options), fn() raise {
    define_mode(name, desc) |> ignore
  })
  mrgmac__quote(name)
}

///|
/// `(sel var . selectors)`: the expansion into nested S-<mode> accessors.
fn sel(x : Value) -> Value raise {
  let s = fsel(mode(car(x)), cdr(x))
  if s is Nil {
    return merror(Str("SEL: ~a ~a"), list2(car(x), cdr(x)))
  }
  let mut x = car(x)
  let mut s = s
  while cdr(s).truthy() {
    x = cons(second(zl_get(car(s), q_mode)), rplaca(s, x))
    s = cddr(s)
    rplacd(cddr(x), Nil) |> ignore
  }
  x
}

///|
/// This has a bug in it.
fn fsel(m : Value, sels : Value) -> Value raise {
  if sels is Nil {
    return list1(m)
  }
  if m is Nil {
    let mut l = zl_get(car(sels), q_modes)
    while l.truthy() {
      let m2 = fsel(cdar(l), cdr(sels))
      if m2.truthy() {
        return cons(caar(l), cons(car(sels), m2))
      }
      l = cdr(l)
    }
    return Nil
  }
  let dum = assq(car(sels), zl_get(m, q_sels))
  if dum.truthy() {
    let r = cons(m, cons(car(sels), fsel(cdr(dum), cdr(sels))))
    if r.truthy() {
      return r
    }
  }
  let mut l = zl_get(m, q_sels)
  while l.truthy() {
    let dum = fsel(cdar(l), sels)
    if dum.truthy() {
      return cons(m, cons(caar(l), dum))
    }
    l = cdr(l)
  }
  Nil
}

///|
/// The macro function installed for selector names.
fn selector(x : Value, env : Value) -> Value raise {
  ignore(env)
  if cddr(x) is Nil {
    list3(q_sel, second(x), car(x))
  } else {
    list3(q_push_plussto, list3(q_sel, second(x), car(x)), third(x))
  }
}

///|
/// `(push+sto . x)` = `(sto . x)` (returns the expansion).
fn push_plussto(x : Value) -> Value raise {
  cons(q_sto, x)
}

///|
/// `(sto place1 val1 place2 val2 ...)`: the expansion into SETQs and A-<mode>
/// accessor calls.
fn sto(x : Value) -> Value raise {
  let nl = Collector::new()
  let mut l = x
  while l.truthy() {
    let place = car(l)
    if atom(place) {
      nl.add(list3(q_setq, first(l), second(l)))
    } else {
      let s = if eq(q_sel, car(place)) {
        fsel(mode(cadr(place)), cddr(place))
      } else {
        Nil
      }
      if s.truthy() {
        let mut x = cadr(place)
        let mut l2 = cddr(s)
        while cdr(l2).truthy() {
          x = cons(second(zl_get(first(l2), q_mode)), rplaca(l2, x))
          rplacd(cddr(x), Nil) |> ignore
          l2 = cddr(l2)
        }
        nl.add(list4(third(zl_get(first(s), q_mode)), x, second(s), second(l)))
      } else {
        merror(Str("STO: ~a"), list1(place)) |> ignore
      }
    }
    l = cddr(l)
  }
  cons(q_progn, nl.result())
}

///|
fn init_mrgmac() -> Unit raise {
  putprop(
    q_mode,
    list3(mrgmac__q_c_mode, q_s_mode, q_a_mode),
    q_mode,
  )
  |> ignore
}
