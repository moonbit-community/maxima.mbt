// Port of src/sublis.lisp: SUBLIS([sym1=form1,sym2=form2,...],expression)
//
// Changes all occurrences of sym1 in expression to form1, all occurrences of
// sym2 to form2, etc. The replacement is done in parallel, so having
// occurrences of sym1 in form2, etc. will have the `desired'
// (non-interfering) effect.

///|
fn d_sublis(substitutions : Value, form : Value) -> Value raise {
  let mut substitutions = substitutions
  if d_listp(substitutions).truthy() {
    let mut nl : Value = Nil
    for temp in cdr(substitutions).iter() {
      let is_eqn = !atom(temp) && !atom(car(temp)) && eq(caar(temp), q_mequal)
      if is_eqn && symbolp(cadr(temp)) {
        nl = cons(cons(cadr(temp), caddr(temp)), nl)
      } else {
        // (the equation header has been popped when only the symbol test
        // failed)
        merror(
          Str(
            "sublis: expected an equation with left-hand side a symbol; found: ~M",
          ),
          list1(if is_eqn { cdr(temp) } else { temp }),
        )
        |> ignore
      }
    }
    substitutions = nl
  } else {
    merror(
      Str("sublis: first argument must a list; found: ~M"),
      list1(substitutions),
    )
    |> ignore
  }
  msublis(substitutions, form)
}

///|
fn msublis(s : Value, y : Value) -> Value raise {
  with_specials(
    [(q_s, s), (q_ear_msublis_marker, make_symbol("*msublis-marker*"))],
    fn() raise {
      msublis_setup() |> ignore
      defer sublis__unsetup_quiet()
      msublis_subst(y, t)
    },
  )
}

///|
fn msublis_setup() -> Value raise {
  let marker = symval(q_ear_msublis_marker)
  let mut x = symval(q_s)
  while x.truthy() {
    let temp = caar(x)
    if !symbolp(temp) {
      merror(
        Str("sublis: left-hand side of equation must be a symbol; found: ~M"),
        list1(temp),
      )
      |> ignore
    }
    set_symbol_plist(temp, list_star([marker, cdar(x), symbol_plist(temp)]))
    |> ignore
    let temp1 = getopr(temp)
    if !eq(temp, temp1) {
      set_symbol_plist(
        temp1,
        list_star([marker, cdar(x), symbol_plist(temp1)]),
      )
      |> ignore
      // Remember extra cleanup
      set(q_s, cons(ncons(temp1), symval(q_s))) |> ignore
    }
    x = cdr(x)
  }
  Nil
}

///|
fn msublis_unsetup() -> Value raise {
  let marker = symval(q_ear_msublis_marker)
  for x in symval(q_s).iter() {
    remprop(car(x), marker) |> ignore
  }
  Nil
}

///|
fn sublis__array_flag(form : Value) -> Value {
  if memq(q_array, car(form)).truthy() {
    list1(q_array)
  } else {
    Nil
  }
}

///|
fn sublis__unsetup_quiet() -> Unit {
  let _ = msublis_unsetup() catch { _ => Nil }

}

///|
fn msublis_subst(form : Value, flag : Value) -> Value raise {
  if atom(form) {
    if form is Nil && flag is Nil {
      Nil // preserve trailing NILs
    } else if symbolp(form) {
      let pl = symbol_plist(form)
      if eq(car(pl), symval(q_ear_msublis_marker)) {
        cadr(pl)
      } else {
        form
      }
    } else {
      form
    }
  } else if flag.truthy() {
    if d_ratp(form).truthy() {
      let disrep = d_ratdisrep(form)
      let sub = msublis_subst(disrep, t)
      if eq(disrep, sub) {
        form
      } else {
        d_rat(sub, Nil)
      }
    } else if atom(car(form)) {
      merror(Str("sublis: malformed expression (atomic car)."), Nil)
    } else {
      let cdr_value = msublis_subst(cdr(form), Nil)
      let caar_value = msublis_subst(caar(form), t)
      if eq(cdr_value, cdr(form)) && eq(caar(form), caar_value) {
        form
      } else if symval(q_d_sublis_apply_lambda).truthy() &&
        eq(caar(form), q_mqapply) &&
        eq(caar_value, q_mqapply) &&
        atom(cadr(form)) &&
        !atom(car(cdr_value)) &&
        eq(caar(car(cdr_value)), q_lambda) {
        cons(cons(car(cdr_value), sublis__array_flag(form)), cdr(cdr_value))
      } else if !atom(caar_value) &&
        (
          !(eq(car(caar_value), q_lambda) || eq(caar(caar_value), q_lambda)) ||
          symval(q_d_sublis_apply_lambda) is Nil
        ) {
        list_star(
          [cons(q_mqapply, sublis__array_flag(form)), caar_value, cdr_value],
        )
      } else {
        cons(cons(caar_value, sublis__array_flag(form)), cdr_value)
      }
    }
  } else {
    let car_value = msublis_subst(car(form), t)
    let cdr_value = msublis_subst(cdr(form), Nil)
    if eq(car(form), car_value) && eq(cdr(form), cdr_value) {
      form
    } else {
      cons(car_value, cdr_value)
    }
  }
}
