// Port of src/askp.lisp: $askinteger and the ASK-* helpers.
//
// $ASKINTEGER returns $yes, $no or $unknown. If LIMITP is non-NIL the facts
// collected are consed onto *INTEGER-INFO*.

///|
fn d_askinteger(x : Value, mode? : Value = q_d_integer) -> Value raise {
  if eq(mode, q_d_even) || eq(mode, q_d_odd) || eq(mode, q_d_integer) {
    ask_integer(x, mode)
  } else {
    improper_arg_err(mode, q_d_askinteger)
  }
}

///|
fn ask_integer(x : Value, even_odd : Value) -> Value raise {
  let x = sratsimp(
    sublis(list2(cons(q_z_star_star, Fix(0L)), cons(q_ear_z, Fix(0L))), x),
  )
  if ratnump(x).truthy() {
    q_d_no
  } else if eq(even_odd, q_d_integer) {
    ask_integerp(x)
  } else {
    ask_evod(x, even_odd)
  }
}

///|
fn ask_evod(x : Value, even_odd : Value) -> Value raise {
  let x = if mtimesp(x).truthy() && equal(cadr(x), Fix(-1L)) {
    muln(cddr(x), t)
  } else {
    x
  }
  let evod_ans = evod(x)
  let is_integer = maxima_integerp(x)
  if equal(evod_ans, even_odd) {
    q_d_yes
  } else if d_numberp(x).truthy() && !is_integer.truthy() {
    q_d_no
  } else if is_integer.truthy() && evod_ans.truthy() {
    q_d_no
  } else {
    let evod_ans = ask_prop(
      x,
      if eq(even_odd, q_d_even) {
        q_even
      } else {
        q_odd
      },
      q_number,
    )
    if eq(evod_ans, q_d_yes) {
      ask_declare(x, even_odd) |> ignore
      q_d_yes
    } else if eq(evod_ans, q_d_no) {
      if is_integer.truthy() {
        if eq(even_odd, q_d_even) {
          ask_declare(x, q_d_odd) |> ignore
        } else {
          ask_declare(x, q_d_even) |> ignore
        }
      }
      q_d_no
    } else {
      q_d_unknown
    }
  }
}

///|
fn ask_integerp(x : Value) -> Value raise {
  let mut x = x
  if mplusp(x).truthy() && integerp(cadr(x)) {
    x = addn(cddr(x), t)
  }
  if mtimesp(x).truthy() && equal(cadr(x), Fix(-1L)) {
    x = muln(cddr(x), t)
  }
  if maxima_integerp(x).truthy() || memalike(x, symval(q_integerl)).truthy() {
    q_d_yes
  } else if d_numberp(x).truthy() ||
    nonintegerp(x).truthy() ||
    memalike(x, symval(q_nonintegerl)).truthy() {
    q_d_no
  } else {
    let integer_ans = ask_prop(x, q_integer, Nil)
    if eq(integer_ans, q_d_yes) {
      ask_declare(x, q_d_integer) |> ignore
      q_d_yes
    } else if eq(integer_ans, q_d_no) {
      ask_declare(x, q_d_noninteger) |> ignore
      q_d_no
    } else {
      q_d_unknown
    }
  }
}

///|
fn ask_declare(x : Value, property : Value) -> Value raise {
  if atom(x) {
    meval(mk(q_d_declare, [x, property])) |> ignore
    if symval(q_limitp).truthy() {
      set(
        q_ear_integer_info,
        cons(mk(q_d_kind, [x, property]), symval(q_ear_integer_info)),
      )
    } else {
      Nil
    }
  } else if symval(q_limitp).truthy() && eq(property, q_d_integer) {
    set(q_integerl, cons(x, symval(q_integerl)))
  } else if symval(q_limitp).truthy() && eq(property, q_d_noninteger) {
    set(q_nonintegerl, cons(x, symval(q_nonintegerl)))
  } else {
    Nil
  }
}

///|
/// Asks the user a question about the property of an object.
/// Returns only $yes, $no or $unknown.
fn ask_prop(object_ : Value, property : Value, fun_or_number : Value) -> Value raise {
  match askp__ask_prop_cell.val {
    Some(f) => f(object_, property, fun_or_number)
    None => askp__ask_prop_base(object_, property, fun_or_number)
  }
}

///|
/// The function cell of ASK-PROP. Share packages (share/contrib/noninteractive/asksign1.lisp) redefine
/// it at load time, as CL Maxima does with DEFUN; callers in the port reach
/// the current definition through this cell (None: the standard one).
let askp__ask_prop_cell : Ref[((Value, Value, Value) -> Value raise)?] = Ref(None)

///|
fn askp__ask_prop_base(
  object_ : Value,
  property : Value,
  fun_or_number : Value,
) -> Value raise {
  let fon = if fun_or_number.truthy() {
    list2(Str(" "), fun_or_number)
  } else {
    Nil
  }
  let c0 = char_downcase(char_at(symbol_name(property), 0))
  let article = if c0 == 'a' || c0 == 'e' || c0 == 'i' || c0 == 'o' || c0 == 'u' {
    " an "
  } else {
    " a "
  }
  while true {
    let answer = retrieve(
      cons(
        list1(q_mtext),
        append(
          list([Str("Is "), object_, Str(article), property]),
          append(fon, list1(Str("?"))),
        ),
      ),
      if symval(q_d_ask_hide_prompt).truthy() {
        q_noprint
      } else {
        Nil
      },
    )
    if eq(answer, q_d_yes) || eq(answer, q_d__cy_) || eq(answer, q_d_y) {
      return q_d_yes
    } else if eq(answer, q_d__cn_) || eq(answer, q_d_n) || eq(answer, q_d_no) {
      return q_d_no
    } else if eq(answer, q_d_unknown) || eq(answer, q_d_uk) {
      return q_d_unknown
    } else {
      mtell(
        list1(
          Str("~%Acceptable answers are: yes, y, Y, no, n, N, unknown, uk~%"),
        ),
      )
      |> ignore
    }
  }
  Nil
}
