// Port of src/grind.lisp: grind(), and the string-mode printers used by
// string() / stringout (STRGRIND, MSTRING).
//
// MSIZE returns a list whose first member is the number of characters in
// the printed representation of the rest of the list.

///|
/// Print the definition of a function, macro or array function named X, or
/// X itself, in 1-D form (shared by $grind and i-$grind).
fn grind__grind1(x0 : Value) -> Unit raise {
  let x = d_verbify(x0)
  let mut y = mget(x, q_mexpr)
  if y.truthy() {
    mgrind(
      list([list1(q_mdefine), cons(list1(x), cdadr(y)), caddr(y)]),
      Nil,
    )
    |> ignore
    return
  }
  y = mget(x, q_mmacro)
  if y.truthy() {
    mgrind(
      list([list1(q_mdefmacro), cons(list1(x), cdadr(y)), caddr(y)]),
      Nil,
    )
    |> ignore
    return
  }
  y = mget(x, q_aexpr)
  if y.truthy() {
    mgrind(
      list([list1(q_mdefine), cons(list2(x, q_array), cdadr(y)), caddr(y)]),
      Nil,
    )
    |> ignore
    return
  }
  mgrind(x, Nil) |> ignore
}

///|
fn d_grind(x : Value) -> Value raise {
  let x = cdr(x)
  with_special(q_d_lispdisp, t, () => {
    fresh_line() |> ignore
    if x is Nil {
      ()
    } else if cdr(x).truthy() {
      for xx in x.iter() {
        d_grind(list([list1(q_d_grind), xx])) |> ignore
      }
    } else {
      let x = strmeval(car(x))
      if symbolp(x) || (stringp(x) && symbolp(getopr(x))) {
        grind__grind1(x)
        write_char('$')
        write_char('\n')
      } else {
        mgrind(x, Nil) |> ignore
        write_char('$')
        write_char('\n')
      }
    }
    q_d_done
  })
}

///|
fn i__dolgrind(x : Value) -> Value raise {
  fresh_line() |> ignore
  let x = strmeval(x)
  if symbolp(x) {
    grind__grind1(x)
    write_char('$')
  } else {
    mgrind(x, Nil) |> ignore
    write_char('$')
  }
  q_d_done
}

///|
fn strgrind(x : Value) -> Value raise {
  with_specials([(q_ear_grind_charlist, Nil), (q_ear_chrps, Fix(0L))], () => {
    strprint(msize(x, Nil, Nil, q_mparen, q_mparen)) |> ignore
    nreverse(symval(q_ear_grind_charlist))
  })
}

///|
fn strprint(x : Value) -> Value raise {
  if atom(x) {
    return styo(x)
  }
  if mgrind__int(car(x)) < mgrind__chrct() {
    for l in cdr(x).iter() {
      strprint(l) |> ignore
    }
    return Nil
  }
  let mut i = mgrind__chrps()
  strprint(cadr(x)) |> ignore
  if cddr(x) is Nil {
    return Nil
  }
  if (atom(cadr(x)) || mgrind__int(caadr(x)) < mgrind__chrct()) &&
    (
      mgrind__chrct() > mgrind__linel() / 2 ||
      atom(caddr(x)) ||
      mgrind__int(caaddr(x)) < mgrind__chrct()
    ) {
    i = mgrind__chrps()
    strprint(caddr(x)) |> ignore
  } else {
    i = i + 1
    mgrind__set_chrps(0)
    sterpri() |> ignore
    styotbsp(int(i)) |> ignore
    strprint(caddr(x)) |> ignore
  }
  let mut l = cdddr(x)
  while l is Cons(_) {
    if atom(car(l)) || mgrind__int(caar(l)) < mgrind__chrct() {
      ()
    } else {
      mgrind__set_chrps(0)
      sterpri() |> ignore
      styotbsp(int(i)) |> ignore
    }
    strprint(car(l)) |> ignore
    l = cdr(l)
  }
  Nil
}

///|
fn styo(x : Value) -> Value raise {
  set(q_ear_grind_charlist, cons(x, symval(q_ear_grind_charlist))) |> ignore
  mgrind__set_chrps(mgrind__chrps() + 1)
  Nil
}

///|
fn sterpri() -> Value raise {
  set(q_ear_grind_charlist, cons(Char('\n'), symval(q_ear_grind_charlist)))
  |> ignore
  mgrind__set_chrps(0)
  Nil
}

///|
fn styotbsp(n : Value) -> Value raise {
  let mut n = to_int(n)
  mgrind__set_chrps(n)
  while n >= 1 {
    set(q_ear_grind_charlist, cons(Char(' '), symval(q_ear_grind_charlist)))
    |> ignore
    n -= 1
  }
  Nil
}

///|
fn mstring(x : Value) -> Value raise {
  nreverse(string1(msize(x, Nil, Nil, q_mparen, q_mparen), Nil))
}

///|
fn string1(x : Value, l : Value) -> Value raise {
  if atom(x) {
    return cons(x, l)
  }
  let mut x = cdr(x)
  let mut l = l
  while x is Cons(_) {
    l = string1(car(x), l)
    x = cdr(x)
  }
  l
}

///|
fn init_grind() -> Unit raise {
  putprop(q_mfunction, int(190), q_lbp) |> ignore
  putprop(q_mfunction, int(190), q_rbp) |> ignore
}
