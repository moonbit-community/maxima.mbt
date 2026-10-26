// Port of share/stats/inference_result.lisp (Mario Rodriguez Riotorto,
// 2006-2012): objects returned by statistical inference procedures, with
// their 2D display (adapted from d-matrix, matout, colout and dim-$matrix of
// the old displa.lisp) and TeX output.

///|
fn share_inference_result__i(s : Value) -> Int raise {
  to_int(symval(s))
}

///|
fn share_inference_result__set(s : Value, n : Int) -> Unit {
  set(s, int(n)) |> ignore
}

///|
fn share_inference_result__max(a : Int, b : Int) -> Int {
  if a > b {
    a
  } else {
    b
  }
}

///|
/// Constructs the 'inference_result' object, with
///    title: string with the name of the inference procedure
///    val: Maxima list, the elements of which are lists of
///         the form: ["Value's name", value]
///    selection: Maxima list numbering the values to be displayed
fn d_inference_result(title : Value, val : Value, selection : Value) -> Value raise {
  list([list1(q_d_inference_result), title, val, selection])
}

///|
/// Left and right characters of the display.
fn d__matrixz(linear_q : Value, direction : Value, h : Value, d : Value) -> Value raise {
  d__vbar(
    linear_q,
    h,
    d,
    char_body=if eq(direction, q_right) {
      Char(' ')
    } else {
      Char('|')
    },
  )
}

///|
fn matoutz(dmstr : Value, cstr : Value, rstr : Value, result : Value) -> Value raise {
  let mut result = cons(
    list([q_d__matrixz, q_left, symval(q_height), symval(q_depth)]),
    result,
  )
  result = cons(Char(' '), result)
  let height = share_inference_result__i(q_height)
  let mut d = dmstr
  let mut c = cstr
  while d is Cons(_) {
    let mut w = 0
    let cc = to_int(car(c))
    let mut dd = car(d)
    let mut r = rstr
    while dd is Cons(_) {
      rplaca(cddar(dd), int(height - to_int(car(r)))) |> ignore
      let ew = to_int(caar(dd))
      rplaca(cdar(dd), int((cc - ew) / 2 - w)) |> ignore
      w = (cc + ew) / 2
      rplaca(dd, cdar(dd)) |> ignore
      dd = cdr(dd)
      r = cdr(r)
    }
    result = cons(list([int(2 + (cc - w)), Fix(0L)]), nreconc(car(d), result))
    d = cdr(d)
    c = cdr(c)
  }
  share_inference_result__set(q_width, 2 + share_inference_result__i(q_width))
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  rplaca(car(result), num_sub(caar(result), Fix(1L))) |> ignore
  result = cons(
    list([q_d__matrixz, q_right, symval(q_height), symval(q_depth)]),
    result,
  )
  result
}

///|
fn coloutz(dmstr : Value, cstr : Value, result : Value) -> Value raise {
  let mut result = result
  share_inference_result__set(q_width, 0)
  share_inference_result__set(q_height, 1)
  share_inference_result__set(q_depth, 0)
  let mut r = dmstr
  let mut c = cstr
  let mut col = 1
  while r is Cons(_) {
    let mut w = 0
    let mut h = -1
    result = push_string(Str(" Col "), result)
    result = nreconc(exploden(int(col)), result)
    result = push_string(Str(" = "), result)
    share_inference_result__set(
      q_width,
      8 + to_int(flatc(int(col))) + share_inference_result__i(q_width),
    )
    let cc = to_int(car(c))
    let mut rr = car(r)
    while rr is Cons(_) {
      h = 1 + h + to_int(cadar(rr)) + to_int(car(cddar(rr)))
      rplaca(cddar(rr), int(h - to_int(cadar(rr)))) |> ignore
      let ew = to_int(caar(rr))
      rplaca(cdar(rr), int((cc - ew) / 2 - w)) |> ignore
      w = (cc + ew) / 2
      rplaca(rr, cdar(rr)) |> ignore
      rr = cdr(rr)
    }
    let d = h / 2
    h = h - d
    result = cons(list([q_d__matrixz, q_left, int(h), int(d)]), result)
    result = cons(Char(' '), result)
    result = cons(list_star([Fix(0L), int(-d), nreverse(car(r))]), result)
    result = cons(list([int(1 + (cc - w)), Fix(0L)]), result)
    result = cons(list([q_d__matrixz, q_right, int(h), int(d)]), result)
    share_inference_result__set(
      q_width,
      4 + cc + share_inference_result__i(q_width),
    )
    share_inference_result__set(
      q_height,
      share_inference_result__max(h, share_inference_result__i(q_height)),
    )
    share_inference_result__set(
      q_depth,
      share_inference_result__max(d, share_inference_result__i(q_depth)),
    )
    update_heights(int(h), int(d)) |> ignore
    checkbreak(result, symval(q_width)) |> ignore
    r = cdr(r)
    c = cdr(c)
    col += 1
  }
  result
}

///|
fn dim__dolinference_result(form : Value, result : Value) -> Value raise {
  let not_list_row = () => {
    for row in cdr(form).iter() {
      if !d_listp(row).truthy() {
        return true
      }
    }
    false
  }
  if cdr(form) is Nil ||
    !memq(q_simp, cdar(form)).truthy() ||
    memalike(list1(list2(q_mlist, q_simp)), cdr(form)).truthy() ||
    not_list_row() {
    return dimension_function(form, result)
  }
  let mut dmstr : Value = Nil
  let mut rstr : Value = Nil
  let mut cstr : Value = Nil
  let mut consp_ = false
  for _l in cdadr(form).iter() {
    dmstr = cons(Nil, dmstr)
    cstr = cons(Fix(0L), cstr)
  }
  let mut r = cdr(form)
  let mut h1 = 0
  let mut d1 = 0
  while true {
    if consp_ || r is Nil {
      let mut width = 0
      for cs in cstr.iter() {
        width = 2 + to_int(cs) + width
      }
      share_inference_result__set(q_width, width)
      h1 = h1 + d1 - 1
      let depth = h1 / 2
      share_inference_result__set(q_depth, depth)
      share_inference_result__set(q_height, h1 - depth)
      break
    }
    let mut c = cdar(r)
    let mut nc = dmstr
    let mut cs = cstr
    let mut h2 = 0
    let mut d2 = 0
    while true {
      if c is Nil {
        d1 = d1 + h1 + h2
        h1 = 1 + d2
        break
      }
      let dummy = dimension(car(c), Nil, q_mparen, q_mparen, Nil, Fix(0L))
      h2 = share_inference_result__max(h2, share_inference_result__i(q_height))
      d2 = share_inference_result__max(d2, share_inference_result__i(q_depth))
      if !checkfit(int(14 + share_inference_result__i(q_width))).truthy() {
        consp_ = true
        break
      } else {
        rplaca(
          nc,
          cons(
            list_star([
              symval(q_width),
              symval(q_height),
              symval(q_depth),
              dummy,
            ]),
            car(nc),
          ),
        )
        |> ignore
        rplaca(
          cs,
          int(
            share_inference_result__max(
              share_inference_result__i(q_width),
              to_int(car(cs)),
            ),
          ),
        )
        |> ignore
      }
      c = cdr(c)
      nc = cdr(nc)
      cs = cdr(cs)
    }
    rstr = cons(int(d1), rstr)
    r = cdr(r)
  }
  match symval(q_linearray) {
    Vec(a) =>
      if share_inference_result__i(q_height) +
        share_inference_result__i(q_depth) >
        a.data.length() {
        consp_ = true
      }
    _ => ()
  }
  if !consp_ &&
    checkfit(int(2 + share_inference_result__i(q_width))).truthy() {
    matoutz(dmstr, cstr, rstr, result)
  } else if !consp_ && share_inference_result__i(q_level) <= 2 {
    coloutz(dmstr, cstr, result)
  } else {
    dimension_function(form, result)
  }
}

///|
/// Sets display properties: the form is rearranged as
///   (($inference_result simp)
///      ((mlist simp) title)
///      ((mlist simp) ((mequal simp) value_name1 value1))
///      ...)
/// with the selected items only, and displayed as a one-column matrix.
fn dimension_inference(form : Value, result : Value) -> Value raise {
  let title = cadr(form)
  let outputitems = reverse(cdr(cadddr(form)))
  let mut output : Value = Nil
  for k in outputitems.iter() {
    let aux = rest(nth(to_int(k), caddr(form)))
    output = cons(
      list([
        list2(q_mlist, q_simp),
        list([list2(q_mequal, q_simp), car(aux), cadr(aux)]),
      ]),
      output,
    )
  }
  output = append(
    list([list2(q_d_inference_result, q_simp), list([list2(q_mlist, q_simp), title])]),
    output,
  )
  dim__dolinference_result(output, result)
}

///|
/// Format TeX output.
/// inference_result looks like
/// ((inference_result) string ((mlist) ((mlist)..) ((mlist)..)..))
fn tex_inference_result(x : Value, l : Value, r : Value) -> Value raise {
  append(
    l,
    append(
      list1(Str("\\left | \\matrix{")),
      append(
        list([Str("\\hbox{"), cadr(x), Str("} \\cr \\matrix{")]),
        append(
          mapcan(
            y => tex_list(
              list1(list([list1(q_mequal), cadr(y), caddr(y)])),
              Nil,
              list1(Str("\\cr ")),
              Str("&"),
            ),
            cdar(butlast(cddr(x))),
          ),
          append(list1(Str("}} \\right .")), r),
        ),
      ),
    ),
  )
}

///|
/// Returns true or false, depending on whether 'obj' is an
/// 'inference_result' object or not.
fn d_inferencep(obj : Value) -> Value raise {
  if listp(obj) {
    lbool(equalp(car(obj), list2(q_d_inference_result, q_simp)))
  } else {
    Nil
  }
}

///|
/// Returns a Maxima list with the names of the items stored in the
/// 'inference_result' object.
fn d_items_inference(obj : Value) -> Value raise {
  let items = cdr(caddr(obj))
  cons(list1(q_mlist), mapcar(x => second(x), items))
}

///|
/// Returns the n-th value of the 'inference_result' object, or the list of
/// values associated to the indices in n, if n is a Maxima list.
fn d_take_inference(n : Value, obj : Value) -> Value raise {
  if d_inferencep(obj).truthy() {
    if d_integerp(n).truthy() && num_le(n, int(length(cdr(caddr(obj))))) {
      caddr(nth(to_int(num_sub(n, Fix(1L))), cdr(caddr(obj))))
    } else if d_listp(n).truthy() {
      let mut values : Value = Nil
      let items = reverse(rest(n))
      for k in items.iter() {
        values = cons(d_take_inference(k, obj), values)
      }
      cons(list1(q_mlist), values)
    } else {
      let m = position(n, mapcar(x => second(x), cdr(caddr(obj))))
      if m < 0 {
        merr("Wrong label in 'take_inference' call", [])
      } else {
        caddr(nth(m, cdr(caddr(obj))))
      }
    }
  } else {
    merr("Wrong object in 'take_inference' call", [])
  }
}

///|
/// Returns the title of the 'inference_result' object.
fn d_title_inference(obj : Value) -> Value raise {
  if d_inferencep(obj).truthy() {
    second(obj)
  } else {
    merr("Wrong object in 'title_inference' call", [])
  }
}

///|
fn init_share_inference_result() -> Unit raise {
  displa_def(q_d_inference_result, q_dim__dolinference_result, Nil) |> ignore
  // Sets display properties (overrides the previous one)
  displa_def(q_d_inference_result, q_dimension_inference, Nil) |> ignore
  // Format TeX output
  putprop(q_d_inference_result, q_tex_inference_result, q_tex) |> ignore
}
