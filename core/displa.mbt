// Port of src/displa.lisp: Maxima's 2-D display.
//
// DIMENSION builds a "dimension string" (in reverse order) for a form while
// maintaining the special variables WIDTH, HEIGHT and DEPTH; OUTPUT then
// draws it into LINEARRAY and prints it line by line.
//
// <dimension string> ::= () | (<string element> . <dimension string>)
// <string element> ::= character |
//                      (<column-relative> <row-relative> . <dimension string>) |
//                      (<drawing function> . args)
//
// All the state (width, height, depth, maxht, maxdp, level, size, lop, rop,
// break, right, bkpt*, lines, oldrow, oldcol, mratp) lives in special
// variables, exactly as in the Lisp code.

///|
fn displa__i(s : Value) -> Int raise {
  to_int(symval(s))
}

///|
fn displa__set(s : Value, n : Int) -> Unit {
  set(s, int(n)) |> ignore
}

///|
fn displa__max(a : Int, b : Int) -> Int {
  if a > b {
    a
  } else {
    b
  }
}

///|
fn displa__linel() -> Int raise {
  to_int(symval(q_d_linel))
}

///|
/// `(push-string "str" result)`: push the characters of S onto RESULT
/// (the dimension string is kept in reverse order).
fn displa__push(s : String, result : Value) -> Value {
  let mut r = result
  for c in s {
    r = cons(Char(c), r)
  }
  r
}

///|
/// The characters of S as a fresh list (`(exploden "str")`).
fn displa__chars(s : String) -> Value {
  let c = Collector::new()
  for ch in s {
    c.add(Char(ch))
  }
  c.result()
}

///|
/// The first character of a Maxima string option such as $absboxchar.
fn displa__first_char(v : Value) -> Value {
  match v {
    Str(s) => {
      for c in s {
        return Char(c)
      }
      Nil
    }
    Char(_) => v
    _ => Nil
  }
}

///|
fn displa__unicode() -> Bool {
  symval(q_d_display2d_unicode).truthy()
}

///|
fn displa__checkfit(w : Int) -> Bool raise {
  let brk = symval(q_break)
  if brk is Nil {
    true
  } else {
    w + to_int(brk) + displa__i(q_right) + 1 - displa__i(q_bkptwd) <=
    displa__linel()
  }
}

///|
/// The keys of `defun-prop`-less operators that are displayed specially.
fn maxima_display(form : Value, stream? : Value) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_output)
  }
  with_special(standard_output, stream, () => displa(form))
}

///|
/// Port: share packages redefine DISPLA when loaded
/// (share/contrib/maximaMathML/mathmldisplay.lisp); in CL every caller then
/// reaches the new definition through the function cell. Such a package
/// installs its definition here.
let displa__redefined : Ref[((Value) -> Value raise)?] = Ref(None)

///|
fn displa(form : Value) -> Value raise {
  if displa__redefined.val is Some(f) {
    return f(form)
  }
  if symval(q_d_ttyoff).truthy() {
    return Nil
  }
  if symval(q_d_display2d).truthy() {
    let alt = symval(q_ear_alt_display2d)
    if alt.truthy() {
      return apply(alt, list1(form))
    }
    let mratp = checkrat(form)
    with_specials(
      [
        (q_displayp, t),
        (q_mratp, mratp),
        (q_maxht, Fix(1L)),
        (q_maxdp, Fix(0L)),
        (q_width, Fix(0L)),
        (q_height, Fix(0L)),
        (q_depth, Fix(0L)),
        (q_level, Fix(0L)),
        (q_size, Fix(2L)),
        (q_break, Fix(0L)),
        (q_right, Fix(0L)),
        (q_lines, Fix(1L)),
        (q_bkpt, Nil),
        (q_bkptwd, Fix(0L)),
        (q_bkptht, Fix(1L)),
        (q_bkptdp, Fix(0L)),
        (q_bkptout, Fix(0L)),
        (q_bkptlevel, Fix(0L)),
        (q_in_p, Nil),
      ],
      () => {
        // make sure the linearray gets cleared out.
        defer displa__clear_linearray()
        let form = dimension(form, Nil, q_mparen, q_mparen, Fix(0L), Fix(0L))
        checkbreak(form, symval(q_width)) |> ignore
        output(
          form,
          if !symval(q_d_leftjust).truthy() && displa__i(q_lines) == 2 {
            int(
              displa__linel() -
              (displa__i(q_width) - displa__i(q_bkptout)),
            )
          } else {
            Fix(0L)
          },
        )
      },
    )
  } else {
    let alt = symval(q_ear_alt_display1d)
    if alt.truthy() {
      apply(alt, list1(form))
    } else {
      linear_displa(form)
    }
  }
}

///|
fn displa__clear_linearray() -> Unit {
  match symval(q_linearray) {
    Vec(a) => for i = 0; i < a.data.length(); i = i + 1 {
      a.data[i] = Nil
    }
    _ => ()
  }
}

///|
fn d_with_default_2d_display(expr : Value) -> Value raise {
  with_specials(
    [(q_ear_alt_display2d, Nil), (q_d_display2d, t)],
    () => meval(cons(list1(q_mprog), cdr(expr))),
  )
}

///|
/// Display text linearly.
fn linear_displa(form : Value) -> Value raise {
  fresh_line(stream=symval(standard_output)) |> ignore
  mgrind(form, symval(standard_output)) |> ignore
  mterpri()
}

///|
fn dimension(
  form : Value,
  result : Value,
  lop : Value,
  rop : Value,
  w : Value,
  right : Value,
) -> Value raise {
  let level = displa__i(q_level) + 1
  let brk = symval(q_break)
  let brk = if w.truthy() && brk.truthy() { num_add(w, brk) } else { Nil }
  with_specials(
    [
      (q_lop, lop),
      (q_rop, rop),
      (q_right, right),
      (q_level, int(level)),
      (q_break, brk),
    ],
    () => {
      let mut form = nformat_check(form)
      if atom(form) {
        return dimension_atom(form, result)
      }
      if atom(car(form)) {
        form = cons(list1(q_mprogn), form)
      }
      let op = caar(form)
      if num_le(lbp(op), rbp(lop)) || num_ge(lbp(rop), rbp(op)) {
        dimension_paren(form, result)
      } else if memq(q_array, car(form)).truthy() {
        dimension_array(form, result)
      } else if safe_get(op, q_dimension).truthy() {
        funcall(get(op, q_dimension), [form, result])
      } else {
        dimension_function(form, result)
      }
    },
  )
}

///|
fn dimension_atom(form : Value, result : Value) -> Value raise {
  if symbolp(form) && get(form, symval(q_atom_context)).truthy() {
    funcall(get(form, symval(q_atom_context)), [form, result])
  } else if stringp(form) {
    dimension_string(makestring(form), result)
  } else if memq(marray_type(form), list([q_array, q_hash_table, q_d_functional])).truthy() {
    dimension_array_object(form, result)
  } else {
    dimension_string(makestring(form), result)
  }
}

///|
fn dimension_string(dummy : Value, result : Value) -> Value raise {
  displa__set(q_width, 0)
  displa__set(q_height, 1)
  displa__set(q_depth, 0)
  let mut crp = false
  let mut width = 0
  for c in dummy.iter() {
    width += 1
    if c is Char('\n') {
      crp = true
    }
  }
  displa__set(q_width, width)
  if (displa__checkfit(width) && !crp) || symval(q_break) is Nil {
    return nreconc(dummy, result)
  }
  let mut width = 0
  displa__set(q_width, 0)
  let mut result = result
  let mut l = dummy
  let mut w = displa__linel() -
    (displa__i(q_break) - displa__i(q_bkptout))
  while true {
    if l is Nil {
      displa__set(q_width, width)
      checkbreak(result, int(width)) |> ignore
      return result
    }
    let d = l
    l = cdr(l)
    if car(d) is Char('\n') {
      displa__set(q_width, width)
      if result.truthy() {
        forcebreak(result, int(width)) |> ignore
      } else {
        forcebreak(list1(Char(' ')), int(width)) |> ignore
      }
      result = Nil
      w = displa__linel() + width
    } else {
      width += 1
      if w == width && l.truthy() {
        displa__set(q_width, width)
        forcebreak(cons(Char('\\'), result), int(width)) |> ignore
        result = Nil
        w = displa__linel() + width
        width += 1
      }
      result = rplacd(d, result)
    }
  }
  result
}

///|
fn dimension_paren(form : Value, result : Value) -> Value raise {
  let result = cons(
    Char(')'),
    dimension(
      form,
      cons(Char('('), result),
      q_mparen,
      q_mparen,
      Fix(1L),
      int(displa__i(q_right) + 1),
    ),
  )
  displa__set(q_width, displa__i(q_width) + 2)
  result
}

///|
fn dimension_array(x : Value, result : Value) -> Value raise {
  let mut x = x
  let mut result = result
  let mut w_base = 0
  let dummy = if eq(caar(x), q_mqapply) {
    let d = cadr(x)
    x = cdr(x)
    d
  } else {
    caar(x)
  }
  if !symval(q_d_noundisp).truthy() || !symbolp(caar(x)) {
    ()
  } else if get(caar(x), q_verb).truthy() && get(caar(x), q_alias).truthy() {
    result = displa__push("''", result)
    w_base = 2
  } else if get(caar(x), q_noun).truthy() &&
    !memq(caar(x), cdr(symval(q_d_aliases))).truthy() &&
    !get(caar(x), q_reversealias).truthy() {
    result = cons(Char('\''), result)
    w_base = 1
  }
  let bas = if !atom(dummy) && memq(q_array, car(dummy)).truthy() {
    with_specials([(q_break, Nil), (q_right, Fix(0L))], () => dimension_paren(
      dummy, Nil,
    ))
  } else {
    with_special(q_atom_context, q_dimension_array, () => dimension(
      dummy,
      Nil,
      symval(q_lop),
      q_mfunction,
      Nil,
      Fix(0L),
    ))
  }
  w_base = w_base + displa__i(q_width)
  let h_base = displa__i(q_height)
  let d_base = displa__i(q_depth)
  let (
    w00, w01, w10, w11, h00, h01, h10, h11, d00, d01, d10, d11, pre_sub_out, pre_sup_out,
    post_sub_out, post_sup_out
  ) = dimension_indices(dummy, cdr(x))
  let w00 = to_int(w00)
  let w01 = to_int(w01)
  let w10 = to_int(w10)
  let w11 = to_int(w11)
  let h00 = to_int(h00)
  let h01 = to_int(h01)
  let h10 = to_int(h10)
  let h11 = to_int(h11)
  let d00 = to_int(d00)
  let d01 = to_int(d01)
  let d10 = to_int(d10)
  let d11 = to_int(d11)
  let width = w_base + displa__max(w00, w01) + displa__max(w10, w11)
  displa__set(q_width, width)
  if !displa__checkfit(width) {
    return dimension_function(
      cons(list1(q_subscript), cons(dummy, cdr(x))),
      result,
    )
  } else if atom(car(bas)) && car(bas) is Char(' ') {
    result = cons(
      cons(Fix(0L), cons(int(-h_base), symval(q_post_subscripts))),
      bas,
    )
    displa__set(q_depth, displa__max(h_base + d_base, displa__i(q_depth)))
  } else {
    let items = [
      append(list([int(-w10), int(h_base + d11)]), post_sup_out),
      append(list([Fix(0L), int(-h10)]), post_sub_out),
      append(list([Fix(0L), Fix(0L)]), bas),
      append(
        list([int(if w00 > 0 { -w01 } else { 0 }), int(h_base + d01)]),
        pre_sup_out,
      ),
      append(
        list([int(if w01 > w00 { w01 - w00 } else { 0 }), int(-h00)]),
        pre_sub_out,
      ),
    ]
    let kept = items.filter(l => length(l) != 2)
    result = append_n([
      if w11 > 0 && w10 > w11 {
        list1(list([int(w10 - w11), Fix(0L)]))
      } else {
        Nil
      },
      list(kept),
      result,
    ])
    displa__set(q_height, h_base + displa__max(d01 + h01, d11 + h11))
    displa__set(q_depth, d_base + displa__max(d00 + h00, d10 + h10))
  }
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  result
}

///|
fn dimension_indices(
  base_symbol : Value,
  indices : Value,
) -> (
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
  Value,
) raise {
  let mut display_indices = safe_mget(base_symbol, q_display_indices)
  let separator = {
    let x = safe__dolget(base_symbol, q_d_display_index_separator)
    if x is Nil || stringp(x) {
      x
    } else {
      Str(char_list_to_string(mstring(x)))
    }
  }
  if length(display_indices) > 0 &&
    length(display_indices) != length(indices) {
    // Ignore DISPLAY-INDICES if it's nonempty and not the same size as
    // INDICES.
    display_indices = Nil
  }
  let (pre_subscripts, pre_superscripts, post_subscripts, post_superscripts) = if display_indices.truthy() {
    (
      extract_indices(indices, display_indices, q_d_presubscript),
      extract_indices(indices, display_indices, q_d_presuperscript),
      extract_indices(indices, display_indices, q_d_postsubscript),
      extract_indices(indices, display_indices, q_d_postsuperscript),
    )
  } else {
    (Nil, Nil, indices, Nil)
  }
  with_specials(
    [
      (q_pre_subscripts, pre_subscripts),
      (q_pre_superscripts, pre_superscripts),
      (q_post_subscripts, post_subscripts),
      (q_post_superscripts, post_superscripts),
    ],
    () => {
      let dim = fn(subs : Value) -> (Value, Value, Value, Value) raise {
        if subs is Nil {
          return (Nil, Fix(0L), Fix(0L), Fix(0L))
        }
        let out = with_specials(
          [
            (q_lop, q_mparen),
            (q_rop, q_mparen),
            (q_break, Nil),
            (q_size, Fix(1L)),
          ],
          () => dimension_list(cons(list1(q_mlist), subs), Nil, separator~),
        )
        (out, symval(q_width), symval(q_height), symval(q_depth))
      }
      let (o00, w00, h00, d00) = dim(pre_subscripts)
      let (o01, w01, h01, d01) = dim(pre_superscripts)
      let (o10, w10, h10, d10) = dim(post_subscripts)
      let (o11, w11, h11, d11) = dim(post_superscripts)
      (
        w00, w01, w10, w11, h00, h01, h10, h11, d00, d01, d10, d11, o00, o01, o10,
        o11,
      )
    },
  )
}

///|
fn extract_indices(
  indices : Value,
  display_indices : Value,
  index_flag : Value,
) -> Value raise {
  let c = Collector::new()
  let n = length(display_indices)
  for i = 0; i <= n; i = i + 1 {
    if eq(nth(i, display_indices), index_flag) {
      c.add(nth(i, indices))
    } else {
      c.add(Nil)
    }
  }
  remove(Nil, c.result())
}

///|
fn safe__dolget(x : Value, y : Value) -> Value raise {
  if symbolp(x) {
    d_get(x, y)
  } else {
    Nil
  }
}

///|
fn dimension_function(x : Value, result : Value) -> Value raise {
  let mut x = x
  let mut result = result
  let mut w = 0
  if !symval(q_d_noundisp).truthy() || !symbolp(caar(x)) {
    ()
  } else if get(caar(x), q_verb).truthy() && get(caar(x), q_alias).truthy() {
    result = displa__push("''", result)
    w = 2
  } else if get(caar(x), q_noun).truthy() &&
    !memq(caar(x), cdr(symval(q_d_aliases))).truthy() &&
    !get(caar(x), q_reversealias).truthy() {
    result = cons(Char('\''), result)
    w = 1
  }
  let fun = if eq(caar(x), q_mqapply) {
    let f = cadr(x)
    x = cdr(x)
    f
  } else {
    caar(x)
  }
  result = with_special(q_atom_context, q_dimension_function, () => dimension(
    fun,
    result,
    symval(q_lop),
    q_mparen,
    Fix(0L),
    Fix(1L),
  ))
  w = w + displa__i(q_width)
  let h = displa__i(q_height)
  let d = displa__i(q_depth)
  if cdr(x) is Nil {
    result = list_star([Char(')'), Char('('), result])
    displa__set(q_width, 2 + w)
  } else {
    let brk = symval(q_break)
    let x1 = x
    let r0 = result
    result = with_specials(
      [
        (q_lop, q_mparen),
        (q_rop, q_mparen),
        (
          q_break,
          if brk.truthy() {
            int(1 + w + to_int(brk))
          } else {
            Nil
          },
        ),
      ],
      () => cons(Char(')'), dimension_list(x1, cons(Char('('), r0))),
    )
    displa__set(q_width, 2 + w + displa__i(q_width))
    displa__set(q_height, displa__max(h, displa__i(q_height)))
    displa__set(q_depth, displa__max(d, displa__i(q_depth)))
  }
  result
}

///|
fn dimension_prefix(form : Value, result : Value) -> Value raise {
  let dissym = safe_get(caar(form), q_dissym)
  let symlength = length(dissym)
  let result = dimension(
    cadr(form),
    revappend(dissym, result),
    caar(form),
    symval(q_rop),
    int(symlength),
    symval(q_right),
  )
  displa__set(q_width, symlength + displa__i(q_width))
  result
}

///|
fn dimension_list(
  form : Value,
  result : Value,
  separator? : Value = Nil,
) -> Value raise {
  let mut result = dimension(
    cadr(form),
    result,
    symval(q_lop),
    q_mcomma,
    Fix(0L),
    symval(q_right),
  )
  let mut w = displa__i(q_width)
  let mut h = displa__i(q_height)
  let mut d = displa__i(q_depth)
  let sep = match separator {
    Str(s) => Some(s)
    _ => None
  }
  for item in cddr(form).iter() {
    match sep {
      Some(s) => {
        result = displa__push(s, result)
        w = w + s.length()
      }
      None => {
        result = displa__push(", ", result)
        w = w + 2
      }
    }
    checkbreak(result, int(w)) |> ignore
    result = dimension(item, result, q_mcomma, q_mcomma, int(w), symval(q_right))
    w = w + displa__i(q_width)
    h = displa__max(h, displa__i(q_height))
    d = displa__max(d, displa__i(q_depth))
  }
  displa__set(q_width, w)
  displa__set(q_height, h)
  displa__set(q_depth, d)
  result
}

///|
fn dimension_infix(form : Value, result : Value) -> Value raise {
  if length(cdr(form)) != 2 {
    return dimension_function(form, result)
  }
  let dissym = safe_get(caar(form), q_dissym)
  let symlength = length(dissym)
  let mut result = dimension(
    cadr(form),
    result,
    symval(q_lop),
    caar(form),
    Fix(0L),
    int(symlength),
  )
  let w = displa__i(q_width)
  let h = displa__i(q_height)
  let d = displa__i(q_depth)
  result = revappend(dissym, result)
  checkbreak(result, int(symlength + w)) |> ignore
  result = dimension(
    caddr(form),
    result,
    caar(form),
    symval(q_rop),
    int(symlength + w),
    symval(q_right),
  )
  displa__set(q_width, w + symlength + displa__i(q_width))
  displa__set(q_height, displa__max(h, displa__i(q_height)))
  displa__set(q_depth, displa__max(d, displa__i(q_depth)))
  result
}

///|
fn dimension_nary(form : Value, result : Value) -> Value raise {
  // If only 0 or 1 arguments, then print "*"() or "*"(A)
  if cddr(form) is Nil {
    return dimension_function(form, result)
  }
  let op = caar(form)
  let dissym = safe_get(op, q_dissym)
  let symlength = length(dissym)
  // Look for a helper function. Fall back on default if none found.
  let helper = {
    let h = safe_get(op, q_dimension_nary_helper)
    if h.truthy() {
      h
    } else {
      q_dimnary
    }
  }
  let mut result = funcall(helper, [
    cadr(form),
    result,
    symval(q_lop),
    op,
    op,
    Fix(0L),
  ])
  let mut w = displa__i(q_width)
  let mut h = displa__i(q_height)
  let mut d = displa__i(q_depth)
  let mut l = cddr(form)
  while true {
    checkbreak(result, int(w)) |> ignore
    result = revappend(dissym, result)
    w = symlength + w
    if cdr(l) is Nil {
      result = funcall(helper, [car(l), result, op, op, symval(q_rop), int(w)])
      displa__set(q_width, w + displa__i(q_width))
      displa__set(q_height, displa__max(h, displa__i(q_height)))
      displa__set(q_depth, displa__max(d, displa__i(q_depth)))
      break
    } else {
      result = funcall(helper, [car(l), result, op, op, op, int(w)])
      w = w + displa__i(q_width)
      h = displa__max(h, displa__i(q_height))
      d = displa__max(d, displa__i(q_depth))
    }
    l = cdr(l)
  }
  result
}

///|
/// Output for MTEXT, generated for example by print(...).
/// Suppress parentheses which would be generated by DIMNARY.
fn dimnary_mtext(
  form : Value,
  result : Value,
  lop : Value,
  op : Value,
  rop : Value,
  w : Value,
) -> Value raise {
  ignore(op)
  dimension(form, result, lop, rop, w, symval(q_right))
}

///|
/// Output for general n-ary operators.
/// Heuristic: if some argument is displayed as an infix or n-ary operator,
/// then put parentheses around that argument (even if parentheses are not
/// necessary, according to operator precedence, to disambiguate the output).
fn dimnary(
  form : Value,
  result : Value,
  lop : Value,
  op : Value,
  rop : Value,
  w : Value,
) -> Value raise {
  ignore(op)
  if consp(form) &&
    memq(
      safe_get(caar(form), q_dimension),
      list([q_dimension_infix, q_dimension_nary]),
    ).truthy() {
    let result = cons(
      Char(')'),
      dimension(
        form,
        cons(Char('('), result),
        q_mparen,
        q_mparen,
        if w.truthy() {
          num_add(w, Fix(1L))
        } else {
          Nil
        },
        int(displa__i(q_right) + 1),
      ),
    )
    displa__set(q_width, displa__i(q_width) + 2)
    result
  } else {
    dimension(form, result, lop, rop, w, symval(q_right))
  }
}

///|
/// Output for Boolean n-ary operators.
fn dimnary_boolean(
  form : Value,
  result : Value,
  lop : Value,
  op : Value,
  rop : Value,
  w : Value,
) -> Value raise {
  ignore(op)
  if consp(form) &&
    (
      memq(
        safe_get(caar(form), q_dimension),
        list([q_dimension_infix, q_dimension_nary]),
      ).truthy() ||
      eq(caar(form), q_mnot)
    ) {
    dimension_paren(form, result)
  } else {
    dimension(form, result, lop, rop, w, symval(q_right))
  }
}

///|
fn dimension_postfix(form : Value, result : Value) -> Value raise {
  let dissym = safe_get(caar(form), q_dissym)
  let symlength = length(dissym)
  let result = dimension(
    cadr(form),
    result,
    symval(q_lop),
    caar(form),
    Fix(0L),
    int(symlength + displa__i(q_right)),
  )
  displa__set(q_width, symlength + displa__i(q_width))
  revappend(dissym, result)
}

///|
fn dimension_nofix(form : Value, result : Value) -> Value raise {
  let form = safe_get(caar(form), q_dissym)
  displa__set(q_width, length(form))
  revappend(form, result)
}

///|
fn dimension_match(form : Value, result : Value) -> Value raise {
  let dissym = safe_get(caar(form), q_dissym)
  let symlength = length(car(dissym))
  if cdr(form) is Nil {
    displa__set(q_width, symlength + length(cdr(dissym)))
    displa__set(q_height, 1)
    displa__set(q_depth, 0)
    return revappend(cdr(dissym), revappend(car(dissym), result))
  }
  let brk = symval(q_break)
  let result = with_specials(
    [
      (q_lop, q_mparen),
      (q_rop, q_mparen),
      (
        q_break,
        if brk.truthy() {
          int(symlength + to_int(brk))
        } else {
          Nil
        },
      ),
      (q_right, int(symlength + displa__i(q_right))),
    ],
    () => dimension_list(form, revappend(car(dissym), result)),
  )
  displa__set(
    q_width,
    length(cdr(dissym)) + symlength + displa__i(q_width),
  )
  revappend(cdr(dissym), result)
}

///|
fn dimension_superscript(form : Value, result : Value) -> Value raise {
  let mut result = result
  let exp = with_special(q_size, Fix(1L), () => dimension(
    caddr(form),
    Nil,
    q_mparen,
    q_mparen,
    Nil,
    Fix(0L),
  ))
  let w = displa__i(q_width)
  let h = displa__i(q_height)
  let d = displa__i(q_depth)
  if !atom(cadr(form)) && memq(q_array, cdr(caadr(form))).truthy() {
    if safe_mget(caaadr(form), q_display_indices).truthy() {
      return dimension_superscript(
        list([
          first(form),
          list([list1(q_mprogn), second(form)]),
          third(form),
        ]),
        result,
      )
    }
    let sub = if eq(q_mqapply, caaadr(form)) {
      cdadr(form)
    } else {
      cadr(form)
    }
    let sub = with_specials(
      [(q_lop, q_mparen), (q_break, Nil), (q_size, Fix(1L))],
      () => dimension_list(sub, Nil),
    )
    let w2 = displa__i(q_width)
    let h2 = displa__i(q_height)
    let d2 = displa__i(q_depth)
    let bas = dimension(
      mop(cadr(form)),
      result,
      symval(q_lop),
      q_mexpt,
      Nil,
      Fix(0L),
    )
    if !displa__checkfit(displa__i(q_width) + displa__max(w, w2)) {
      result = dimension_function(cons(list1(q_d_expt), cdr(form)), result)
    } else {
      result = cons(
        cons(Fix(0L), cons(int(displa__i(q_height) + d), exp)),
        bas,
      )
      result = cons(
        cons(int(-w), cons(int(-(displa__i(q_depth) + h2)), sub)),
        result,
      )
      result = cons(list([int(displa__max(w, w2) - w2), Fix(0L)]), result)
      displa__set(q_width, displa__i(q_width) + displa__max(w, w2))
      displa__set(q_height, h + d + displa__i(q_height))
      displa__set(q_depth, d2 + h2 + displa__i(q_depth))
    }
    update_heights(symval(q_height), symval(q_depth)) |> ignore
    return result
  }
  if atom(caddr(form)) &&
    !atom(cadr(form)) &&
    !safe_get(caaadr(form), q_dimension).truthy() {
    let bas = nformat_check(cadr(form))
    if !safe_get(caar(bas), q_dimension).truthy() {
      return dimension_function(
        list_star([
          list1(q_mqapply),
          list([list1(q_mexpt), mop(bas), caddr(form)]),
          margs(bas),
        ]),
        result,
      )
    }
  }
  let bas = dimension(cadr(form), result, symval(q_lop), q_mexpt, Nil, Fix(0L))
  displa__set(q_width, w + displa__i(q_width))
  if !displa__checkfit(displa__i(q_width)) {
    return dimension_function(cons(list1(q_d_expt), cdr(form)), result)
  }
  if car(bas) is Char(')') {
    result = cons(list_star([Fix(0L), int(1 + d), exp]), bas)
    displa__set(q_height, displa__max(1 + h + d, displa__i(q_height)))
  } else {
    result = cons(
      list_star([Fix(0L), int(displa__i(q_height) + d), exp]),
      bas,
    )
    displa__set(q_height, h + d + displa__i(q_height))
  }
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  result
}

///|
fn dsumprod(
  form : Value,
  result : Value,
  d__form : Value,
  symbol_w_above : Value,
  symbol_w_below : Value,
  symbol_h : Value,
  symbol_d : Value,
) -> Value raise {
  let symbol_w_above = to_int(symbol_w_above)
  let symbol_w_below = to_int(symbol_w_below)
  let symbol_h = to_int(symbol_h)
  let symbol_d = to_int(symbol_d)
  let lsum = eq(caar(form), q_p_lsum)
  // format the variable
  let mut dummy2 = dimension(caddr(form), Nil, q_mparen, q_mequal, Nil, Fix(0L))
  let mut w = displa__i(q_width)
  let mut h = displa__i(q_height)
  let mut d = displa__i(q_depth)
  let (str, to) : (String, Value) = if lsum { (" in ", Str("")) } else { (" = ", nth(4, form)) }
  dummy2 = displa__push(str, dummy2)
  // format the lower limit
  dummy2 = dimension(cadddr(form), dummy2, q_mequal, q_mparen, Nil, Fix(0L))
  w = str.length() + w + displa__i(q_width)
  h = displa__max(h, displa__i(q_height))
  d = displa__max(d, displa__i(q_depth))
  // format the upper limit
  let mut dummy = dimension(to, Nil, q_mparen, q_mparen, Nil, Fix(0L))
  if !displa__checkfit(displa__max(w, displa__i(q_width))) {
    return dimension_function(form, result)
  }
  dummy2 = cons(
    cons(int(-symbol_w_below), cons(int(-(symbol_d + h)), dummy2)),
    cons(d__form, result),
  )
  let mut w1 = 0
  if displa__i(q_width) > symbol_w_below {
    w1 = 0
  } else {
    w1 = (symbol_w_below - displa__i(q_width)) / 2
    displa__set(q_width, w1 + displa__i(q_width))
  }
  dummy = cons(
    cons(int(w1 - w), cons(int(symbol_h + displa__i(q_depth)), dummy)),
    dummy2,
  )
  w = displa__max(w, displa__i(q_width))
  d = symbol_d + h + d
  h = symbol_h + displa__i(q_height) + displa__i(q_depth)
  update_heights(int(h), int(d)) |> ignore
  // format the expression
  dummy = dimension(
    cadr(form),
    cons(list([int(1 + (w - displa__i(q_width))), Fix(0L)]), dummy),
    caar(form),
    symval(q_rop),
    int(w),
    symval(q_right),
  )
  displa__set(
    q_width,
    1 + w + displa__i(q_width) + (symbol_w_above - symbol_w_below) / 2,
  )
  displa__set(q_height, displa__max(h, displa__i(q_height)))
  displa__set(q_depth, displa__max(d, displa__i(q_depth)))
  dummy
}

///|
fn dim_mdefine(form : Value, result : Value) -> Value raise {
  with_specials([(q_d_noundisp, t), (q_d_stringdisp, t)], () => dimension_infix(
    if cdddr(form).truthy() {
      list([car(form), cadr(form), cons(list1(q_mprogn), cddr(form))])
    } else {
      form
    },
    result,
  ))
}

///|
fn dim_mncexpt(form : Value, result : Value) -> Value raise {
  dimension_superscript(
    list([list1(q_mncexpt), cadr(form), cons(list1(q_mangle), cddr(form))]),
    result,
  )
}

///|
fn dim__pctproduct(form : Value, result : Value) -> Value raise {
  let symbol_width_above = if displa__unicode() { 7 } else { 5 }
  let symbol_width_below = 5
  dsumprod(
    form,
    result,
    list1(q_d__prodsign),
    int(symbol_width_above),
    int(symbol_width_below),
    Fix(3L),
    Fix(1L),
  )
}

///|
fn dim_rat(form : Value, result : Value) -> Value raise {
  if symval(q_d_pfeformat).truthy() {
    dimension_nary(form, result)
  } else {
    dim_mquotient(form, result)
  }
}

///|
fn dim_mquotient(form : Value, result : Value) -> Value raise {
  if length(cdr(form)) != 2 {
    return dimension_function(form, result)
  }
  if displa__i(q_size) == 1 && atom(cadr(form)) && atom(caddr(form)) {
    return dimension_nary(form, result)
  }
  let num = dimension(cadr(form), Nil, q_mparen, q_mparen, Nil, symval(q_right))
  let w = displa__i(q_width)
  let h = displa__i(q_height)
  let d = displa__i(q_depth)
  if !displa__checkfit(w) {
    return dimension_nary(form, result)
  }
  let den = dimension(caddr(form), Nil, q_mparen, q_mparen, Nil, symval(q_right))
  if !displa__checkfit(displa__i(q_width)) {
    return dimension_nary(form, result)
  }
  dratio(
    result,
    num,
    int(w),
    int(h),
    int(d),
    den,
    symval(q_width),
    symval(q_height),
    symval(q_depth),
  )
}

///|
fn dratio(
  result : Value,
  num : Value,
  w1 : Value,
  h1 : Value,
  d1 : Value,
  den : Value,
  w2 : Value,
  h2 : Value,
  d2 : Value,
) -> Value raise {
  let w1 = to_int(w1)
  let h1 = to_int(h1)
  let d1 = to_int(d1)
  let w2 = to_int(w2)
  let h2 = to_int(h2)
  let d2 = to_int(d2)
  let width = displa__max(w1, w2)
  displa__set(q_width, width)
  displa__set(q_height, 1 + h1 + d1)
  displa__set(q_depth, h2 + d2)
  let h1x = (width - w1) / 2
  let d2x = (width - w2) / 2
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  let mut result = result
  result = cons(list_star([int(h1x), int(1 + d1), num]), result)
  result = cons(list_star([int(d2x - (h1x + w1)), int(-h2), den]), result)
  result = cons(list([int(0 - d2x - w2), Fix(0L)]), result)
  result = cons(list([q_d__hbar, int(width)]), result)
  result
}

///|
/// This code gets run when STARDISP is assigned a value.
fn stardisp(symbol : Value, val : Value) -> Value raise {
  ignore(symbol)
  putprop(
    q_mtimes,
    if val.truthy() {
      list1(Char('*'))
    } else {
      list1(Char(' '))
    },
    q_dissym,
  )
}

///|
fn dim__pctintegrate(form : Value, result : Value) -> Value raise {
  let n = length(cdr(form))
  if !(n == 2 || n == 4) {
    return dimension_function(form, result)
  }
  let mut dummy : Value = Nil
  let mut w = 0
  let mut h = 0
  let mut d = 0
  if cdddr(form) is Nil {
    dummy = list_star([Char(' '), list1(q_d__integralsign), result])
    w = 2
    h = 3
    d = 2
  } else {
    dummy = dimension(nth(4, form), Nil, q_mparen, q_mparen, Nil, Fix(0L))
    w = displa__i(q_width)
    h = displa__i(q_height)
    d = displa__i(q_depth)
    let dummy2 = dimension(cadddr(form), Nil, q_mparen, q_mparen, Nil, Fix(0L))
    if !displa__checkfit(2 + displa__max(w, displa__i(q_width))) {
      return dimension_function(form, result)
    }
    dummy = list_star([
      list_star([Fix(0L), int(3 + d), dummy]),
      list1(q_d__integralsign),
      result,
    ])
    dummy = cons(
      cons(int(-w), cons(int(-(2 + displa__i(q_height))), dummy2)),
      dummy,
    )
    w = 2 + displa__max(w, displa__i(q_width))
    h = 3 + h + d
    d = 2 + displa__i(q_height) + displa__i(q_depth)
    dummy = cons(list([int(w - 1 - displa__i(q_width)), Fix(0L)]), dummy)
  }
  update_heights(int(h), int(d)) |> ignore
  dummy = dimension(cadr(form), dummy, q_p_integrate, q_mparen, int(w), Fix(2L))
  w = w + displa__i(q_width)
  h = displa__max(h, displa__i(q_height))
  d = displa__max(d, displa__i(q_depth))
  dummy = displa__push(" d", dummy)
  dummy = dimension(
    caddr(form),
    dummy,
    q_mparen,
    symval(q_rop),
    int(2 + w),
    symval(q_right),
  )
  displa__set(q_width, 2 + w + displa__i(q_width))
  displa__set(q_height, displa__max(h, displa__i(q_height)))
  displa__set(q_depth, displa__max(d, displa__i(q_depth)))
  dummy
}

///|
/// A Lisp list of variables on which the expression depends.
fn displa__dependencies(expr : Value) -> Value raise {
  if atom(expr) {
    let deps = mapcar(f => cons(caar(f), cdr(f)), cdr(symval(q_d_dependencies)))
    let v = cdr(assoc(expr, deps))
    if v.truthy() {
      v
    } else {
      list1(expr)
    }
  } else {
    cdr(with_special(q_d_listconstvars, Nil, () => d_listofvars(expr)))
  }
}

///|
/// Determine whether form is a partial derivative, and return d or di.
/// d is symbol to use for regular derivative, usually "d";
/// di is symbol to use for partial derivative.
fn dim_derivative_sym(form : Value, d : Value, di : Value) -> Value raise {
  let expr = cadr(form)
  let dvars = displa__dependencies(cons(list1(q_mlist), cddr(form)))
  let dn = length(dvars)
  let evars = displa__dependencies(expr)
  let e = length(evars)
  if e > 1 || dn > 1 || !equal(dvars, evars) {
    di
  } else {
    d
  }
}

///|
fn dim__pctderivative(form : Value, result : Value) -> Value raise {
  if cddr(form) is Nil {
    return dimension_function(cons(list1(q_p_diff), cdr(form)), result)
  }
  let form = if cdddr(form) is Nil {
    append(form, list1(Fix(1L)))
  } else {
    form
  }
  let abbrev_ok = () => {
    let mut l = cddr(form)
    while l is Cons(_) {
      if atom(car(l)) && integerp(cadr(l)) && num_gt(cadr(l), Fix(0L)) {
        ()
      } else {
        return false
      }
      l = cddr(l)
    }
    true
  }
  let lop = symval(q_lop)
  let rop = symval(q_rop)
  if symval(q_d_derivabbrev).truthy() && abbrev_ok() {
    dmderivabbrev(form, result)
  } else if num_gt(rbp(lop), Fix(130L)) ||
    num_gt(lbp(rop), Fix(130L)) ||
    (
      !atom(cadr(form)) &&
      (num_gt(rbp(lop), Fix(110L)) || num_gt(lbp(rop), Fix(110L)))
    ) {
    dimension_paren(form, result)
  } else {
    dmderivlong(form, result)
  }
}

///|
fn dmderivabbrev(form : Value, result : Value) -> Value raise {
  let mut dummy : Value = Nil
  let mut w = 0
  let mut l = cddr(form)
  while l is Cons(_) {
    let var_ = dimension(car(l), Nil, q_mparen, q_mparen, Nil, Fix(0L))
    let n = to_int(cadr(l))
    let mut i = n
    while i != 1 {
      dummy = cons(Char(' '), append(var_, dummy))
      i -= 1
    }
    dummy = cons(Char(' '), nconc(var_, dummy))
    w = w + n + n * displa__i(q_width)
    l = cddr(l)
  }
  dummy = cdr(dummy)
  w = w - 1
  let mut result = dimension(
    cadr(form),
    result,
    symval(q_lop),
    q_p_deriv,
    Fix(0L),
    symval(q_right),
  )
  result = cons(
    cons(Fix(0L), cons(int(0 - displa__i(q_depth) - 1), dummy)),
    result,
  )
  displa__set(q_width, w + displa__i(q_width))
  displa__set(q_depth, displa__max(1, 1 + displa__i(q_depth)))
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  result
}

///|
fn dmderivlong(form : Value, result : Value) -> Value raise {
  let dsym = dim_derivative_sym(
    form,
    Char('d'),
    if display2d_unicode_enabled().truthy() {
      Char('\u{2202}')
    } else {
      Char('d')
    },
  )
  let mut num = list1(cadddr(form))
  let mut den = if equal(Fix(1L), cadddr(form)) {
    dimension(caddr(form), list1(dsym), q_mparen, q_mparen, Nil, Fix(0L))
  } else {
    dimension_superscript(cons(list1(q_diff), cddr(form)), list1(dsym))
  }
  let mut w2 = 1 + displa__i(q_width)
  let mut h2 = displa__i(q_height)
  let mut d2 = displa__i(q_depth)
  let mut l = cddddr(form)
  while l is Cons(_) {
    num = cons(cadr(l), num)
    den = if equal(Fix(1L), cadr(l)) {
      dimension(
        car(l),
        cons(dsym, cons(Char(' '), den)),
        q_mparen,
        q_mparen,
        Nil,
        Fix(0L),
      )
    } else {
      dimension_superscript(
        cons(list1(q_diff), l),
        cons(dsym, cons(Char(' '), den)),
      )
    }
    w2 = 2 + w2 + displa__i(q_width)
    h2 = displa__max(h2, displa__i(q_height))
    d2 = displa__max(d2, displa__i(q_depth))
    l = cddr(l)
  }
  num = nformat_check(addn(num, t))
  let mut w1 = 0
  let mut h1 = 0
  let mut d1 = 0
  if equal(Fix(1L), num) {
    num = list1(dsym)
    w1 = 1
    h1 = 1
    d1 = 0
  } else {
    num = dimension_superscript(list([list1(q_diff), dsym, num]), Nil)
    w1 = displa__i(q_width)
    h1 = displa__i(q_height)
    d1 = displa__i(q_depth)
  }
  let form = nformat_check(cadr(form))
  if atom(form) {
    num = dimension(form, num, q_p_deriv, q_mparen, Nil, Fix(0L))
    w1 = w1 + displa__i(q_width)
    return dratio(
      result,
      num,
      int(w1),
      int(h1),
      int(d1),
      den,
      int(w2),
      int(h2),
      int(d2),
    )
  }
  let mut result = dratio(
    result,
    num,
    int(w1),
    int(h1),
    int(d1),
    den,
    int(w2),
    int(h2),
    int(d2),
  )
  let w1 = displa__i(q_width)
  let h1 = displa__i(q_height)
  let d1 = displa__i(q_depth)
  result = dimension(
    form,
    cons(Char(' '), result),
    q_p_deriv,
    symval(q_rop),
    int(w1),
    symval(q_right),
  )
  displa__set(q_width, 1 + w1 + displa__i(q_width))
  displa__set(q_height, displa__max(h1, displa__i(q_height)))
  displa__set(q_depth, displa__max(d1, displa__i(q_depth)))
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  result
}

///|
/// An alist whose key represents the unicode character we're looking for
/// and whose value is the Unicode code for the corresponding character.
let displa__unicode_alist : Array[(String, Int)] = [
  ("box-drawings-light-vertical", 0x2502),
  ("box-drawings-light-horizontal", 0x2500),
  ("box-drawings-light-down-and-right", 0x250c),
  ("box-drawings-light-down-and-left", 0x2510),
  ("box-drawings-light-up-and-left", 0x2518),
  ("box-drawings-light-up-and-right", 0x2514),
  ("box-drawings-light-down-and-horizontal", 0x252c),
  ("box-drawings-double-horizontal", 0x2550),
  ("box-drawings-double-vertical", 0x2551),
  ("box-drawings-double-down-and-right", 0x2554),
  ("box-drawings-double-down-and-left", 0x2557),
  ("box-drawings-double-up-and-left", 0x255d),
  ("box-drawings-double-up-and-right", 0x255a),
  ("mathematical-right-angle-bracket", 0x27E9),
  ("top-half-integral", 0x2320),
  ("integral-extension", 0x23ae),
  ("bottom-half-integral", 0x2321),
  ("low-line", 0x005f),
  ("box-drawings-light-diagonal-upper-left-to-lower-right", 0x2572),
  ("box-drawings-light-diagonal-upper-right-to-lower-left", 0x2571),
  ("overline", 0x203e),
]

///|
/// Return the Unicode character corresponding to the CHAR-KEYWORD.
fn get_unicode_char(char_keyword : Value) -> Value raise {
  for e in displa__unicode_alist {
    if eq(char_keyword, kw(e.0)) {
      return Char(code_char(e.1))
    }
  }
  raise LispError::SimpleError("Unknown char keyword: " + prin1_to_string(char_keyword))
}

///|
fn displa__uchar(name : String) -> Value raise {
  get_unicode_char(kw(name))
}

///|
fn display2d_unicode_enabled() -> Value raise {
  lbool(symval(q_d_display2d_unicode).truthy())
}

///|
fn dim__pctat(form : Value, result : Value) -> Value raise {
  if length(cdr(form)) != 2 {
    return dimension_function(form, result)
  }
  let at_char = if display2d_unicode_enabled().truthy() {
    symval(q_at_char_unicode)
  } else {
    displa__first_char(symval(q_d_absboxchar))
  }
  let exp = dimension(cadr(form), result, symval(q_lop), q_p_at, Nil, Fix(0L))
  let w = displa__i(q_width)
  let h = displa__i(q_height)
  let d = displa__i(q_depth)
  let eqs = dimension(
    if !eq(q_mlist, caar(caddr(form))) {
      caddr(form)
    } else if cddr(caddr(form)) is Nil {
      cadr(caddr(form))
    } else {
      cons(list1(q_mcomma), cdaddr(form))
    },
    Nil,
    q_mparen,
    q_mparen,
    Nil,
    Fix(0L),
  )
  if !displa__checkfit(1 + w + displa__i(q_width)) {
    return dimension_function(form, result)
  }
  let result = cons(
    cons(Fix(0L), cons(int(0 - 1 - d), eqs)),
    cons(list([q_d__vbar, int(1 + h), int(1 + d), at_char]), exp),
  )
  displa__set(q_width, 1 + w + displa__i(q_width))
  displa__set(q_height, 1 + h)
  displa__set(q_depth, 1 + d + displa__i(q_depth))
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  result
}

///|
/// Shared body of DIM-MPLUS and DIM-MMINUS (they differ in the operator
/// and in which sign a negated term gets).
fn displa__dim_sum(
  form : Value,
  result : Value,
  op : Value,
  unary : Value,
  neg_sign : Char,
  pos_sign : Char,
) -> Value raise {
  // If only 0 or 1 arguments, then print "+"() or +A
  if cddr(form) is Nil &&
    !memq(cadar(form), list([q_trunc, q_exact])).truthy() {
    if cdr(form) is Nil {
      return dimension_function(form, result)
    } else {
      return dimension_prefix(cons(list1(unary), cdr(form)), result)
    }
  }
  let mut result = dimension(cadr(form), result, symval(q_lop), op, Fix(0L), Fix(0L))
  checkbreak(result, symval(q_width)) |> ignore
  let mut l = cddr(form)
  let mut w = displa__i(q_width)
  let mut h = displa__i(q_height)
  let mut d = displa__i(q_depth)
  let trunc = memq(q_trunc, cdar(form)).truthy()
  while true {
    if l is Nil {
      if trunc {
        displa__set(q_width, 8 + w)
        displa__set(q_height, h)
        displa__set(q_depth, d)
        result = displa__push(" + . . .", result)
      }
      return result
    }
    let (dissym, f) = if mmminusp(car(l)).truthy() {
      (list([Char(' '), Char(neg_sign), Char(' ')]), cadar(l))
    } else {
      (list([Char(' '), Char(pos_sign), Char(' ')]), car(l))
    }
    if !trunc && cdr(l) is Nil {
      result = dimension(
        f,
        append(dissym, result),
        op,
        symval(q_rop),
        int(3 + w),
        symval(q_right),
      )
      displa__set(q_width, 3 + w + displa__i(q_width))
      displa__set(q_height, displa__max(h, displa__i(q_height)))
      displa__set(q_depth, displa__max(d, displa__i(q_depth)))
      return result
    } else {
      result = dimension(f, append(dissym, result), op, op, int(3 + w), Fix(0L))
      w = 3 + w + displa__i(q_width)
      h = displa__max(h, displa__i(q_height))
      d = displa__max(d, displa__i(q_depth))
      checkbreak(result, int(w)) |> ignore
    }
    l = cdr(l)
  }
  result
}

///|
fn dim_mplus(form : Value, result : Value) -> Value raise {
  displa__dim_sum(form, result, q_mplus, q_munaryplus, '-', '+')
}

///|
fn dim_mminus(form : Value, result : Value) -> Value raise {
  displa__dim_sum(form, result, q_mminus, q_munaryminus, '+', '-')
}

///|
fn dim__pctlsum(form : Value, result : Value) -> Value raise {
  dsumprod(
    form,
    result,
    list1(q_d__sumsign),
    Fix(4L),
    Fix(4L),
    Fix(3L),
    Fix(2L),
  )
}

///|
fn dim__pctsum(form : Value, result : Value) -> Value raise {
  dsumprod(
    form,
    result,
    list1(q_d__sumsign),
    Fix(4L),
    Fix(4L),
    Fix(3L),
    Fix(2L),
  )
}

///|
fn dim__pctlimit(form : Value, result : Value) -> Value raise {
  let n = length(cdr(form))
  if !(n == 3 || n == 4) {
    return dimension_function(form, result)
  }
  let mut dummy = dimension(third(form), Nil, q_mparen, q_mparen, Nil, Fix(0L))
  let mut w = displa__i(q_width)
  let mut h = displa__i(q_height)
  let mut d = displa__i(q_depth)
  dummy = displa__push(" -> ", dummy)
  dummy = dimension(fourth(form), dummy, q_mparen, q_mparen, Nil, Fix(0L))
  w = 4 + w + displa__i(q_width)
  h = displa__max(h, displa__i(q_height))
  d = displa__max(d, displa__i(q_depth))
  if cddddr(form) is Nil {
    ()
  } else if eq(q_d_plus, fifth(form)) {
    dummy = cons(Char('+'), dummy)
    w += 1
  } else {
    dummy = cons(Char('-'), dummy)
    w += 1
  }
  let result = displa__push("limit", result)
  dummy = cons(list_star([Fix(-5L), int(-h), dummy]), result)
  d = h + d
  update_heights(Fix(1L), int(d)) |> ignore
  dummy = dimension(
    cadr(form),
    cons(list([Fix(1L), Fix(0L)]), dummy),
    q_p_limit,
    symval(q_rop),
    int(1 + w),
    symval(q_right),
  )
  displa__set(q_width, 1 + w + displa__i(q_width))
  displa__set(q_depth, displa__max(d, displa__i(q_depth)))
  dummy
}

///|
/// MCOND or %MCOND always has an even number of arguments.  The first two
/// arguments are the foo and bar in 'if foo then bar .  Of the remaining
/// pairs of arguments, the first is MAYBE-ELSEIF and the second is
/// ELSE-OR-THEN.  The parser appends (T NIL) to any if-then which lacks an
/// else.
fn dim_mcond(form : Value, result : Value) -> Value raise {
  let mut result = displa__push("if ", result)
  result = dimension(cadr(form), result, q_mcond, q_mparen, Fix(3L), Fix(0L))
  let mut w = 3 + displa__i(q_width)
  let mut h = displa__i(q_height)
  let mut d = displa__i(q_depth)
  checkbreak(result, int(w)) |> ignore
  result = displa__push(" then ", result)
  result = dimension(caddr(form), result, q_mcond, q_mparen, int(6 + w), Fix(0L))
  w = 6 + w + displa__i(q_width)
  h = displa__max(h, displa__i(q_height))
  d = displa__max(d, displa__i(q_depth))
  let mut args = cdddr(form)
  while length(args) >= 2 {
    let maybe_elseif = car(args)
    let else_or_then = cadr(args)
    if eq(maybe_elseif, t) && length(args) == 2 {
      if !(eq(q_d_false, else_or_then) || else_or_then is Nil) {
        checkbreak(result, int(w)) |> ignore
        result = displa__push(" else ", result)
        result = dimension(
          else_or_then,
          result,
          q_mcond,
          symval(q_rop),
          int(6 + w),
          symval(q_right),
        )
        w = 6 + w + displa__i(q_width)
        h = displa__max(h, displa__i(q_height))
        d = displa__max(d, displa__i(q_depth))
      }
    } else {
      checkbreak(result, int(w)) |> ignore
      result = displa__push(" elseif ", result)
      result = dimension(
        maybe_elseif,
        result,
        q_mcond,
        symval(q_rop),
        int(8 + w),
        symval(q_right),
      )
      w = 8 + w + displa__i(q_width)
      h = displa__max(h, displa__i(q_height))
      d = displa__max(d, displa__i(q_depth))
      checkbreak(result, int(w)) |> ignore
      result = displa__push(" then ", result)
      result = dimension(
        else_or_then,
        result,
        q_mcond,
        symval(q_rop),
        int(6 + w),
        symval(q_right),
      )
      w = 6 + w + displa__i(q_width)
      h = displa__max(h, displa__i(q_height))
      d = displa__max(d, displa__i(q_depth))
    }
    args = cddr(args)
  }
  displa__set(q_width, w)
  displa__set(q_height, h)
  displa__set(q_depth, d)
  result
}

///|
fn dim_mdo(form : Value, result : Value) -> Value raise {
  let mut result = result
  let mut w = 0
  let mut h = 0
  let mut d = 0
  let mut brkflag = false
  let upd = (k : Int) => {
    w = k + w + displa__i(q_width)
    h = displa__max(h, displa__i(q_height))
    d = displa__max(d, displa__i(q_depth))
  }
  if cadr(form).truthy() {
    result = displa__push("for ", result)
    result = cons(
      Char(' '),
      dimension(cadr(form), result, q_mdo, q_mparen, Fix(4L), symval(q_right)),
    )
    w = 4 + displa__i(q_width)
    h = displa__i(q_height)
    d = displa__i(q_depth)
    brkflag = true
  }
  if caddr(form) is Nil || equal(Fix(1L), caddr(form)) {
    ()
  } else {
    result = displa__push("from ", result)
    result = cons(
      Char(' '),
      dimension(caddr(form), result, q_mdo, q_mparen, int(6 + w), Fix(0L)),
    )
    upd(6)
  }
  let form = cdddr(form)
  if equal(Fix(1L), car(form)) {
    ()
  } else if car(form).truthy() {
    result = displa__push("step ", result)
    result = cons(
      Char(' '),
      dimension(car(form), result, q_mdo, q_mparen, int(6 + w), Fix(0L)),
    )
    upd(6)
  } else if cadr(form).truthy() {
    result = displa__push("next ", result)
    result = cons(
      Char(' '),
      dimension(cadr(form), result, q_mdo, q_mparen, int(6 + w), Fix(0L)),
    )
    upd(6)
  }
  if caddr(form).truthy() {
    result = displa__push("thru ", result)
    result = cons(
      Char(' '),
      dimension(caddr(form), result, q_mdo, q_mparen, int(6 + w), Fix(0L)),
    )
    upd(6)
    brkflag = true
  }
  if cadddr(form).truthy() {
    if !atom(cadddr(form)) && eq(caar(cadddr(form)), q_mnot) {
      result = displa__push("while ", result)
      result = cons(
        Char(' '),
        dimension(cadr(cadddr(form)), result, q_mdo, q_mparen, int(7 + w), Fix(0L)),
      )
      upd(7)
    } else {
      result = displa__push("unless ", result)
      result = cons(
        Char(' '),
        dimension(cadddr(form), result, q_mdo, q_mparen, int(8 + w), Fix(0L)),
      )
      upd(8)
    }
  }
  if brkflag {
    checkbreak(result, int(w)) |> ignore
  }
  result = displa__push("do ", result)
  result = dimension(
    car(cddddr(form)),
    result,
    q_mdo,
    symval(q_rop),
    int(4 + w),
    symval(q_right),
  )
  displa__set(q_width, 4 + w + displa__i(q_width))
  displa__set(q_height, displa__max(h, displa__i(q_height)))
  displa__set(q_depth, displa__max(d, displa__i(q_depth)))
  result
}

///|
fn dim_mdoin(form : Value, result : Value) -> Value raise {
  let mut result = displa__push("for ", result)
  result = dimension(cadr(form), result, q_mdo, q_mparen, Fix(4L), Fix(0L))
  let mut w = 4 + displa__i(q_width)
  let mut h = displa__i(q_height)
  let mut d = displa__i(q_depth)
  let upd = (k : Int) => {
    w = k + w + displa__i(q_width)
    h = displa__max(h, displa__i(q_height))
    d = displa__max(d, displa__i(q_depth))
  }
  result = displa__push(" in ", result)
  result = dimension(caddr(form), result, q_mdo, q_mparen, int(4 + w), Fix(0L))
  upd(4)
  let form = cdr(cddddr(form))
  if car(form).truthy() {
    result = displa__push(" thru ", result)
    result = dimension(car(form), result, q_mdo, q_mparen, int(6 + w), Fix(0L))
    upd(6)
  }
  if cadr(form).truthy() {
    result = displa__push(" unless ", result)
    result = dimension(cadr(form), result, q_mdo, q_mparen, int(8 + w), Fix(0L))
    upd(8)
  }
  result = displa__push(" do ", result)
  result = dimension(
    caddr(form),
    result,
    q_mdo,
    symval(q_rop),
    int(4 + w),
    symval(q_right),
  )
  displa__set(q_width, 4 + w + displa__i(q_width))
  displa__set(q_height, displa__max(h, displa__i(q_height)))
  displa__set(q_depth, displa__max(d, displa__i(q_depth)))
  result
}

///|
/// There is wired knowledge of character offsets here.
fn dim_mabs(form : Value, result : Value) -> Value raise {
  let mabs_char = if display2d_unicode_enabled().truthy() {
    symval(q_mabs_char_unicode)
  } else {
    displa__first_char(symval(q_d_absboxchar))
  }
  let arg = dimension(cadr(form), Nil, q_mparen, q_mparen, Nil, Fix(0L))
  if 2 + displa__i(q_width) > displa__linel() ||
    (displa__i(q_height) == 1 && displa__i(q_depth) == 0) {
    dimension_function(form, result)
  } else {
    displa__set(q_width, 2 + displa__i(q_width))
    update_heights(symval(q_height), symval(q_depth)) |> ignore
    let bar = list([q_d__vbar, symval(q_height), symval(q_depth), mabs_char])
    cons(bar, nconc(arg, cons(bar, result)))
  }
}

///|
fn dim__dolmatrix(form : Value, result : Value) -> Value raise {
  let cols = if d_listp(cadr(form)).truthy() { length(cadr(form)) } else { 0 }
  let malformed = () => {
    for row in cdr(form).iter() {
      if !d_listp(row).truthy() || cols != length(row) {
        return true
      }
    }
    false
  }
  if cdr(form) is Nil ||
    memalike(list1(list2(q_mlist, q_simp)), cdr(form)).truthy() ||
    malformed() {
    // The matrix is not well formed. Display the matrix in linear mode.
    return dimension_function(form, result)
  }
  let pad_h = symval(q_d_display_matrix_padding_horizontal).truthy()
  let pad_v = symval(q_d_display_matrix_padding_vertical).truthy()
  let mut dmstr : Value = Nil
  let mut cstr : Value = Nil
  let mut rstr : Value = Nil
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
        width = (if pad_h { 2 } else { 0 }) + to_int(cs) + width
      }
      displa__set(q_width, width)
      if display2d_unicode_enabled().truthy() {
        h1 = 1 + h1 + d1
      } else {
        h1 = h1 + d1 - 1
      }
      let depth = h1 / 2
      displa__set(q_depth, depth)
      displa__set(q_height, h1 - depth)
      break
    }
    let mut c = cdar(r)
    let mut nc = dmstr
    let mut cs = cstr
    let mut h2 = 0
    let mut d2 = 0
    while true {
      if c is Nil {
        d1 = (if pad_v || rstr is Nil { d1 } else { d1 - 1 }) + h1 + h2
        h1 = 1 + d2
        break
      }
      let dummy = dimension(car(c), Nil, q_mparen, q_mparen, Nil, Fix(0L))
      h2 = displa__max(h2, displa__i(q_height))
      d2 = displa__max(d2, displa__i(q_depth))
      if !displa__checkfit(14 + displa__i(q_width)) {
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
        rplaca(cs, int(displa__max(displa__i(q_width), to_int(car(cs))))) |> ignore
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
      if displa__i(q_height) + displa__i(q_depth) > a.data.length() {
        consp_ = true
      }
    _ => ()
  }
  if !consp_ &&
    displa__checkfit(
      if symval(q_d_display_matrix_brackets).truthy() {
        2 + displa__i(q_width)
      } else {
        displa__i(q_width)
      },
    ) {
    matout(dmstr, cstr, rstr, result)
  } else if !consp_ && displa__i(q_level) <= 2 {
    colout(form, result)
  } else {
    dimension_function(form, result)
  }
}

///|
fn matout(dmstr : Value, cstr : Value, rstr : Value, result : Value) -> Value raise {
  let brackets = symval(q_d_display_matrix_brackets).truthy()
  let pad_h = symval(q_d_display_matrix_padding_horizontal).truthy()
  let unicode = display2d_unicode_enabled().truthy()
  let mut result = result
  if brackets {
    result = cons(
      list([q_d__matrix, q_left, symval(q_height), symval(q_depth)]),
      result,
    )
  }
  if pad_h {
    result = cons(Char(' '), result)
  }
  let height = displa__i(q_height)
  let mut d = dmstr
  let mut c = cstr
  while d is Cons(_) {
    let mut w = 0
    let mut dd = car(d)
    let mut r = rstr
    let cc = to_int(car(c))
    while dd is Cons(_) {
      rplaca(
        cddar(dd),
        int(height - to_int(car(r)) - (if unicode { 1 } else { 0 })),
      )
      |> ignore
      let ew = to_int(caar(dd))
      rplaca(cdar(dd), int((cc - ew) / 2 - w)) |> ignore
      w = (cc + ew) / 2
      rplaca(dd, cdar(dd)) |> ignore
      dd = cdr(dd)
      r = cdr(r)
    }
    result = cons(
      list([
        int(
          (if pad_h {
            2
          } else if cdr(c).truthy() {
            0
          } else {
            1
          }) +
          (cc - w),
        ),
        Fix(0L),
      ]),
      nreconc(car(d), result),
    )
    d = cdr(d)
    c = cdr(c)
  }
  if brackets {
    displa__set(q_width, 2 + displa__i(q_width))
  } else if symval(q_d_display2d_unicode).truthy() {
    displa__set(q_height, displa__i(q_height) - 1)
    displa__set(q_depth, displa__i(q_depth) - 1)
  }
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  rplaca(car(result), num_sub(caar(result), Fix(1L))) |> ignore
  if brackets {
    result = cons(
      list([q_d__matrix, q_right, symval(q_height), symval(q_depth)]),
      result,
    )
  }
  result
}

///|
fn colout(form : Value, result : Value) -> Value raise {
  let n = to_int(d_length(d_first(form)))
  let c = Collector::new()
  for k = 1; k <= n; k = k + 1 {
    c.add(list([list1(q_mequal), Str(" Col \{k}"), d_col(form, int(k))]))
  }
  dimension_list(cons(list1(q_mlist), c.result()), result, separator=Str(""))
}

///|
fn dim_determinant(form : Value, result : Value) -> Value raise {
  let a = rest(form)
  if symval(q_d_display_determinant_bars).truthy() &&
    length(a) == 1 &&
    d_matrixp(first(a)).truthy() {
    with_special(q_d_display_matrix_brackets, Nil, () => dim_mabs(
      list([list1(q_mabs), first(a)]),
      result,
    ))
  } else {
    dimension_function(form, result)
  }
}

///|
fn dim_mbox_or_mlabox(form : Value, result : Value) -> Value raise {
  if length(form) == 3 {
    dim_mlabox(form, result)
  } else {
    dim_mbox(form, result)
  }
}

///|
fn dim_mbox(form : Value, result : Value) -> Value raise {
  let dummy = dimension(cadr(form), Nil, q_mparen, q_mparen, Nil, Fix(0L))
  if !displa__checkfit(2 + displa__i(q_width)) {
    dimension_function(cons(list1(q_d_box), cdr(form)), result)
  } else {
    let result = cons(
      list([
        q_d__box,
        symval(q_height),
        symval(q_depth),
        symval(q_width),
        nreverse(dummy),
      ]),
      result,
    )
    displa__set(q_width, 2 + displa__i(q_width))
    displa__set(q_height, 1 + displa__i(q_height))
    displa__set(q_depth, 1 + displa__i(q_depth))
    update_heights(symval(q_height), symval(q_depth)) |> ignore
    result
  }
}

///|
fn dim_mlabox(form : Value, result : Value) -> Value raise {
  if display2d_unicode_enabled().truthy() {
    dim_mlabox_unicode(form, result)
  } else {
    dim_mlabox_ascii(form, result)
  }
}

///|
/// Bind the six box-drawing specials to the light (single-line) characters.
fn displa__with_light_box(f : () -> Value raise) -> Value raise {
  with_specials(
    [
      (
        q_ear_d_box_char_unicode_horz,
        displa__uchar("box-drawings-light-horizontal"),
      ),
      (
        q_ear_d_box_char_unicode_vert,
        displa__uchar("box-drawings-light-vertical"),
      ),
      (
        q_ear_d_box_char_unicode_upper_left,
        displa__uchar("box-drawings-light-down-and-right"),
      ),
      (
        q_ear_d_box_char_unicode_upper_right,
        displa__uchar("box-drawings-light-down-and-left"),
      ),
      (
        q_ear_d_box_char_unicode_lower_right,
        displa__uchar("box-drawings-light-up-and-left"),
      ),
      (
        q_ear_d_box_char_unicode_lower_left,
        displa__uchar("box-drawings-light-up-and-right"),
      ),
    ],
    f,
  )
}

///|
fn dim_mlabox_unicode(form : Value, result : Value) -> Value raise {
  if symval(q_d_display_box_double_lines).truthy() {
    dim_mlabox_unicode_default(form, result)
  } else {
    displa__with_light_box(() => dim_mlabox_unicode_default(form, result))
  }
}

///|
/// The label characters of a labelled box, as many as fit in WIDTH, in
/// reverse order, and how many were taken.
fn displa__label_chars(label : Value, width : Int) -> (Value, Int) raise {
  let mut l = mapcar(
    s => match s {
      Sym(_) => displa__first_char(Str(symbol_name(s)))
      Char(_) => s
      _ => Nil
    },
    makstring(label),
  )
  let mut w = 0
  let mut nl : Value = Nil
  while !(l is Nil || width == w) {
    nl = cons(car(l), nl)
    w += 1
    l = cdr(l)
  }
  (nl, w)
}

///|
fn dim_mlabox_unicode_default(form : Value, result : Value) -> Value raise {
  let dummy = dimension(cadr(form), Nil, q_mparen, q_mparen, Nil, Fix(0L))
  if !displa__checkfit(2 + displa__i(q_width)) {
    return dimension_function(cons(list1(q_d_box), cdr(form)), result)
  }
  displa__set(q_width, 2 + displa__i(q_width))
  displa__set(q_height, 1 + displa__i(q_height))
  displa__set(q_depth, 1 + displa__i(q_depth))
  let width = displa__i(q_width)
  let height = displa__i(q_height)
  let depth = displa__i(q_depth)
  let horz = symval(q_ear_d_box_char_unicode_horz)
  let vert = symval(q_ear_d_box_char_unicode_vert)
  let (nl, w) = displa__label_chars(caddr(form), width)
  let mut result = cons(
    cons(
      Fix(0L),
      cons(
        int(height - 1),
        if w < width {
          cons(
            symval(q_ear_d_box_char_unicode_upper_right),
            cons(list([q_d__hbar, int(width - w - 1), horz]), nl),
          )
        } else {
          nl
        },
      ),
    ),
    result,
  )
  result = nconc(
    dummy,
    list_star([
      list([q_d__vbar, int(height - 1), int(depth - 1), vert]),
      list([int(-width), Fix(0L)]),
      result,
    ]),
  )
  result = cons(
    list([
      int(1 - width),
      int(-depth),
      symval(q_ear_d_box_char_unicode_lower_right),
      list([q_d__hbar, int(width - 2), horz]),
      symval(q_ear_d_box_char_unicode_lower_left),
    ]),
    result,
  )
  result = list_star([
    list([q_d__vbar, int(height - 1), int(depth - 1), vert]),
    list([Fix(-1L), Fix(0L)]),
    result,
  ])
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  result
}

///|
fn dim_mlabox_ascii(form : Value, result : Value) -> Value raise {
  let dummy = dimension(cadr(form), Nil, q_mparen, q_mparen, Nil, Fix(0L))
  if !displa__checkfit(2 + displa__i(q_width)) {
    return dimension_function(cons(list1(q_d_box), cdr(form)), result)
  }
  displa__set(q_width, 2 + displa__i(q_width))
  displa__set(q_height, 1 + displa__i(q_height))
  displa__set(q_depth, 1 + displa__i(q_depth))
  let width = displa__i(q_width)
  let height = displa__i(q_height)
  let depth = displa__i(q_depth)
  let ch = displa__first_char(symval(q_d_boxchar))
  let (nl, w) = displa__label_chars(caddr(form), width)
  let mut result = cons(
    cons(
      Fix(0L),
      cons(
        int(height - 1),
        if w < width {
          cons(list([q_d__hbar, int(width - w), ch]), nl)
        } else {
          nl
        },
      ),
    ),
    result,
  )
  result = nconc(
    dummy,
    list_star([
      list([q_d__vbar, int(height - 1), int(depth - 1), ch]),
      list([int(-width), Fix(0L)]),
      result,
    ]),
  )
  result = cons(
    list([int(1 - width), int(-depth), list([q_d__hbar, int(width), ch])]),
    result,
  )
  result = list_star([
    list([q_d__vbar, int(height - 1), int(depth - 1), ch]),
    list([Fix(-1L), Fix(0L)]),
    result,
  ])
  update_heights(symval(q_height), symval(q_depth)) |> ignore
  result
}

///|
fn dim_mtext(form : Value, result : Value) -> Value raise {
  if cddr(form) is Nil {
    dimension(cadr(form), result, symval(q_lop), symval(q_rop), Fix(0L), Fix(0L))
  } else {
    dimension_nary(form, result)
  }
}

///|
fn dim_mlabel(form : Value, result : Value) -> Value raise {
  let mut result = result
  let mut w = 0
  let mut h = 0
  let mut d = 0
  let labels_p = symval(q_ear_display_labels_p).truthy()
  let mratp = symval(q_mratp)
  if cadr(form) is Nil {
    w = 0
    h = 0
    d = 0
  } else if mratp.truthy() {
    result = append(
      mratp,
      if labels_p {
        dimension_paren(cadr(form), result)
      } else {
        Nil
      },
    )
    w = 4 + displa__i(q_width)
    h = displa__i(q_height)
    d = displa__i(q_depth)
  } else {
    result = cons(
      Char(' '),
      if labels_p {
        dimension_paren(cadr(form), result)
      } else {
        Nil
      },
    )
    w = 1 + displa__i(q_width)
    h = displa__i(q_height)
    d = displa__i(q_depth)
  }
  let r0 = result
  with_special(q_level, symval(q_d_linel), () => checkbreak(r0, int(w))) |> ignore
  let dummy = list([Fix(0L), Fix(0L)])
  result = dimension(
    caddr(form),
    cons(dummy, result),
    q_mlabel,
    symval(q_rop),
    int(w),
    symval(q_right),
  )
  if !symval(q_d_leftjust).truthy() && displa__i(q_bkptout) == 0 {
    rplaca(
      dummy,
      int(displa__max(0, (displa__linel() - displa__i(q_width)) / 2 - w)),
    )
    |> ignore
    displa__set(q_width, to_int(car(dummy)) + displa__i(q_width))
  }
  displa__set(q_width, w + displa__i(q_width))
  displa__set(q_height, displa__max(h, displa__i(q_height)))
  displa__set(q_depth, displa__max(d, displa__i(q_depth)))
  result
}
