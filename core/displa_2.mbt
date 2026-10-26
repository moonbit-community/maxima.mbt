// Port of src/displa.lisp, part 2: line breaking, output and the
// drawing functions; displa-def forms and other top-level forms.

///|
fn checkrat(form : Value) -> Value raise {
  if atom(form) {
    return Nil
  }
  if !atom(car(form)) && eq(caar(form), q_mrat) {
    if memq(q_trunc, cdar(form)).truthy() {
      return list([Char(' '), Char('/'), Char('T'), Char('/')])
    } else {
      return list([Char(' '), Char('/'), Char('R'), Char('/')])
    }
  }
  if !atom(car(form)) && eq(caar(form), q_mpois) {
    return list([Char(' '), Char('/'), Char('P'), Char('/')])
  }
  let mut l = cdr(form)
  while l.truthy() {
    if atom(l) {
      merr("display: not a well-formed Maxima expression: ~S", [form]) |> ignore
    }
    let f = checkrat(car(l))
    if f.truthy() {
      return f
    }
    l = cdr(l)
  }
  Nil
}

///|
fn checkfit(w : Value) -> Value raise {
  lbool(displa__checkfit(to_int(w)))
}

///|
fn checkbreak(result : Value, w : Value) -> Value raise {
  let brk = symval(q_break)
  if brk is Nil {
    return Nil
  }
  let w = to_int(w) + to_int(brk)
  let linel = displa__linel()
  let bkpt = symval(q_bkpt)
  if w - displa__i(q_bkptout) > linel {
    if bkpt is Nil || physical_equal_value(result, bkpt) {
      merr(
        "display: failed to break up a long expression.~%display: change '$linel' slightly and try again.",
        [],
      )
      |> ignore
    }
    let mut l = result
    while true {
      if physical_equal_value(bkpt, cdr(l)) {
        rplacd(l, Nil) |> ignore
        break
      }
      if l is Nil {
        // MEANING OF FOLLOWING MESSAGE IS OBSCURE.
        merr("display: 'checkbreak' not found.", []) |> ignore
      }
      l = cdr(l)
    }
    output(bkpt, Fix(0L)) |> ignore
    displa__set(q_lines, 1 + displa__i(q_lines))
    set(q_bkpt, result) |> ignore
    set(q_bkptout, symval(q_bkptwd)) |> ignore
    displa__set(q_bkptwd, w)
    set(q_bkptht, symval(q_maxht)) |> ignore
    set(q_bkptdp, symval(q_maxdp)) |> ignore
    set(q_bkptlevel, symval(q_level)) |> ignore
    displa__set(q_maxht, 1)
    displa__set(q_maxdp, 0)
    Nil
  } else if bkpt is Nil ||
    displa__i(q_level) <= displa__i(q_bkptlevel) ||
    linel / 2 > displa__i(q_bkptwd) - displa__i(q_bkptout) {
    set(q_bkpt, result) |> ignore
    displa__set(q_bkptwd, w)
    set(q_bkptlevel, symval(q_level)) |> ignore
    displa__set(q_bkptht, displa__max(displa__i(q_maxht), displa__i(q_bkptht)))
    displa__set(q_bkptdp, displa__max(displa__i(q_maxdp), displa__i(q_bkptdp)))
    displa__set(q_maxht, 1)
    displa__set(q_maxdp, 0)
    Nil
  } else {
    Nil
  }
}

///|
fn forcebreak(result : Value, w : Value) -> Value raise {
  output(result, Fix(0L)) |> ignore
  displa__set(q_lines, 2 + displa__i(q_lines))
  set(q_bkpt, Nil) |> ignore
  set(q_bkptout, num_add(w, symval(q_break))) |> ignore
  displa__set(q_maxht, 1)
  displa__set(q_maxdp, 0)
  Nil
}

///|
fn update_heights(ht_star : Value, dp_star : Value) -> Value raise {
  if symval(q_break).truthy() {
    set(q_maxht, num_max(symval(q_maxht), ht_star)) |> ignore
    set(q_maxdp, num_max(symval(q_maxdp), dp_star)) |> ignore
  }
  Nil
}

///|
/// When the console is used interactively, the user's ENTER key already
/// moved the cursor to a fresh line (Lisp: INTERACTIVE-STREAM-P).
let displa__interactive : Ref[Bool] = Ref(false)

///|
fn output(result : Value, w : Value) -> Value raise {
  if !(displa__interactive.val && physical_equal_value(symval(standard_input), console_in)) {
    fresh_line() |> ignore
  }
  if symval(q_d_ttyoff).truthy() {
    return Nil
  }
  let n = match symval(q_linearray) {
    Vec(a) => a.data.length()
    _ => 0
  }
  if displa__i(q_bkptht) + displa__i(q_bkptdp) > n {
    // I suppose we could reallocate LINEARRAY to some larger size and keep
    // going here ...
    merr("display: expression is too tall to be displayed.", []) |> ignore
  }
  output_linear(nreverse(result), w)
}

///|
/// Output function for terminals without cursor positioning capability.
/// Characters are drawn into LINEARRAY instead.  Each element of LINEARRAY
/// is a list -- the car is how many spaces to indent; the cdr is a list of
/// characters to draw.  After drawing into this array, lines are printed
/// one at a time.
fn output_linear(result : Value, w : Value) -> Value raise {
  draw_linear(result, symval(q_bkptdp), w) |> ignore
  let la = symval(q_linearray)
  let mut i0 = false
  let mut i = displa__i(q_bkptht) + displa__i(q_bkptdp) - 1
  while i >= 0 {
    let line = aref1(la, i)
    if !i0 && line is Nil {
      ()
    } else {
      i0 = true
      if line is Nil {
        mterpri() |> ignore
      } else {
        output_linear_one_line(int(i)) |> ignore
      }
    }
    i -= 1
  }
  Nil
}

///|
fn output_linear_one_line(i : Value) -> Value raise {
  let la = symval(q_linearray)
  let ii = to_int(i)
  let line = nreverse(cdr(aref1(la, ii)))
  let n = car(line)
  aset1(la, ii, Nil) |> ignore
  tyotbsp(n) |> ignore
  let out = symval(standard_output)
  for v in cdr(line).iter() {
    match v {
      Char(c) => write_char(c, stream=out)
      _ => princ(v, stream=out) |> ignore
    }
  }
  mterpri()
}

///|
/// Move the cursor over N spaces to the left by outputting spaces.
fn tyotbsp(n : Value) -> Value raise {
  let mut n = to_int(n)
  let out = symval(standard_output)
  while n >= 1 {
    write_char(' ', stream=out)
    n -= 1
  }
  Nil
}

///|
/// This puts the LINE lists into LINEARRAY ready to be drawn.  Each LINE
/// consists of first an initial number of columns to space and then the
/// characters to be printed.  OLDROW and OLDCOL (special) are the starting
/// points for the (dx,dy) offsets given in the dimension string DMSTR.
fn draw_linear(dmstr : Value, oldrow : Value, oldcol : Value) -> Value raise {
  with_specials([(q_oldrow, oldrow), (q_oldcol, oldcol)], () => {
    let la = symval(q_linearray)
    let mut dmstr = dmstr
    while dmstr is Cons(_) {
      if atom(car(dmstr)) {
        let row = displa__i(q_oldrow)
        let mut oldcol = displa__i(q_oldcol)
        let mut line = aref1(la, row)
        if line is Nil {
          line = list1(int(oldcol))
        } else {
          let mut n = to_int(car(line))
          line = cdr(line)
          while oldcol > n {
            line = cons(Char(' '), line)
            n += 1
          }
        }
        while dmstr is Cons(_) && atom(car(dmstr)) {
          oldcol += 1
          line = cons(car(dmstr), line)
          dmstr = cdr(dmstr)
        }
        displa__set(q_oldcol, oldcol)
        aset1(la, row, cons(int(oldcol), line)) |> ignore
      } else if integerp(caar(dmstr)) {
        // Why update OLDCOL and not OLDROW?
        let c = draw_linear(
          reverse(cddar(dmstr)),
          num_add(symval(q_oldrow), cadar(dmstr)),
          num_add(symval(q_oldcol), caar(dmstr)),
        )
        set(q_oldcol, c) |> ignore
        dmstr = cdr(dmstr)
      } else {
        let c = apply(caar(dmstr), cons(t, cdar(dmstr)))
        set(q_oldcol, c) |> ignore
        dmstr = cdr(dmstr)
      }
    }
    // Be sure to return this.
    symval(q_oldcol)
  })
}

///|
fn d__hbar(linear_q : Value, w : Value, char_? : Value = Nil) -> Value raise {
  ignore(linear_q)
  let ch = if char_ is Nil {
    if display2d_unicode_enabled().truthy() {
      symval(q_d__hbar_char_unicode)
    } else {
      symval(q_d__hbar_char_ascii)
    }
  } else {
    char_
  }
  let mut nl : Value = Nil
  for i = 0; i < to_int(w); i = i + 1 {
    nl = cons(ch, nl)
  }
  draw_linear(nl, symval(q_oldrow), symval(q_oldcol))
}

///|
fn d__vbar(
  linear_q : Value,
  h : Value,
  d : Value,
  char_body? : Value = Nil,
  char_head? : Value = Nil,
  char_foot? : Value = Nil,
) -> Value raise {
  ignore(linear_q)
  let uni = display2d_unicode_enabled().truthy()
  let body = if char_body is Nil {
    if uni {
      symval(q_d__vbar_char_unicode)
    } else {
      symval(q_d__vbar_char_ascii)
    }
  } else {
    char_body
  }
  let head = if char_head is Nil { body } else { char_head }
  let foot = if char_foot is Nil { body } else { char_foot }
  let h = to_int(h)
  let d = -to_int(d)
  let mut i = h - 2
  let mut nl_head = list1(list([Fix(0L), int(h - 1), head]))
  while true {
    if (uni && i <= d) || (!uni && i < d) {
      if uni && i == d {
        nl_head = cons(list([Fix(-1L), int(i), foot]), nl_head)
      }
      return draw_linear(nreverse(nl_head), symval(q_oldrow), symval(q_oldcol))
    }
    nl_head = cons(list([Fix(-1L), int(i), body]), nl_head)
    i -= 1
  }
  Nil
}

///|
fn d__integralsign(linear_q : Value) -> Value raise {
  ignore(linear_q)
  let dmstr = if display2d_unicode_enabled().truthy() {
    symval(q_d__integralsign_string_unicode)
  } else {
    symval(q_d__integralsign_string_ascii)
  }
  draw_linear(dmstr, symval(q_oldrow), symval(q_oldcol))
}

///|
fn d__prodsign(linear_q : Value) -> Value raise {
  ignore(linear_q)
  let dmstr = if display2d_unicode_enabled().truthy() {
    symval(q_d__prodsign_unicode_dmstr)
  } else {
    symval(q_d__prodsign_ascii_dmstr)
  }
  draw_linear(dmstr, symval(q_oldrow), symval(q_oldcol))
}

///|
fn d__sumsign(linear_q : Value) -> Value raise {
  ignore(linear_q)
  let dmstr = if display2d_unicode_enabled().truthy() {
    symval(q_d__sumsign_unicode_dmstr)
  } else {
    symval(q_d__sumsign_ascii_dmstr)
  }
  draw_linear(dmstr, symval(q_oldrow), symval(q_oldcol))
}

///|
fn d__matrix(linear_q : Value, direction : Value, h : Value, d : Value) -> Value raise {
  if display2d_unicode_enabled().truthy() {
    d__matrix_unicode(linear_q, direction, h, d)
  } else {
    d__matrix_ascii(linear_q, direction, h, d)
  }
}

///|
fn d__matrix_unicode(
  linear_q : Value,
  direction : Value,
  h : Value,
  d : Value,
) -> Value raise {
  ignore(linear_q)
  let right = eq(direction, q_right)
  let char_upper_corner = if right {
    symval(q_d__matrix_char_unicode_upper_right)
  } else {
    symval(q_d__matrix_char_unicode_upper_left)
  }
  let char_lower_corner = if right {
    symval(q_d__matrix_char_unicode_lower_right)
  } else {
    symval(q_d__matrix_char_unicode_lower_left)
  }
  let dmstr = list1(
    list([
      q_d__vbar,
      h,
      d,
      symval(q_d__matrix_char_unicode_vert),
      char_upper_corner,
      char_lower_corner,
    ]),
  )
  draw_linear(dmstr, symval(q_oldrow), symval(q_oldcol))
}

///|
fn d__matrix_ascii(
  linear_q : Value,
  direction : Value,
  h : Value,
  d : Value,
) -> Value raise {
  d__vbar(
    linear_q,
    h,
    d,
    char_body=displa__first_char(
      if eq(direction, q_right) {
        symval(q_d_rmxchar)
      } else {
        symval(q_d_lmxchar)
      },
    ),
  )
}

///|
fn d__box(
  linear_q : Value,
  h : Value,
  d : Value,
  w : Value,
  body : Value,
) -> Value raise {
  ignore(linear_q)
  if display2d_unicode_enabled().truthy() {
    d__box_unicode(h, d, w, body)
  } else {
    d__box_ascii(h, d, w, body)
  }
}

///|
fn d__box_unicode(h : Value, d : Value, w : Value, body : Value) -> Value raise {
  if symval(q_d_display_box_double_lines).truthy() {
    d__box_unicode_default(h, d, w, body)
  } else {
    displa__with_light_box(() => d__box_unicode_default(h, d, w, body))
  }
}

///|
fn d__box_unicode_default(
  h : Value,
  d : Value,
  w : Value,
  body : Value,
) -> Value raise {
  let horz = symval(q_ear_d_box_char_unicode_horz)
  let vert = symval(q_ear_d_box_char_unicode_vert)
  let wi = to_int(w)
  let di = to_int(d)
  let dmstr = append_n([
    list([
      list([
        Fix(0L),
        h,
        symval(q_ear_d_box_char_unicode_upper_right),
        list([q_d__hbar, w, horz]),
        symval(q_ear_d_box_char_unicode_upper_left),
      ]),
      list([int(-(wi + 2)), Fix(0L)]),
      list([q_d__vbar, h, d, vert]),
    ]),
    body,
    list([
      list([
        int(-(1 + wi)),
        int(-(1 + di)),
        symval(q_ear_d_box_char_unicode_lower_right),
        list([q_d__hbar, w, horz]),
        symval(q_ear_d_box_char_unicode_lower_left),
      ]),
      list([Fix(-1L), Fix(0L)]),
      list([q_d__vbar, h, d, vert]),
    ]),
  ])
  draw_linear(dmstr, symval(q_oldrow), symval(q_oldcol))
}

///|
fn d__box_ascii(h : Value, d : Value, w : Value, body : Value) -> Value raise {
  let ch = displa__first_char(symval(q_d_boxchar))
  let wi = to_int(w)
  let di = to_int(d)
  let dmstr = append_n([
    list([
      list([Fix(0L), h, list([q_d__hbar, int(2 + wi), ch])]),
      list([int(-(wi + 2)), Fix(0L)]),
      list([q_d__vbar, h, d, ch]),
    ]),
    body,
    list([
      list([int(-(1 + wi)), int(-(1 + di)), list([q_d__hbar, int(wi + 2), ch])]),
      list([Fix(-1L), Fix(0L)]),
      list([q_d__vbar, h, d, ch]),
    ]),
  ])
  draw_linear(dmstr, symval(q_oldrow), symval(q_oldcol))
}

///|
/// `(displa-def operator dim-function [l-dissym [r-dissym]] [lbp] [rbp])`
fn displa__def(
  op : Value,
  dimfn : Value,
  l_dissym? : String,
  r_dissym? : String,
  bp? : Array[Int] = [],
) -> Unit {
  putprop(op, dimfn, q_dimension) |> ignore
  match (l_dissym, r_dissym) {
    (Some(l), Some(r)) =>
      putprop(op, cons(displa__chars(l), displa__chars(r)), q_dissym) |> ignore
    (Some(l), None) => putprop(op, displa__chars(l), q_dissym) |> ignore
    _ => ()
  }
  let mut lbp : Int? = None
  let mut rbp : Int? = None
  for x in bp {
    if rbp is Some(_) {
      lbp = rbp
    }
    rbp = Some(x)
  }
  if lbp is Some(v) {
    putprop(op, int(v), q_lbp) |> ignore
  }
  if rbp is Some(v) {
    putprop(op, int(v), q_rbp) |> ignore
  }
}

///|
fn init_displa() -> Unit raise {
  // The port is Unicode-capable (the :lisp-unicode-capable feature).
  set(q_d_display2d_unicode, t) |> ignore
  putprop(
    q_d_display2d_unicode,
    lfunc("display2d_unicode-assign", args => {
      let val = arg(args, 1)
      if !(val is Nil || eq(val, t)) {
        mseterr(arg(args, 0), val, reason=Str("must be one of: false, true"))
        |> ignore
      }
      Nil
    }),
    q_assign,
  )
  |> ignore
  defvar_init(q_linearray, make_array([1000], initial=Nil))
  let u = displa__uchar
  defvar_init(q_at_char_unicode, u("box-drawings-light-vertical"))
  defvar_init(q_mabs_char_unicode, u("box-drawings-light-vertical"))
  defvar_init(q_ear_d_box_char_unicode_horz, u("box-drawings-double-horizontal"))
  defvar_init(q_ear_d_box_char_unicode_vert, u("box-drawings-double-vertical"))
  defvar_init(
    q_ear_d_box_char_unicode_upper_left,
    u("box-drawings-double-down-and-right"),
  )
  defvar_init(
    q_ear_d_box_char_unicode_upper_right,
    u("box-drawings-double-down-and-left"),
  )
  defvar_init(
    q_ear_d_box_char_unicode_lower_right,
    u("box-drawings-double-up-and-left"),
  )
  defvar_init(
    q_ear_d_box_char_unicode_lower_left,
    u("box-drawings-double-up-and-right"),
  )
  defvar_init(q_d__hbar_char_unicode, u("box-drawings-light-horizontal"))
  defvar_init(q_d__vbar_char_unicode, u("box-drawings-light-vertical"))
  defvar_init(q_d__hbar_char_ascii, Char('-'))
  defvar_init(q_d__vbar_char_ascii, Char('|'))
  set(
    q_d__integralsign_string_unicode,
    list([
      list([Fix(0L), Fix(2L), u("top-half-integral")]),
      list([Fix(-1L), Fix(1L), u("integral-extension")]),
      list([Fix(-1L), Fix(0L), u("integral-extension")]),
      list([Fix(-1L), Fix(-1L), u("integral-extension")]),
      list([Fix(-1L), Fix(-2L), u("bottom-half-integral")]),
    ]),
  )
  |> ignore
  defvar_init(
    q_d__integralsign_string_ascii,
    list([
      list([Fix(0L), Fix(2L), Char('/')]),
      list([Fix(-1L), Fix(1L), Char('|')]),
      list([Fix(-1L), Fix(0L), Char('|')]),
      list([Fix(-1L), Fix(-1L), Char('|')]),
      list([Fix(-1L), Fix(-2L), Char('/')]),
    ]),
  )
  set(
    q_d__prodsign_unicode_dmstr,
    list([
      list([
        Fix(0L),
        Fix(2L),
        list([q_d__hbar, Fix(1L)]),
        u("box-drawings-light-down-and-horizontal"),
        list([q_d__hbar, Fix(3L)]),
        u("box-drawings-light-down-and-horizontal"),
        list([q_d__hbar, Fix(1L)]),
      ]),
      list([Fix(-6L), Fix(0L)]),
      list([q_d__vbar, Fix(2L), Fix(1L)]),
      Char(' '),
      Char(' '),
      Char(' '),
      list([q_d__vbar, Fix(2L), Fix(1L)]),
      list([Fix(0L), Fix(0L)]),
    ]),
  )
  |> ignore
  defvar_init(
    q_d__prodsign_ascii_dmstr,
    list([
      list([Fix(0L), Fix(2L), list([q_d__hbar, Fix(5L), Char('_')])]),
      list([Fix(-5L), Fix(0L)]),
      list([q_d__vbar, Fix(2L), Fix(1L), Char('|')]),
      Char(' '),
      Char(' '),
      Char(' '),
      list([q_d__vbar, Fix(2L), Fix(1L), Char('|')]),
      list([Fix(0L), Fix(0L)]),
    ]),
  )
  set(
    q_d__sumsign_unicode_dmstr,
    list([
      list([Fix(0L), Fix(2L), list([q_d__hbar, Fix(4L), u("low-line")])]),
      list([
        Fix(-4L),
        Fix(1L),
        u("box-drawings-light-diagonal-upper-left-to-lower-right"),
      ]),
      u("mathematical-right-angle-bracket"),
      list([
        Fix(-2L),
        Fix(-1L),
        u("box-drawings-light-diagonal-upper-right-to-lower-left"),
      ]),
      list([Fix(-1L), Fix(-2L), list([q_d__hbar, Fix(4L), u("overline")])]),
    ]),
  )
  |> ignore
  defvar_init(
    q_d__sumsign_ascii_dmstr,
    list([
      list([Fix(0L), Fix(2L), list([q_d__hbar, Fix(4L), Char('_')])]),
      list([Fix(-4L), Fix(1L), Char('\\')]),
      Char('>'),
      list([Fix(-2L), Fix(-1L), Char('/')]),
      list([Fix(-1L), Fix(-2L), list([q_d__hbar, Fix(4L), Char('-')])]),
    ]),
  )
  defvar_init(q_d__matrix_char_unicode_horz, u("box-drawings-light-horizontal"))
  defvar_init(q_d__matrix_char_unicode_vert, u("box-drawings-light-vertical"))
  defvar_init(
    q_d__matrix_char_unicode_upper_left,
    u("box-drawings-light-down-and-right"),
  )
  defvar_init(
    q_d__matrix_char_unicode_upper_right,
    u("box-drawings-light-down-and-left"),
  )
  defvar_init(
    q_d__matrix_char_unicode_lower_right,
    u("box-drawings-light-up-and-left"),
  )
  defvar_init(
    q_d__matrix_char_unicode_lower_left,
    u("box-drawings-light-up-and-right"),
  )
  displa__def(q_bigfloat, q_dim_bigfloat)
  displa__def(q_p_bigfloat, q_dim_bigfloat)
  displa__def(q_mquote, q_dimension_prefix, l_dissym="'")
  displa__def(q_p_mquote, q_dimension_prefix, l_dissym="'")
  displa__def(q_msetq, q_dimension_infix, l_dissym=" : ")
  displa__def(q_p_msetq, q_dimension_infix, l_dissym=" : ")
  displa__def(q_mset, q_dimension_infix, l_dissym=" :: ")
  displa__def(q_p_mset, q_dimension_infix, l_dissym=" :: ")
  displa__def(q_mdefine, q_dim_mdefine, l_dissym=" := ")
  displa__def(q_p_mdefine, q_dim_mdefine, l_dissym=" := ")
  displa__def(q_mdefmacro, q_dim_mdefine, l_dissym=" ::= ")
  displa__def(q_p_mdefmacro, q_dim_mdefine, l_dissym=" ::= ")
  displa__def(q_mfactorial, q_dimension_postfix, l_dissym="!")
  displa__def(q_p_mfactorial, q_dimension_postfix, l_dissym="!")
  displa__def(q_mexpt, q_dimension_superscript)
  displa__def(q_p_mexpt, q_dimension_superscript)
  displa__def(q_mncexpt, q_dim_mncexpt, l_dissym="^^")
  displa__def(q_p_mncexpt, q_dim_mncexpt, l_dissym="^^")
  displa__def(q_mnctimes, q_dimension_nary, l_dissym=" . ")
  displa__def(q_p_mnctimes, q_dimension_nary, l_dissym=" . ")
  displa__def(q_p_product, q_dim__pctproduct, bp=[115])
  displa__def(q_rat, q_dim_rat, l_dissym="/")
  displa__def(q_p_rat, q_dim_rat, l_dissym="/")
  displa__def(q_mquotient, q_dim_mquotient, l_dissym="/")
  displa__def(q_p_mquotient, q_dim_mquotient, l_dissym="/")
  displa__def(q_mtimes, q_dimension_nary, l_dissym=" ")
  displa__def(q_p_mtimes, q_dimension_nary, l_dissym=" ")
  putprop(q_d_stardisp, q_stardisp, q_assign) |> ignore
  displa__def(q_p_integrate, q_dim__pctintegrate, bp=[115])
  displa__def(q_p_derivative, q_dim__pctderivative, bp=[125])
  displa__def(q_p_at, q_dim__pctat, bp=[105, 105])
  displa__def(q_mplus, q_dim_mplus)
  displa__def(q_p_mplus, q_dim_mplus)
  putprop(q_munaryplus, list([Char('+'), Char(' ')]), q_dissym) |> ignore
  displa__def(q_mminus, q_dim_mminus)
  displa__def(q_p_mminus, q_dim_mminus)
  putprop(q_munaryminus, list([Char('-'), Char(' ')]), q_dissym) |> ignore
  putprop(q_munaryminus, int(134), q_rbp) |> ignore
  putprop(q_munaryminus, int(100), q_rbp) |> ignore
  displa__def(q_p_sum, q_dim__pctsum, bp=[110])
  displa__def(q_p_limit, q_dim__pctlimit, bp=[110, 110])
  displa__def(q_p_lsum, q_dim__pctlsum, bp=[110])
  displa__def(q_marrow, q_dimension_infix, l_dissym=" -> ", bp=[80, 80])
  displa__def(q_p_marrow, q_dimension_infix, l_dissym=" -> ", bp=[80, 80])
  displa__def(q_mgreaterp, q_dimension_infix, l_dissym=" > ")
  displa__def(q_p_mgreaterp, q_dimension_infix, l_dissym=" > ")
  displa__def(q_mgeqp, q_dimension_infix, l_dissym=" >= ")
  displa__def(q_p_mgeqp, q_dimension_infix, l_dissym=" >= ")
  displa__def(q_mequal, q_dimension_infix, l_dissym=" = ")
  displa__def(q_p_mequal, q_dimension_infix, l_dissym=" = ")
  displa__def(q_mnotequal, q_dimension_infix, l_dissym=" # ")
  displa__def(q_p_mnotequal, q_dimension_infix, l_dissym=" # ")
  displa__def(q_mleqp, q_dimension_infix, l_dissym=" <= ")
  displa__def(q_p_mleqp, q_dimension_infix, l_dissym=" <= ")
  displa__def(q_mlessp, q_dimension_infix, l_dissym=" < ")
  displa__def(q_p_mlessp, q_dimension_infix, l_dissym=" < ")
  displa__def(q_mnot, q_dimension_prefix, l_dissym="not ")
  displa__def(q_p_mnot, q_dimension_prefix, l_dissym="not ")
  displa__def(q_mand, q_dimension_nary, l_dissym=" and ")
  displa__def(q_p_mand, q_dimension_nary, l_dissym=" and ")
  putprop(q_mand, q_dimnary_boolean, q_dimension_nary_helper) |> ignore
  displa__def(q_mor, q_dimension_nary, l_dissym=" or ")
  displa__def(q_p_mor, q_dimension_nary, l_dissym=" or ")
  putprop(q_mor, q_dimnary_boolean, q_dimension_nary_helper) |> ignore
  displa__def(q_mcond, q_dim_mcond)
  displa__def(q_p_mcond, q_dim_mcond)
  displa__def(q_mdo, q_dim_mdo)
  displa__def(q_p_mdo, q_dim_mdo)
  displa__def(q_mdoin, q_dim_mdoin)
  displa__def(q_p_mdoin, q_dim_mdoin)
  displa__def(q_mprogn, q_dimension_match, l_dissym="(", r_dissym=")")
  displa__def(q_p_mprogn, q_dimension_match, l_dissym="(", r_dissym=")")
  displa__def(q_mlist, q_dimension_match, l_dissym="[", r_dissym="]")
  displa__def(q_p_mlist, q_dimension_match, l_dissym="[", r_dissym="]")
  displa__def(q_mangle, q_dimension_match, l_dissym="<", r_dissym=">")
  displa__def(q_p_mangle, q_dimension_match, l_dissym="<", r_dissym=">")
  displa__def(q_mcomma, q_dimension_nary, l_dissym=", ", bp=[10, 10])
  displa__def(q_p_mcomma, q_dimension_nary, l_dissym=", ", bp=[10, 10])
  displa__def(q_mabs, q_dim_mabs)
  displa__def(q_p_mabs, q_dim_mabs)
  displa__def(q_d_matrix, q_dim__dolmatrix)
  displa__def(q_p_matrix, q_dim__dolmatrix)
  displa__def(q_p_determinant, q_dim_determinant)
  displa__def(q_mbox, q_dim_mbox_or_mlabox)
  displa__def(q_p_mbox, q_dim_mbox_or_mlabox)
  displa__def(q_mlabox, q_dim_mlabox)
  displa__def(q_p_mlabox, q_dim_mlabox)
  displa__def(q_mtext, q_dim_mtext, bp=[1, 1])
  displa__def(q_p_mtext, q_dim_mtext, bp=[1, 1])
  putprop(q_mtext, q_dimnary_mtext, q_dimension_nary_helper) |> ignore
  displa__def(q_mlabel, q_dim_mlabel, bp=[0, 0])
  displa__def(q_p_mlabel, q_dim_mlabel, bp=[0, 0])
  // backwards-compatibility for wxMaxima
  setf_get(q_mlabel, q_wxxml, q_wxxml_mlable) |> ignore
  putprop(q_mparen, int(-1), q_lbp) |> ignore
  putprop(q_mparen, int(-1), q_rbp) |> ignore
}
