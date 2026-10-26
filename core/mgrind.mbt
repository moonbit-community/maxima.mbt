// Port of src/mgrind.lisp: the sizing printer used for 1-D output
// (grind, string, display2d:false). MSIZE builds a tree
//   (<width> . <items>)
// whose leaves are characters; MPRINT/STRPRINT walk it, breaking lines
// when an item does not fit in the remaining line width.
//
// LOP and ROP are special variables: MSIZE binds them, and the grind
// functions (msize-prefix, msize-infix, ...) read them freely.

///|
fn mgrind__int(v : Value) -> Int raise {
  to_int(v)
}

///|
fn mgrind__chrps() -> Int raise {
  to_int(symval(q_ear_chrps))
}

///|
fn mgrind__set_chrps(n : Int) -> Unit {
  set(q_ear_chrps, int(n)) |> ignore
}

///|
fn mgrind__linel() -> Int raise {
  to_int(symval(q_d_linel))
}

///|
/// `(chrct*)` as a MoonBit Int.
fn mgrind__chrct() -> Int raise {
  mgrind__linel() - mgrind__chrps()
}

///|
/// Characters of a MoonBit string as a fresh Lisp list.
fn mgrind__chars(s : String) -> Value {
  let c = Collector::new()
  for ch in s {
    c.add(Char(ch))
  }
  c.result()
}

///|
fn chrct_star() -> Value raise {
  int(mgrind__chrct())
}

///|
fn mtyotbsp(n : Value, out : Value) -> Value raise {
  let mut n = to_int(n)
  mgrind__set_chrps(mgrind__chrps() + n)
  while n >= 1 {
    write_char(' ', stream=out)
    n -= 1
  }
  Nil
}

///|
/// Format a Maxima `do' form (mdo) as a flat keyword-tagged list.
fn strmdo(x : Value) -> Value raise {
  let parts : Array[Value] = []
  if second(x).truthy() {
    parts.push(list([q_d_for, second(x)]))
  }
  if equal(Fix(1L), third(x)) {
    ()
  } else if third(x).truthy() {
    parts.push(list([q_d_from, third(x)]))
  }
  if equal(Fix(1L), fourth(x)) {
    ()
  } else if fourth(x).truthy() {
    parts.push(list([q_d_step, fourth(x)]))
  } else if fifth(x).truthy() {
    parts.push(list([q_d_next, fifth(x)]))
  }
  if nth(5, x).truthy() {
    parts.push(list([q_d_thru, nth(5, x)]))
  }
  let s7 = nth(6, x)
  if s7 is Nil {
    ()
  } else if consp(s7) && eq(caar(s7), q_mnot) {
    parts.push(list([q_d_while, cadr(s7)]))
  } else {
    parts.push(list([q_d_unless, s7]))
  }
  parts.push(list([q_d_do, nth(7, x)]))
  nconc_n(parts)
}

///|
/// Format a Maxima `do in' form (mdoin) as a flat keyword-tagged list.
fn strmdoin(x : Value) -> Value raise {
  let parts : Array[Value] = [list([q_d_for, second(x), q_d_in, third(x)])]
  if nth(5, x).truthy() {
    parts.push(list([q_d_thru, nth(5, x)]))
  }
  let s7 = nth(6, x)
  if s7 is Nil {
    ()
  } else if consp(s7) && eq(caar(s7), q_mnot) {
    parts.push(list([q_d_while, cadr(s7)]))
  } else {
    parts.push(list([q_d_unless, s7]))
  }
  parts.push(list([q_d_do, nth(7, x)]))
  nconc_n(parts)
}

///|
fn nformat_check(form : Value) -> Value raise {
  if symval(q_d_display_format_internal).truthy() &&
    !(atom(form) || atom(car(form)) || specrepp(form).truthy()) {
    form
  } else {
    nformat(form)
  }
}

///|
/// Convert ATOM to a list of characters suitable for printing.
fn makestring(atom_ : Value) -> Value raise {
  if numberp(atom_) {
    return exploden(atom_)
  }
  match atom_ {
    Str(s) => {
      let dummy = mgrind__chars(s)
      if symval(q_d_stringdisp).truthy() {
        return cons(Char('"'), nconc(dummy, list1(Char('"'))))
      } else {
        return dummy
      }
    }
    _ => ()
  }
  if !symbolp(atom_) {
    return exploden(atom_)
  }
  let dummy = get(atom_, q_reversealias)
  if dummy.truthy() &&
    !(memq(atom_, symval(q_d_aliases)).truthy() && get(atom_, q_noun).truthy()) {
    return exploden(stripdollar(dummy))
  }
  if !eq(getop(atom_), atom_) {
    return makestring(getop(atom_))
  }
  let dummy = exploden(atom_)
  match dummy {
    Nil => Nil
    Cons({ car: Char('$'), cdr }) => cdr
    Cons({ car: Char('%'), cdr }) => cdr
    _ =>
      if symval(q_d_lispdisp).truthy() {
        cons(Char('?'), dummy)
      } else {
        dummy
      }
  }
}

///|
fn mgrind(x : Value, out : Value) -> Value raise {
  mgrind__set_chrps(0)
  mprint(msize(x, Nil, Nil, q_mparen, q_mparen), out)
}

///|
fn mprint(x : Value, out : Value) -> Value raise {
  if x is Char(c) {
    mgrind__set_chrps(mgrind__chrps() + 1)
    write_char(c, stream=out)
    return Nil
  }
  if mgrind__int(car(x)) < mgrind__chrct() {
    for l in cdr(x).iter() {
      mprint(l, out) |> ignore
    }
    return Nil
  }
  let mut i = mgrind__chrps()
  mprint(cadr(x), out) |> ignore
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
    mprint(caddr(x), out) |> ignore
  } else {
    i = i + 1
    mgrind__set_chrps(0)
    terpri(stream=out)
    mtyotbsp(int(i), out) |> ignore
    mprint(caddr(x), out) |> ignore
  }
  let mut l = cdddr(x)
  while l is Cons(_) {
    if atom(car(l)) || mgrind__int(caar(l)) < mgrind__chrct() {
      ()
    } else {
      mgrind__set_chrps(0)
      terpri(stream=out)
      mtyotbsp(int(i), out) |> ignore
    }
    mprint(car(l), out) |> ignore
    l = cdr(l)
  }
  Nil
}

///|
fn msize(x : Value, l : Value, r : Value, lop : Value, rop : Value) -> Value raise {
  with_specials([(q_lop, lop), (q_rop, rop)], () => {
    let mut x = nformat_check(x)
    if atom(x) {
      return msize_atom(x, l, r)
    }
    if atom(car(x)) {
      x = cons(list1(q_mprogn), x)
    }
    let op = caar(x)
    if num_le(lbp(op), rbp(lop)) || num_ge(lbp(rop), rbp(op)) {
      msize_paren(x, l, r)
    } else if memq(q_array, cdar(x)).truthy() {
      msize_array(x, l, r)
    } else if safe_get(op, q_grind).truthy() {
      funcall(get(op, q_grind), [x, l, r])
    } else {
      msize_function(x, l, r, Nil)
    }
  })
}

///|
fn msize_atom(x : Value, l : Value, r : Value) -> Value raise {
  let mut y : Value = Nil
  if numberp(x) {
    y = exploden(x)
  } else if x is Str(s) {
    // Escape double quotes and backslashes.
    let c = Collector::new()
    for ch in s {
      if ch == '"' || ch == '\\' {
        c.add(Char('\\'))
      }
      c.add(Char(ch))
    }
    y = cons(Char('"'), nconc(c.result(), list1(Char('"'))))
  } else {
    y = safe_get(x, q_reversealias)
    if y.truthy() &&
      !(memq(x, symval(q_d_aliases)).truthy() && get(x, q_noun).truthy()) {
      y = exploden(stripdollar(y))
    } else {
      y = exploden(x)
      if y is Nil {
        ()
      } else if safe_get(x, q_noun).truthy() {
        return msize_atom(get(x, q_noun), l, r)
      } else if car(y) is Char('$') {
        y = slash(cdr(y))
      } else if memq(marray_type(x), list([q_array, q_hash_table, q_d_functional])).truthy() {
        return msize_array_object(x, l, r)
      } else {
        y = if symval(q_d_lispdisp).truthy() {
          cons(Char('?'), slash(y))
        } else {
          slash(y)
        }
      }
    }
  }
  msz(y, l, r)
}

///|
fn msize_paren(x : Value, l : Value, r : Value) -> Value raise {
  msize(x, cons(Char('('), l), cons(Char(')'), r), q_mparen, q_mparen)
}

///|
fn msize_array(x : Value, l : Value, r : Value) -> Value raise {
  let mut x = x
  let mut l = l
  let f = if eq(caar(x), q_mqapply) {
    let f = cadr(x)
    x = cdr(x)
    f
  } else {
    caar(x)
  }
  if atom(car(x)) {
    ()
  } else if symbolp(caar(x)) &&
    get(caar(x), q_verb).truthy() &&
    get(caar(x), q_alias).truthy() {
    l = revappend(list([Char('\''), Char('\'')]), l)
  } else if symbolp(caar(x)) &&
    get(caar(x), q_noun).truthy() &&
    !memq(caar(x), cdr(symval(q_d_aliases))).truthy() &&
    !get(caar(x), q_reversealias).truthy() {
    l = cons(Char('\''), l)
  }
  let l = msize(f, l, list1(symval(q_ear_lb)), symval(q_lop), q_mfunction)
  let r = msize_list(cdr(x), Nil, cons(symval(q_ear_rb), r))
  cons(num_add(car(l), car(r)), cons(l, cdr(r)))
}

///|
fn msize_function(x : Value, l : Value, r : Value, op : Value) -> Value raise {
  let mut l = l
  if !symbolp(caar(x)) {
    ()
  } else if get(caar(x), q_verb).truthy() && get(caar(x), q_alias).truthy() {
    l = revappend(list([Char('\''), Char('\'')]), l)
  } else if get(caar(x), q_noun).truthy() &&
    !memq(caar(x), cdr(symval(q_d_aliases))).truthy() &&
    !get(caar(x), q_reversealias).truthy() {
    l = cons(Char('\''), l)
  }
  let l = msize(
    if op.truthy() {
      getop(caar(x))
    } else {
      caar(x)
    },
    l,
    list1(Char('(')),
    q_mparen,
    q_mparen,
  )
  let r = msize_list(cdr(x), Nil, cons(Char(')'), r))
  cons(num_add(car(l), car(r)), cons(l, cdr(r)))
}

///|
fn msize_list(x : Value, l : Value, r : Value) -> Value raise {
  if x is Nil {
    return msz(Nil, l, r)
  }
  let mut x = x
  let mut l = l
  let mut nl : Value = Nil
  let mut w = 0
  while true {
    if cdr(x) is Nil {
      nl = cons(msize(car(x), l, r, q_mparen, q_mparen), nl)
      return cons(int(w + mgrind__int(caar(nl))), nreverse(nl))
    }
    nl = cons(msize(car(x), l, list1(Char(',')), q_mparen, q_mparen), nl)
    w = w + mgrind__int(caar(nl))
    x = cdr(x)
    l = Nil
  }
  Nil
}

///|
fn msize_prefix(x : Value, l : Value, r : Value) -> Value raise {
  msize(cadr(x), revappend(strsym(caar(x)), l), r, caar(x), symval(q_rop))
}

///|
fn msize_infix(x : Value, l : Value, r : Value) -> Value raise {
  if length(cdr(x)) != 2 {
    return msize_function(x, l, r, t)
  }
  let l = msize(cadr(x), l, Nil, symval(q_lop), caar(x))
  let r = msize(caddr(x), reverse(strsym(caar(x))), r, caar(x), symval(q_rop))
  list([num_add(car(l), car(r)), l, r])
}

///|
fn msize_postfix(x : Value, l : Value, r : Value) -> Value raise {
  msize(cadr(x), l, append(strsym(caar(x)), r), symval(q_lop), caar(x))
}

///|
fn msize_nary(x : Value, l : Value, r : Value) -> Value raise {
  msznary(x, l, r, strsym(caar(x)))
}

///|
fn msize_nofix(x : Value, l : Value, r : Value) -> Value raise {
  msize(caar(x), l, r, caar(x), symval(q_rop))
}

///|
fn msize_matchfix(x : Value, l : Value, r : Value) -> Value raise {
  let ss = strsym(caar(x))
  let l = nreconc(l, car(ss))
  let l = cons(int(length(l)), l)
  let r = append(cdr(ss), r)
  let x = msize_list(cdr(x), Nil, r)
  cons(num_add(car(l), car(x)), cons(l, cdr(x)))
}

///|
fn msize_mlabel(x : Value, l : Value, r : Value) -> Value raise {
  let mut l = l
  if symval(q_ear_display_labels_p).truthy() {
    l = cons(
      msize(
        cadr(x),
        list1(Char('(')),
        list([Char(')'), Char(' ')]),
        Nil,
        Nil,
      ),
      l,
    )
  }
  msize(caddr(x), l, r, symval(q_lop), symval(q_rop))
}

///|
fn msize_mtext(x : Value, l : Value, r : Value) -> Value raise {
  let mut x = cdr(x)
  if x is Nil {
    return msz(Nil, l, r)
  }
  let mut l = l
  let mut nl : Value = Nil
  let mut w = 0
  let item = (e : Value, l : Value, r : Value) => if stringp(e) {
    msz(makestring(e), l, r)
  } else {
    msize(e, l, r, symval(q_lop), symval(q_rop))
  }
  while true {
    if cdr(x) is Nil {
      nl = cons(item(car(x), l, r), nl)
      return cons(int(w + mgrind__int(caar(nl))), nreverse(nl))
    }
    nl = cons(item(car(x), l, r), nl)
    w = w + mgrind__int(caar(nl))
    x = cdr(x)
    l = Nil
  }
  Nil
}

///|
/// SPACEOUT appears solely in trace output. See mtrace.lisp.
fn msize_spaceout(x : Value, ll : Value, r : Value) -> Value raise {
  ignore(ll)
  ignore(r)
  let n = to_int(cadr(x))
  let mut l : Value = Nil
  for i = 0; i < n; i = i + 1 {
    l = cons(Char(' '), l)
  }
  cons(int(n), l)
}

///|
/// If X, the operand of a unary minus, is a product or quotient whose
/// leftmost factor is an atom or binds more tightly than "-" (possibly inside
/// further products and quotients), return X with the minus moved onto that
/// factor, else NIL.
fn mminus_onto_leftmost_factor(x : Value) -> Value raise {
  let x = nformat_check(x)
  if consp(x) &&
    consp(car(x)) &&
    (
      (eq(caar(x), q_mtimes) && cddr(x).truthy()) ||
      (memq(caar(x), list([q_mquotient, q_rat])).truthy() && length(x) == 3)
    ) {
    let y = nformat_check(cadr(x))
    let z = if atom(y) {
      list([list1(q_mminus), y])
    } else if !consp(car(y)) {
      Nil
    } else if memq(caar(y), list([q_mtimes, q_mquotient, q_rat])).truthy() {
      mminus_onto_leftmost_factor(y)
    } else if num_gt(lbp(caar(y)), rbp(q_d_op_)) {
      list([list1(q_mminus), y])
    } else {
      Nil
    }
    if z.truthy() {
      list_star([list1(caar(x)), z, cddr(x)])
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn msize_mminus(x : Value, l : Value, r : Value) -> Value raise {
  if cddr(x) is Nil {
    if cdr(x) is Nil {
      return msize_function(x, l, r, t)
    }
    // Without simplification, the minus stays where it is, so that the
    // expression reads back unchanged.
    let y = if symval(q_d_simp).truthy() {
      mminus_onto_leftmost_factor(cadr(x))
    } else {
      Nil
    }
    if y.truthy() {
      return msize(y, l, r, symval(q_lop), symval(q_rop))
    } else {
      return msize(cadr(x), append(list1(Char('-')), l), r, q_mminus, symval(q_rop))
    }
  }
  let l0 = msize(cadr(x), l, Nil, symval(q_lop), q_mminus)
  let mut x = cddr(x)
  let mut nl = list1(l0)
  let mut w = mgrind__int(car(l0))
  while true {
    let (l1, dissym) = if mmminusp(car(x)).truthy() {
      (cadar(x), list1(Char('+')))
    } else {
      (car(x), list1(Char('-')))
    }
    if cdr(x) is Nil {
      let r = msize(l1, dissym, r, q_mminus, symval(q_rop))
      return cons(int(mgrind__int(car(r)) + w), nreverse(cons(r, nl)))
    }
    nl = cons(msize(l1, dissym, Nil, q_mminus, q_mminus), nl)
    w = mgrind__int(caar(nl)) + w
    x = cdr(x)
  }
  Nil
}

///|
fn msize_text_string(x : Value, ll : Value, r : Value) -> Value raise {
  ignore(ll)
  ignore(r)
  cons(int(length(cdr(x))), cdr(x))
}

///|
fn msz(x : Value, l : Value, r : Value) -> Value raise {
  let x = nreconc(l, nconc(x, r))
  cons(int(length(x)), x)
}

///|
fn msznary(x : Value, l : Value, r : Value, dissym : Value) -> Value raise {
  if cddr(x) is Nil {
    return msize_function(x, l, r, t)
  }
  let l = msize(cadr(x), l, Nil, symval(q_lop), caar(x))
  let mut ol = cddr(x)
  let mut nl = list1(l)
  let mut w = mgrind__int(car(l))
  while true {
    if cdr(ol) is Nil {
      let r = msize(car(ol), reverse(dissym), r, caar(x), symval(q_rop))
      return cons(int(mgrind__int(car(r)) + w), nreverse(cons(r, nl)))
    }
    nl = cons(msize(car(ol), reverse(dissym), Nil, caar(x), caar(x)), nl)
    w = mgrind__int(caar(nl)) + w
    ol = cdr(ol)
  }
  Nil
}

///|
fn msz_bigfloat(x : Value, l : Value, r : Value) -> Value raise {
  msz(mapcar(c => get_first_char(c), fpformat(x)), l, r)
}

///|
fn msz_mqapply(x : Value, l : Value, r : Value) -> Value raise {
  let l = msize(cadr(x), l, list1(Char('(')), symval(q_lop), q_mfunction)
  let r = msize_list(cddr(x), Nil, cons(Char(')'), r))
  cons(num_add(car(l), car(r)), cons(l, cdr(r)))
}

///|
fn msz_mdef(x : Value, l : Value, r : Value) -> Value raise {
  let l = msize(cadr(x), l, copy_list(strsym(caar(x))), symval(q_lop), caar(x))
  let mut r = msize(caddr(x), Nil, r, caar(x), symval(q_rop))
  if !atom(cadr(l)) {
    // An expression like g(x):=x:
    //   left side  l = (6 (2 #\g #\( ) (4 #\x #\) #\: #\= ))
    //   right side r = (1 #\x )
    // the result is (7 (2 #\g #\( ) (4 #\x #\) #\: #\= ) (1 #\x ))
    let mut x = cons(num_sub(car(l), caadr(l)), cddr(l))
    if !atom(cadr(r)) &&
      !atom(caddr(r)) &&
      mgrind__int(car(l)) + mgrind__int(caadr(r)) + mgrind__int(caaddr(r)) <
      mgrind__linel() {
      x = nconc(x, list([cadr(r), caddr(r)]))
      r = cons(car(r), cdddr(r))
    }
    cons(num_add(car(l), car(r)), cons(cadr(l), cons(x, cdr(r))))
  } else {
    // An expression like x f :=x or f x:=x, where f is a postfix or a
    // prefix operator.
    cons(num_add(car(l), car(r)), cons(l, list1(r)))
  }
}

///|
fn msz_mexpt(x : Value, l : Value, r : Value) -> Value raise {
  let l = msize(cadr(x), l, Nil, symval(q_lop), q_mexpt)
  let x = nformat_check(caddr(x))
  let r = if mmminusp(x).truthy() {
    msize(cadr(x), list([Char('-'), Char('^')]), r, q_mexpt, symval(q_rop))
  } else {
    msize(x, list1(Char('^')), r, q_mexpt, symval(q_rop))
  }
  list([num_add(car(l), car(r)), l, r])
}

///|
fn msz_mtimes(x : Value, l : Value, r : Value) -> Value raise {
  msznary(x, l, r, list1(Char('*')))
}

///|
fn msz_mplus(x : Value, l : Value, r : Value) -> Value raise {
  if cddr(x) is Nil {
    if cdr(x) is Nil {
      return msize_function(x, l, r, t)
    }
    return msize(cadr(x), append(list1(Char('+')), l), r, q_mplus, symval(q_rop))
  }
  let l0 = msize(cadr(x), l, Nil, symval(q_lop), q_mplus)
  let mut x = cddr(x)
  let mut nl = list1(l0)
  let mut w = mgrind__int(car(l0))
  while true {
    let (l1, dissym) = if mmminusp(car(x)).truthy() {
      (cadar(x), list1(Char('-')))
    } else {
      (car(x), list1(Char('+')))
    }
    if cdr(x) is Nil {
      let r = msize(l1, dissym, r, q_mplus, symval(q_rop))
      return cons(int(mgrind__int(car(r)) + w), nreverse(cons(r, nl)))
    }
    nl = cons(msize(l1, dissym, Nil, q_mplus, q_mplus), nl)
    w = mgrind__int(caar(nl)) + w
    x = cdr(x)
  }
  Nil
}

///|
/// See comments above DIM-MCOND in displa.lisp concerning MCOND parsing and
/// formatting.
fn msz_mcond(x : Value, l : Value, r : Value) -> Value raise {
  let if_ = nreconc(l, list([Char('i'), Char('f'), Char(' ')]))
  let if_ = cons(int(length(if_)), if_)
  let l = msize(cadr(x), Nil, Nil, q_mcond, q_mparen)
  let mut args = cdddr(x)
  let else_literal = reverse(exploden(Str(" else ")))
  let elseif_literal = reverse(exploden(Str(" elseif ")))
  let then_literal = reverse(exploden(Str(" then ")))
  let sgra = reverse(args)
  if (car(sgra) is Nil || eq(car(sgra), q_d_false)) && eq(cadr(sgra), t) {
    args = reverse(cddr(sgra))
  }
  let mut parts = list([if_, l])
  let part = if length(args) == 0 {
    list1(msize(caddr(x), copy_tree(then_literal), r, q_mcond, symval(q_rop)))
  } else {
    list1(msize(caddr(x), copy_tree(then_literal), Nil, q_mcond, q_mparen))
  }
  parts = append(parts, part)
  while length(args) >= 2 {
    let maybe_elseif = car(args)
    let else_or_then = cadr(args)
    if length(args) == 2 {
      if eq(maybe_elseif, t) {
        let part = list1(
          msize(else_or_then, copy_tree(else_literal), r, q_mcond, symval(q_rop)),
        )
        parts = append(parts, part)
      } else {
        let a = msize(
          maybe_elseif,
          copy_tree(elseif_literal),
          Nil,
          q_mcond,
          q_mparen,
        )
        let b = msize(
          else_or_then,
          copy_tree(then_literal),
          r,
          q_mcond,
          symval(q_rop),
        )
        parts = append(parts, list([a, b]))
      }
    } else {
      let a = msize(
        maybe_elseif,
        copy_tree(elseif_literal),
        Nil,
        q_mcond,
        q_mparen,
      )
      let b = msize(else_or_then, copy_tree(then_literal), Nil, q_mcond, q_mparen)
      parts = append(parts, list([a, b]))
    }
    args = cddr(args)
  }
  let mut total = 0
  for p in parts.iter() {
    total = total + mgrind__int(car(p))
  }
  cons(int(total), parts)
}

///|
fn msz_mdo(x : Value, l : Value, r : Value) -> Value raise {
  msznary(cons(list1(q_mdo), strmdo(x)), l, r, list1(Char(' ')))
}

///|
fn msz_mdoin(x : Value, l : Value, r : Value) -> Value raise {
  msznary(cons(list1(q_mdo), strmdoin(x)), l, r, list1(Char(' ')))
}

///|
fn strsym(x : Value) -> Value raise {
  let s = get(x, q_strsym)
  if s.truthy() {
    s
  } else {
    get(x, q_dissym)
  }
}

///|
fn slash(x : Value) -> Value raise {
  if x is Nil {
    return Nil
  }
  // Following test is the same (except backslash is not included, so
  // backslash is preceded by backslash) as in SCAN-TOKEN (src/nparse.lisp).
  let mut l = cdr(x)
  while l is Cons(_) {
    if ascii_numberp(car(l)).truthy() || alphabetp(car(l)).truthy() {
      ()
    } else {
      rplacd(l, cons(car(l), cdr(l))) |> ignore
      rplaca(l, Char('\\')) |> ignore
      l = cdr(l)
    }
    l = cdr(l)
  }
  if alphabetp(car(x)).truthy() {
    x
  } else {
    cons(Char('\\'), x)
  }
}

///|
fn init_mgrind() -> Unit raise {
  let defprop = (s : Value, v : Value, p : Value) => putprop(s, v, p) |> ignore
  let chars = (s : String) => mgrind__chars(s)
  defprop(q_mquote, q_msize_prefix, q_grind)
  defprop(q_mnot, q_msize_prefix, q_grind)
  defprop(q_mnot, int(70), q_rbp)
  for e in [(q_msetq, ":"), (q_mset, "::")] {
    defprop(e.0, q_msize_infix, q_grind)
    defprop(e.0, chars(e.1), q_strsym)
    defprop(e.0, int(180), q_lbp)
    defprop(e.0, int(20), q_rbp)
  }
  defprop(q_mncexpt, q_msize_infix, q_grind)
  defprop(q_mncexpt, int(140), q_lbp)
  defprop(q_mncexpt, int(139), q_rbp)
  defprop(q_mquotient, q_msize_infix, q_grind)
  defprop(q_mquotient, int(120), q_lbp)
  defprop(q_mquotient, int(120), q_rbp)
  defprop(q_rat, q_msize_infix, q_grind)
  defprop(q_rat, int(120), q_lbp)
  defprop(q_rat, int(120), q_rbp)
  for op in [q_mequal, q_mnotequal, q_mgreaterp, q_mgeqp, q_mlessp, q_mleqp] {
    defprop(op, q_msize_infix, q_grind)
    defprop(op, int(80), q_lbp)
    defprop(op, int(80), q_rbp)
  }
  defprop(q_mfactorial, q_msize_postfix, q_grind)
  defprop(q_mfactorial, int(160), q_lbp)
  defprop(q_mfactorial, int(159), q_rbp)
  defprop(q_mnctimes, q_msize_nary, q_grind)
  defprop(q_mnctimes, int(130), q_lbp)
  defprop(q_mnctimes, int(129), q_rbp)
  defprop(q_mand, q_msize_nary, q_grind)
  defprop(q_mand, int(65), q_lbp)
  defprop(q_mand, int(65), q_rbp)
  defprop(q_mor, q_msize_nary, q_grind)
  defprop(q_mor, int(60), q_lbp)
  defprop(q_mor, int(60), q_rbp)
  defprop(q_mprogn, q_msize_matchfix, q_grind)
  defprop(q_mprogn, list([list1(Char('(')), Char(')')]), q_strsym)
  defprop(q_mlist, q_msize_matchfix, q_grind)
  setf_get(q_p_mlist, q_grind, get(q_mlist, q_grind)) |> ignore
  defprop(q_mlabel, q_msize_mlabel, q_grind)
  defprop(q_mtext, q_msize_mtext, q_grind)
  defprop(q_spaceout, q_msize_spaceout, q_grind)
  defprop(q_mminus, q_msize_mminus, q_grind)
  defprop(q_mminus, list1(Char('-')), q_strsym)
  defprop(q_mminus, int(134), q_rbp)
  defprop(q_mminus, int(100), q_lbp)
  defprop(q_text_string, q_msize_text_string, q_grind)
  defprop(q_bigfloat, q_msz_bigfloat, q_grind)
  defprop(q_mqapply, q_msz_mqapply, q_grind)
  defprop(q_mdefine, q_msz_mdef, q_grind)
  defprop(q_mdefine, chars(":="), q_strsym)
  defprop(q_mdefine, int(180), q_lbp)
  defprop(q_mdefine, int(20), q_rbp)
  // copy binding powers to nounified operator
  setf_get(q_p_mdefine, q_lbp, get(q_mdefine, q_lbp)) |> ignore
  setf_get(q_p_mdefine, q_rbp, get(q_mdefine, q_rbp)) |> ignore
  defprop(q_mdefmacro, q_msz_mdef, q_grind)
  defprop(q_mdefmacro, chars("::="), q_strsym)
  defprop(q_mdefmacro, int(180), q_lbp)
  defprop(q_mdefmacro, int(20), q_rbp)
  setf_get(q_p_mdefmacro, q_lbp, get(q_mdefmacro, q_lbp)) |> ignore
  setf_get(q_p_mdefmacro, q_rbp, get(q_mdefmacro, q_rbp)) |> ignore
  defprop(q_mexpt, q_msz_mexpt, q_grind)
  defprop(q_mexpt, int(140), q_lbp)
  defprop(q_mexpt, int(139), q_rbp)
  defprop(q_mtimes, q_msz_mtimes, q_grind)
  defprop(q_mtimes, int(120), q_lbp)
  defprop(q_mtimes, int(120), q_rbp)
  defprop(q_mplus, q_msz_mplus, q_grind)
  defprop(q_mplus, int(100), q_lbp)
  defprop(q_mplus, int(100), q_rbp)
  for op in [q_mcond, q_p_mcond] {
    defprop(op, q_msz_mcond, q_grind)
    defprop(op, int(45), q_lbp)
    defprop(op, int(45), q_rbp)
  }
  for op in [q_mdo, q_p_mdo] {
    defprop(op, q_msz_mdo, q_grind)
    defprop(op, int(25), q_lbp)
    defprop(op, int(25), q_rbp)
  }
  for op in [q_mdoin, q_p_mdoin] {
    defprop(op, q_msz_mdoin, q_grind)
    defprop(op, int(30), q_lbp)
    defprop(op, int(30), q_rbp)
  }
}
