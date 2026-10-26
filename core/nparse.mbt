// Port of src/nparse.lisp: the Maxima-language reader. A tokenizer reading
// characters from a Lisp stream, and a Pratt ("top down operator
// precedence") parser driven by NUD/LED/LBP/RBP/POS... properties on the
// operator symbols.
//
// NUD -- NUll left Denotation (op has nothing to its left (prefix))
// LED -- LEft Denotation      (op has something to left (postfix or infix))
// LBP -- Left Binding Power   (the stickiness to the left)
// RBP -- Right Binding Power  (the stickiness to the right)

///|
let nparse__q_nodisplayinput : Value = sym("nodisplayinput")

///|
/// Cache for `maxima_lit` (`#$...$` read-time literals).
let nparse__lit_cache : Map[String, Value] = Map([])

///|
fn nparse__chr(v : Value, c : Char) -> Bool {
  match v {
    Char(x) => x == c
    _ => false
  }
}

///|
fn nparse__cdaadr(x : Value) -> Value {
  cdr(car(car(cdr(x))))
}

///|
/// `(digit-char-p c (max 10 *read-base*))`
fn nparse__digitp_rb(v : Value) -> Bool {
  let rb = match symval(q_ear_read_base) {
    Fix(n) => n.to_int().max(10)
    _ => 10
  }
  match v {
    Char(c) => digit_char_p(c, radix=rb) is Some(_)
    _ => false
  }
}

///|
fn nparse__digitp(v : Value) -> Bool {
  match v {
    Char(c) => digit_char_p(c, radix=10) is Some(_)
    _ => false
  }
}

///|
fn nparse__eof() -> Value {
  symval(q_ear_parse_stream_eof)
}

///|
fn nparse__is_eof(c : Value) -> Bool {
  eql(c, nparse__eof())
}

///|
/// `(function f)` for a registered Lisp function.
fn nparse__fn(f : Value) -> Value raise {
  symbol_function(f)
}

///|
fn alphabetp(n : Value) -> Value raise {
  match n {
    Char(c) =>
      if alpha_char_p(c) {
        t
      } else {
        member(n, symval(q_ear_alphabet))
      }
    _ => Nil
  }
}

///|
fn ascii_numberp(num : Value) -> Value raise {
  match num {
    Char(c) => lbool(c >= '0' && c <= '9')
    _ => Nil
  }
}

///|
/// Maxima lets us refer to a Lisp symbol by prefixing it with "?"; the port
/// has no concatenated streams, so only `*standard-input*` itself counts.
fn parse_stream_standard_input_p(stream : Value) -> Value raise {
  lbool(eq(stream, symval(standard_input)))
}

///|
/// `(file-position stream)` for an input stream (nil if not applicable).
fn nparse__file_position(stream : Value) -> Value {
  match stream {
    Stream(s) => Fix((s.pos - s.unread.length()).to_int64())
    _ => Nil
  }
}

///|
/// The LINE-NUMBER local function of MREAD-SYNERR: rewind and find the line
/// (and column) of file position FP by reading line by line, leaving the
/// stream at the end of that line.
fn nparse__synerr_line_number(fp : Value) -> Value raise {
  match (fp, symval(q_ear_parse_stream)) {
    (Fix(fpos), Stream(s)) => {
      let fp = fpos.to_int()
      let input = s.input
      let len = input.length()
      s.unread.clear()
      let endpos = fn(start : Int) -> Int {
        if start >= len {
          len
        } else {
          let mut i = start
          while i < len && input[i] != '\n' {
            i += 1
          }
          if i < len {
            i + 1
          } else {
            len
          }
        }
      }
      let mut o = 1
      let mut p = endpos(0)
      let mut n = 1
      while p < fp && p < len {
        o = 1 + p
        p = endpos(p)
        n += 1
      }
      s.pos = p
      cons(int(n), int(fp - o))
    }
    _ => Nil
  }
}

///|
/// The COLUMN local function of MREAD-SYNERR: the characters of the current
/// line seen so far (at most the last 20).
fn nparse__synerr_column() -> Value raise {
  let n = to_int(get(q_ear_parse_window, q_length))
  let window = symval(q_ear_parse_window)
  let mut some : Value = Nil
  let mut i = n - 1
  while i >= n - 20 {
    let ch = nth(i, window)
    if ch is Nil {
      break
    }
    if nparse__is_eof(ch) || nparse__chr(ch, '\n') {
      return some
    }
    some = cons(ch, some)
    i -= 1
  }
  some
}

///|
fn mread_synerr(format_string : Value, l : Value) -> Value raise {
  let ps = symval(q_ear_parse_stream)
  let stdin_p = parse_stream_standard_input_p(ps).truthy()
  let fp = if !stdin_p { nparse__file_position(ps) } else { Nil }
  let file = if !stdin_p {
    cadr(symval(q_ear_current_line_info))
  } else {
    Nil
  }
  with_special(standard_output, symval(error_output), fn() raise {
    if file.truthy() && symval(q_d_report_synerr_line).truthy() {
      // print the file, line and column information
      let line_column = nparse__synerr_line_number(fp)
      fresh_line() |> ignore
      format(t, "~a:~a:~a:", [file, car(line_column), cdr(line_column)])
      |> ignore
    } else {
      // if file=nil, then print a fresh line only; otherwise print
      // file and character location
      fresh_line() |> ignore
      if file.truthy() {
        format(t, "~a:~a:", [file, fp]) |> ignore
      }
    }
    write_string(gettext("incorrect syntax: "))
    let printed = mapcar(
      fn(x) raise {
        if symbolp(x) {
          Str(princ_to_string(stripdollar(x)))
        } else if stringp(x) {
          maybe_invert_string_case(x)
        } else {
          x
        }
      },
      l,
    )
    format(t, lstring(format_string), list_to_array(printed)) |> ignore
    if symval(q_d_report_synerr_info).truthy() ||
      parse_stream_standard_input_p(symval(q_ear_parse_stream)).truthy() {
      let some = nparse__synerr_column()
      let sb = StringBuilder()
      sb.write_char('\n')
      for c in some.iter() {
        match c {
          Char(ch) => sb.write_char(ch)
          _ => ()
        }
      }
      sb.write_char('\n')
      // ~vT: move to column n (at least one space when already there)
      let col = if length(some) > 2 { length(some) - 2 } else { 0 }
      let pad = if col == 0 { 1 } else { col }
      for _ in 0..<pad {
        sb.write_char(' ')
      }
      sb.write_char('^')
      write_string(sb.to_string())
      read_line(stream=symval(q_ear_parse_stream)) |> ignore
    }
    terpri()
    finish_output()
  })
  if symval(q_ear_quit_on_error).truthy() {
    d_quit(exit_code=Fix(1L))
  } else {
    throw_macsyma_top()
  }
}

///|
fn tyi_parse_int(stream : Value, eof : Value) -> Value raise {
  if symval(q_ear_parse_window) is Nil {
    let w = list(Array::make(25, Nil))
    set(q_ear_parse_window, w) |> ignore
    putprop(q_ear_parse_window, int(length(w)), q_length) |> ignore
    setf_cdr(last(w), w) |> ignore
  }
  let tem = tyi(stream~, eof_option=eof)
  let w = symval(q_ear_parse_window)
  setf_car(w, tem) |> ignore
  set(q_ear_parse_window, cdr(w)) |> ignore
  if nparse__chr(tem, '\n') {
    newline(stream) |> ignore
  }
  tem
}

///|
fn ear_mread_prompt(out_stream : Value, char_ : Value) -> Value raise {
  ignore(char_)
  if out_stream is Nil {
    return format(Nil, "~A", [symval(q_ear_mread_prompt)])
  }
  fresh_line(stream=out_stream) |> ignore
  format(out_stream, "~A", [symval(q_ear_mread_prompt)])
}

///|
fn aliaslookup(op : Value) -> Value raise {
  if symbolp(op) {
    let a = get(op, q_alias)
    if a.truthy() {
      a
    } else {
      op
    }
  } else {
    op
  }
}

// ---------------------------------------------------------------------------
// Tokenizing: the input scanner

///|
fn gobble_whitespace() -> Value raise {
  while member(parse_tyipeek(), symval(q_ear_whitespace_chars)).truthy() {
    parse_tyi() |> ignore
  }
  Nil
}

///|
fn read_command_token(obj : Value) -> Value raise {
  gobble_whitespace() |> ignore
  read_command_token_aux(obj)
}

///|
/// maclisp would not complain about (car 3), it gives nil
fn safe_assoc(item : Value, lis : Value) -> Value raise {
  for v in lis.iter() {
    if consp(v) && equal(car(v), item) {
      return v
    }
  }
  Nil
}

///|
/// list contains an atom, only check
/// (parser-assoc 1 '(2 1 3)) ==>(1 3)
/// (parser-assoc 1 '(2 (1 4) 3)) ==>(1 4)
fn parser_assoc(c : Value, lis : Value) -> Value raise {
  let mut v = lis
  while consp(v) {
    let a = car(v)
    if consp(a) {
      if eq(car(a), c) {
        return a
      }
    } else if eql(a, c) {
      return v
    }
    v = cdr(v)
  }
  Nil
}

///|
/// we need to be able to unparse-tyi an arbitrary number of characters,
/// since if you do PREFIX("ABCDEFGH"); then ABCDEFGA should read as a symbol.
fn parse_tyi() -> Value raise {
  let tem = symval(q_ear_parse_tyi)
  if tem is Nil {
    tyi_parse_int(symval(q_ear_parse_stream), nparse__eof())
  } else if atom(tem) {
    set(q_ear_parse_tyi, Nil) |> ignore
    tem
  } else {
    set(q_ear_parse_tyi, cdr(tem)) |> ignore
    car(tem)
  }
}

///|
/// read one character but leave it there. so next parse-tyi gets it
fn parse_tyipeek() -> Value raise {
  let tem = symval(q_ear_parse_tyi)
  if tem is Nil {
    set(
      q_ear_parse_tyi,
      tyi_parse_int(symval(q_ear_parse_stream), nparse__eof()),
    )
  } else if atom(tem) {
    tem
  } else {
    car(tem)
  }
}

///|
/// push characters back on the stream
fn unparse_tyi(c : Value) -> Value raise {
  let tem = symval(q_ear_parse_tyi)
  if tem is Nil {
    set(q_ear_parse_tyi, c)
  } else {
    set(q_ear_parse_tyi, cons(c, tem))
  }
}

///|
/// When we have an operator which starts with a letter, check that the
/// operator is followed by whitespace, so that e.g. `grad x` parses as the
/// prefix operator grad but `gradef(x)` as the symbol gradef (bug #1925),
/// and %orb is read as a symbol even when %or is an operator.
fn operator_terminated_p(sym_ : Value) -> Value raise {
  let name = symbol_name(sym_)
  if name.length() < 2 {
    return t
  }
  if !alphabetp(Char(char_at(name, 1))).truthy() {
    return t
  }
  member(parse_tyipeek(), symval(q_ear_whitespace_chars))
}

///|
fn nparse__ans_of(x : Value) -> Value raise {
  if eql(car(x), q_ans) && operator_terminated_p(cadr(x)).truthy() {
    cadr(x)
  } else {
    Nil
  }
}

///|
fn read_command_token_aux(obj : Value) -> Value raise {
  let ch = parse_tyipeek()
  let lis : Value = if nparse__is_eof(ch) { Nil } else { parser_assoc(ch, obj) }
  if lis is Nil {
    return Nil
  }
  parse_tyi() |> ignore
  let result = if atom(cadr(lis)) {
    // INFIX("ABC"); puts into macsyma-operators something like:
    // (#\A #\B #\C (ANS $abc))
    // ordinary things are like: (#\< (ANS $<) (#\= (ANS $<=)))
    // where if you fail at the #\< #\X stage, then the previous step was
    // permitted.
    read_command_token_aux(list1(cdr(lis)))
  } else if cddr(lis) is Nil {
    // lis something like (#\= (ANS $<=)): no longer operators start with it
    nparse__ans_of(cadr(lis))
  } else {
    // An answer here and at least one longer operator starting with it.
    let res = nparse__ans_of(cadr(lis))
    let com_token = read_command_token_aux(cddr(lis))
    if com_token.truthy() {
      com_token
    } else if res.truthy() {
      res
    } else {
      read_command_token_aux(list1(cadr(lis)))
    }
  }
  if result is Nil {
    unparse_tyi(ch) |> ignore
  }
  result
}

///|
/// note that only $-ed tokens are GETALIASed.
fn scan_macsyma_token() -> Value raise {
  getalias(implode(cons(Char('$'), scan_token(t))))
}

///|
fn scan_lisp_token() -> Value raise {
  let charlist = scan_token(Nil)
  if charlist.truthy() {
    implode(charlist)
  } else {
    mread_synerr(Str("Lisp symbol expected."), Nil)
  }
}

///|
/// Example: ?mismatch(x+y,x*z,?:from\-end,true); => 3
fn scan_keyword_token() -> Value raise {
  let charlist = cdr(scan_token(Nil))
  if charlist.truthy() {
    kw(char_list_to_string(charlist))
  } else {
    mread_synerr(Str("Lisp keyword expected."), Nil)
  }
}

///|
fn scan_token(flag : Value) -> Value raise {
  let mut flag = flag.truthy()
  let mut l : Value = Nil
  while true {
    let c = parse_tyipeek()
    if nparse__is_eof(c) ||
      (
        flag &&
        !(
          nparse__digitp_rb(c) ||
          alphabetp(c).truthy() ||
          nparse__chr(c, '\\')
        )
      ) {
      // Read at least one char ...
      return nreverse(if l is Nil { list1(parse_tyi()) } else { l })
    }
    let mut c = c
    if nparse__chr(parse_tyi(), '\\') {
      c = parse_tyi()
    }
    flag = true
    l = cons(c, l)
  }
  Nil
}

///|
fn scan_lisp_string() -> Value raise {
  scan_string()
}

///|
fn scan_macsyma_string() -> Value raise {
  scan_string()
}

///|
fn scan_string(init_? : Value = Nil) -> Value raise {
  let buf = StringBuilder()
  match init_ {
    Char(c) => buf.write_char(c)
    _ => ()
  }
  while true {
    let c = parse_tyipeek()
    if nparse__is_eof(c) {
      break
    }
    if nparse__chr(c, '"') {
      parse_tyi() |> ignore
      break
    }
    let mut c = c
    if nparse__chr(parse_tyi(), '\\') {
      c = parse_tyi()
    }
    match c {
      Char(ch) => buf.write_char(ch)
      _ => ()
    }
  }
  Str(buf.to_string())
}

///|
fn readlist(lis : Value) -> Value raise {
  let s = char_list_to_string(lis)
  // CL reads an integer token (no trailing decimal point) in *read-base*.
  match symval(q_ear_read_base) {
    Fix(rb) if rb != 10L && !s.contains(".") =>
      match parse_integer(s, radix=rb.to_int()) {
        Some(v) => return v
        None =>
          // Not a number in this base: the CL reader makes it a symbol.
          if s.length() > 0 && s.iter().all(c => c.is_ascii_digit()) {
            return sym(s)
          }
      }
    _ => ()
  }
  match parse_number_token(s) {
    Some(v) => v
    None => lread(s)
  }
}

///|
fn nparse__exponent_marker_p(c : Value) -> Bool {
  match c {
    Char(
      'E' | 'e' | 'F' | 'f' | 'B' | 'b' | 'D' | 'd' | 'S' | 's' | 'L' | 'l'
    ) => true
    _ => false
  }
}

///|
fn nparse__number_markers(dot : Bool) -> Value {
  let cs = [
    'E', 'e', 'F', 'f', 'B', 'b', 'D', 'd', 'S', 's', 'L', 'l',
  ].map(c => Value::Char(c))
  if dot {
    cons(Char('.'), list(cs))
  } else {
    list(cs)
  }
}

///|
/// WARNING: MAKE-NUMBER destructively modifies its argument!
fn make_number(data : Value) -> Value raise {
  let data = nreverse(data)
  // Maxima really wants to read in any number as a flonum (except when we
  // have a bigfloat, of course!). So convert exponent markers to the
  // flonum-exponent-marker.
  let marker = car(nth(3, data))
  if !nparse__chr(marker, 'D') {
    match marker {
      Char('E' | 'F' | 'S' | 'D' | 'L') =>
        setf_car(nthcdr(3, data), list1(Char('D'))) |> ignore
      _ => ()
    }
  }
  if !equal(nth(3, data), list1(Char('B'))) {
    return readlist(append_n(list_to_array(data)))
  }
  let int_part = readlist(
    if first(data).truthy() {
      first(data)
    } else {
      list1(Char('0'))
    },
  )
  let frac_part = readlist(
    if third(data).truthy() {
      third(data)
    } else {
      list1(Char('0'))
    },
  )
  let frac_len = length(third(data))
  let exp_sign = first(fifth(data))
  let exp_ = readlist(nth(5, data))
  if symval(q_d_fast_bfloat_conversion).truthy() &&
    num_gt(num_abs(exp_), symval(q_d_fast_bfloat_threshold)) {
    // Exponent is large enough that we don't want to do exact rational
    // arithmetic. Instead we do bfloat arithmetic: 1.234b1000 is computed
    // as bfloat(1234)*10b0^(1000-3), with extra precision.
    let extra_prec = num_add(
      symval(q_ear_fast_bfloat_extra_bits),
      int(@math.ceil(dlog(to_double(exp_)) / dlog(2.0)).to_int()),
    )
    let result = with_special(
      q_fpprec,
      num_add(symval(q_fpprec), extra_prec),
      fn() raise {
        let mant = num_add(
          num_mul(int_part, expt(Fix(10L), int(frac_len))),
          frac_part,
        )
        let bf_mant = bcons(intofp(mant))
        let p = power(
          bcons(intofp(Fix(10L))),
          num_sub(
            if nparse__chr(exp_sign, '-') {
              num_neg(exp_)
            } else {
              exp_
            },
            int(frac_len),
          ),
        )
        // Compute the product using extra precision.
        mul2(bf_mant, p)
      },
    )
    // Now round the product back to the desired precision.
    with_special(q_fpprec, num_sub(symval(q_fpprec), extra_prec), fn() raise {
      bigfloatp(result)
    })
  } else {
    // For bigfloats, turn them into rational numbers then convert to
    // bigfloat. Fix for the 0.25b0 # 2.5b-1 bug (R. J. Fateman).
    let ratio = num_mul(
      num_add(
        int_part,
        num_mul(frac_part, expt(Fix(10L), int(-frac_len))),
      ),
      expt(
        Fix(10L),
        if nparse__chr(exp_sign, '-') {
          num_neg(exp_)
        } else {
          exp_
        },
      ),
    )
    d_bfloat(cl_rat_to_maxima(ratio))
  }
}

///|
fn cl_rat_to_maxima(x : Value) -> Value raise {
  if integerp(x) {
    x
  } else {
    list3(list2(q_rat, q_simp), numerator(x), denominator(x))
  }
}

///|
fn scan_digits(
  data : Value,
  continuation_q : Value,
  continuation : Value,
  exponent_p? : Value = Nil,
) -> Value raise {
  let mut l : Value = Nil
  while true {
    let c = parse_tyipeek()
    if !nparse__digitp_rb(c) {
      if member(c, continuation_q).truthy() {
        let ch = match parse_tyi() {
          Char(x) => Value::Char(char_upcase(x))
          v => v
        }
        return funcall(continuation, [list_star([list1(ch), nreverse(l), data])])
      } else if l is Nil && exponent_p.truthy() {
        // We're trying to parse the exponent part of a number, and we
        // didn't get a value after the exponent marker. That's an error.
        return mread_synerr(
          Str("parser: incomplete number; missing exponent?"),
          Nil,
        )
      } else {
        return make_number(cons(nreverse(l), data))
      }
    }
    parse_tyi() |> ignore
    l = cons(c, l)
  }
  Nil
}

///|
fn scan_number_after_dot(data : Value) -> Value raise {
  scan_digits(data, nparse__number_markers(false), q_scan_number_exponent)
}

///|
fn scan_number_exponent(data : Value) -> Value raise {
  let pk = parse_tyipeek()
  let sign = if nparse__chr(pk, '+') || nparse__chr(pk, '-') {
    parse_tyi()
  } else {
    Char('+')
  }
  scan_digits(cons(list1(sign), data), Nil, Nil, exponent_p=t)
}

// ---------------------------------------------------------------------------
// The expression parser
//
// Based on a theory of parsing presented in:
//   Pratt, Vaughan R., ``Top Down Operator Precedence,''
//   ACM Symposium on Principles of Programming Languages
//   Boston, MA; October, 1973.

///|
fn peek_one_token() -> Value raise {
  peek_one_token_g(Nil, Nil)
}

///|
fn peek_one_token_g(eof_ok_q : Value, eof_obj : Value) -> Value raise {
  let sbt = symval(q_scan_buffered_token)
  if car(sbt).truthy() {
    cdr(sbt)
  } else {
    rplacd(sbt, scan_one_token_g(eof_ok_q, eof_obj)) |> ignore
    cdr(rplaca(sbt, t))
  }
}

///|
fn scan_one_token() -> Value raise {
  scan_one_token_g(Nil, Nil)
}

///|
fn scan_one_token_g(eof_ok_q : Value, eof_obj : Value) -> Value raise {
  let sbt = symval(q_scan_buffered_token)
  if car(sbt).truthy() {
    rplaca(sbt, Nil) |> ignore
    return cdr(sbt)
  }
  let tok = read_command_token(symval(q_macsyma_operators))
  if tok.truthy() {
    return tok
  }
  let tst = parse_tyipeek()
  if nparse__is_eof(tst) {
    parse_tyi() |> ignore
    if eof_ok_q.truthy() {
      eof_obj
    } else {
      mread_synerr(Str("end of file while scanning expression."), Nil)
    }
  } else if nparse__chr(tst, '/') {
    parse_tyi() |> ignore
    if nparse__chr(parse_tyipeek(), '*') {
      parse_tyi() |> ignore
      gobble_comment() |> ignore
      scan_one_token_g(eof_ok_q, eof_obj)
    } else {
      q_d_op_sl
    }
  } else if nparse__chr(tst, '.') {
    parse_tyi() |> ignore // Read the dot
    if nparse__digitp(parse_tyipeek()) {
      scan_number_after_dot(list2(list1(Char('.')), Nil))
    } else {
      q_d_op_dot
    }
  } else if nparse__chr(tst, '"') {
    parse_tyi() |> ignore
    scan_macsyma_string()
  } else if nparse__chr(tst, '?') {
    parse_tyi() |> ignore
    let pk = parse_tyipeek()
    if nparse__chr(pk, '"') {
      parse_tyi() |> ignore
      scan_lisp_string()
    } else if nparse__chr(pk, ':') {
      scan_keyword_token()
    } else {
      scan_lisp_token()
    }
  } else if nparse__digitp(tst) {
    scan_number_before_dot(Nil)
  } else {
    scan_macsyma_token()
  }
}

///|
/// nested comments are permitted.
fn gobble_comment() -> Value raise {
  let mut depth = 1
  while true {
    let c = parse_tyipeek()
    parse_tyi() |> ignore
    if depth == 0 {
      return t
    }
    if nparse__is_eof(c) {
      mread_synerr(Str("end of file in comment."), Nil) |> ignore
    } else if nparse__chr(c, '*') {
      if nparse__chr(parse_tyipeek(), '/') {
        depth -= 1
        parse_tyi() |> ignore
        if depth == 0 {
          return t
        }
      }
    } else if nparse__chr(c, '/') {
      if nparse__chr(parse_tyipeek(), '*') {
        depth += 1
        parse_tyi() |> ignore
      }
    }
  }
  t
}

///|
fn scan_number_rest(data : Value) -> Value raise {
  let c = caar(data)
  if nparse__chr(c, '.') {
    // We found a dot
    scan_number_after_dot(data)
  } else if nparse__exponent_marker_p(c) {
    // Dot missing but found exponent marker.  Fake it.
    let mut data = cons(list1(Char('.')), rest(data))
    data = cons(list1(Char('0')), data)
    data = cons(list1(c), data)
    scan_number_exponent(data)
  } else {
    Nil
  }
}

///|
fn scan_number_before_dot(data : Value) -> Value raise {
  scan_digits(data, nparse__number_markers(true), q_scan_number_rest)
}

///|
/// "First character": `(peek-one-token)`
fn first_c() -> Value raise {
  peek_one_token()
}

///|
/// "Pop character": `(scan-one-token)`
fn pop_c() -> Value raise {
  scan_one_token()
}

///|
/// OBSOLETE. PRESERVE FOR SAKE OF POSSIBLE CALLS FROM NON-MAXIMA CODE !!
fn mstringp(x : Value) -> Value raise {
  lbool(stringp(x))
}

///|
fn inherit_propl(op_to : Value, op_from : Value, getl_ : Value) -> Value raise {
  let propl = getl(op_from, getl_)
  if propl.truthy() {
    remprop(op_to, car(propl)) |> ignore
    putprop(op_to, cadr(propl), car(propl))
  } else {
    inherit_propl(
      op_to,
      maxima_error(
        Str("has no ~a properties. ~a ~a"),
        list([getl_, op_from, q_wrng_type_arg]),
      ),
      getl_,
    )
  }
}

///|
/// `(def-nud-equiv op equiv)`
fn def_nud_equiv(op : Value, equiv : Value) -> Value raise {
  putprop(op, equiv, q_nud)
}

///|
fn nud_propl() -> Value raise {
  list1(q_nud)
}

///|
/// `(def-led-equiv op equiv)`
fn def_led_equiv(op : Value, equiv : Value) -> Value raise {
  putprop(op, equiv, q_led)
}

///|
fn led_propl() -> Value raise {
  list1(q_led)
}

///|
fn nud_call(op : Value) -> Value raise {
  let tem = if symbolp(op) { getl(op, list1(q_nud)) } else { Nil }
  if tem is Nil {
    if nparse__operatorp(op).truthy() {
      mread_synerr(Str("~A is not a prefix operator"), list1(mopstrip(op)))
    } else {
      cons(q_d_any, op)
    }
  } else {
    funcall(cadr(tem), [op])
  }
}

///|
fn led_call(op : Value, l : Value) -> Value raise {
  let tem = if symbolp(op) { getl(op, list1(q_led)) } else { Nil }
  if tem is Nil {
    mread_synerr(Str("~A is not an infix operator"), list1(mopstrip(op)))
  } else {
    funcall(cadr(tem), [op, l])
  }
}

///|
fn set_lbp_and_rbp(op : Value, lbp : Value, rbp : Value) -> Value raise {
  if !consp(op) {
    let existing_lbp = get(op, q_lbp)
    let existing_rbp = get(op, q_rbp)
    if lbp is Nil {
      // ignore omitted arg
      ()
    } else if existing_lbp is Nil {
      putprop(op, lbp, q_lbp) |> ignore
    } else if !equal(existing_lbp, lbp) {
      maxima_error(
        Str("Incompatible LBP's defined for this operator ~a"),
        list1(op),
      )
      |> ignore
    }
    if rbp is Nil {
      ()
    } else if existing_rbp is Nil {
      putprop(op, rbp, q_rbp) |> ignore
    } else if !equal(existing_rbp, rbp) {
      maxima_error(
        Str("Incompatible RBP's defined for this operator ~a"),
        list1(op),
      )
      |> ignore
    }
    Nil
  } else {
    mapcar(x => set_lbp_and_rbp(x, lbp, rbp), op)
  }
}

///|
/// `(def-collisions op . alist)`: give each keyword of a statement a bit, and
/// record on each keyword the bits of the keywords it collides with.
fn def_collisions(op : Value, alist : Value) -> Value raise {
  let mut keys : Value = Nil
  let mut i = 1L
  for d in alist.iter() {
    keys = cons(cons(car(d), Fix(i)), keys)
    i = i << 1
  }
  putprop(op, copy_tree(keys), q_keys) |> ignore
  for data in alist.iter() {
    let mut mask : Value = Fix(0L)
    for k in cdr(data).iter() {
      mask = logior(mask, cdr(assq(k, keys)))
    }
    putprop(car(data), mask, op) |> ignore
  }
  op
}

///|
fn collision_lookup(
  op : Value,
  active_bitmask : Value,
  key_bitmask : Value,
) -> Value raise {
  let result = logand(active_bitmask, key_bitmask)
  if !zerop(result) {
    let mut l = get(op, q_keys)
    while l.truthy() {
      if !zerop(logand(result, cdar(l))) {
        return caar(l)
      }
      l = cdr(l)
    }
    parse_bug_err(q_collision_check)
  } else {
    Nil
  }
}

///|
fn collision_check(op : Value, active_bitmask : Value, key : Value) -> Value raise {
  let key_bitmask = get(key, op)
  if key_bitmask is Nil {
    mread_synerr(
      Str("`~A' is an unknown keyword in a `~A' statement."),
      list2(mopstrip(key), mopstrip(op)),
    )
    |> ignore
  }
  let collision = collision_lookup(op, active_bitmask, key_bitmask)
  if collision.truthy() {
    if eq(collision, key) {
      mread_synerr(
        Str("The `~A' slot for `~A' is already filled."),
        list2(mopstrip(key), mopstrip(op)),
      )
      |> ignore
    } else {
      mread_synerr(
        Str("A `~A' cannot have a `~A' with a `~A' field."),
        list3(mopstrip(op), mopstrip(key), mopstrip(collision)),
      )
      |> ignore
    }
  }
  logior(cdr(assq(key, get(op, q_keys))), active_bitmask)
}

// Data abstraction

///|
/// LBP = Left Binding Power
fn lbp(lex : Value) -> Value raise {
  let v = safe_get(lex, q_lbp)
  if v.truthy() {
    v
  } else {
    Fix(200L)
  }
}

///|
fn def_lbp(sym_ : Value, val : Value) -> Value raise {
  putprop(sym_, val, q_lbp) |> ignore
  sym_
}

///|
/// RBP = Right Binding Power
fn rbp(lex : Value) -> Value raise {
  let v = safe_get(lex, q_rbp)
  if v.truthy() {
    v
  } else {
    Fix(200L)
  }
}

///|
fn def_rbp(sym_ : Value, val : Value) -> Value raise {
  putprop(sym_, val, q_rbp) |> ignore
  sym_
}

///|
fn def_match(x : Value, m : Value) -> Value raise {
  putprop(x, m, q_match) |> ignore
  x
}

///|
/// POS = Part of Speech!
fn lpos(op : Value) -> Value raise {
  let v = safe_get(op, q_lpos)
  if v.truthy() {
    v
  } else {
    q_d_any
  }
}

///|
fn rpos(op : Value) -> Value raise {
  let v = safe_get(op, q_rpos)
  if v.truthy() {
    v
  } else {
    q_d_any
  }
}

///|
fn pos(op : Value) -> Value raise {
  let v = safe_get(op, q_pos)
  if v.truthy() {
    v
  } else {
    q_d_any
  }
}

///|
fn def_pos(op : Value, pos : Value) -> Value raise {
  putprop(op, pos, q_pos) |> ignore
  op
}

///|
fn def_rpos(op : Value, pos : Value) -> Value raise {
  putprop(op, pos, q_rpos) |> ignore
  op
}

///|
fn def_lpos(op : Value, pos : Value) -> Value raise {
  putprop(op, pos, q_lpos) |> ignore
  op
}

///|
fn mheader(op : Value) -> Value raise {
  let h = safe_get(op, q_mheader)
  add_lineinfo(if h.truthy() { h } else { ncons(op) })
}

///|
fn def_mheader(op : Value, header : Value) -> Value raise {
  putprop(op, header, q_mheader) |> ignore
  op
}

///|
/// `(operatorp lex)`, defined by the DEF-OPERATORP macro.
fn nparse__operatorp(lex : Value) -> Value raise {
  if symbolp(lex) {
    getl(lex, list2(q_nud, q_led))
  } else {
    Nil
  }
}

///|
/// `(operatorp1 lex)`, defined by the DEF-OPERATORP1 macro. Use for truth
/// value only, not for return-value.
fn nparse__operatorp1(lex : Value) -> Value raise {
  if symbolp(lex) {
    getl(lex, list4(q_lbp, q_rbp, q_nud, q_led))
  } else {
    Nil
  }
}

///|
/// `(def-operatorp)`: defines the Lisp function OPERATORP.
fn def_operatorp() -> Value raise {
  defun(q_operatorp, args => nparse__operatorp(arg(args, 0)), name="operatorp")
  q_operatorp
}

///|
/// `(def-operatorp1)`: defines the Lisp function OPERATORP1.
fn def_operatorp1() -> Value raise {
  defun(
    q_operatorp1,
    args => nparse__operatorp1(arg(args, 0)),
    name="operatorp1",
  )
  q_operatorp1
}

// The Macsyma Parser

///|
/// (MREAD) with arguments compatible with losing maclisp READ style.
/// Returns a parsed form of tokens read from stream.
fn mread(read_args : Value) -> Value raise {
  let prompt = symval(q_ear_mread_prompt)
  if prompt.truthy() {
    let w = symval(q_ear_parse_window)
    if w.truthy() {
      setf_car(w, Nil) |> ignore
      set(q_ear_parse_window, cdr(w)) |> ignore
    }
    princ(prompt) |> ignore
    finish_output()
  }
  mread_raw(car(read_args), ear_mread_eof_obj=cadr(read_args))
}

///|
fn mread_prompter(stream : Value, char_ : Value) -> Value raise {
  ignore(char_)
  fresh_line(stream~) |> ignore
  princ(symval(q_ear_mread_prompt_internal), stream~)
}

///|
/// input can look like:
/// aa && bb && jim:3;
fn mread_raw(
  ear_parse_stream : Value,
  ear_mread_eof_obj? : Value = Nil,
) -> Value raise {
  with_specials(
    [
      (q_ear_parse_stream, ear_parse_stream),
      (q_ear_mread_eof_obj, ear_mread_eof_obj),
      (q_scan_buffered_token, list1(Nil)),
      (q_ear_parse_tyi, Nil),
    ],
    fn() raise {
      let sbt = symval(q_scan_buffered_token)
      // a handy unique object for the EQ test.
      if eq(sbt, peek_one_token_g(t, sbt)) {
        return symval(q_ear_mread_eof_obj)
      }
      let mut labels : Value = Nil
      while true {
        let input = parse(q_d_any, Fix(0L))
        let fc = first_c()
        if eq(fc, q_d_op_sc) || eq(fc, q_d_op_dol) {
          // force a separate line info structure
          set(q_ear_current_line_info, Nil) |> ignore
          let h = mheader(pop_c())
          let lab = if labels.truthy() {
            cons(mheader(q_d_op_lb), nreverse(labels))
          } else {
            Nil
          }
          return list3(h, lab, input)
        } else if eq(fc, q_d_op_amp_amp) {
          pop_c() |> ignore
          if symbolp(input) {
            labels = cons(input, labels)
          } else {
            mread_synerr(Str("Invalid && tag. Tag must be a symbol"), Nil)
            |> ignore
          }
        } else {
          parse_bug_err(q_mread_raw) |> ignore
        }
      }
      Nil
    },
  )
}

///|
/// (PARSE <mode> <rbp>)
///
/// Parse an expression containing operators which have a higher left
/// binding power than <rbp>, returning as soon as an operator of lesser or
/// equal binding power is seen. Modes: $ANY (any type), $CLAUSE (boolean
/// expressions), $EXPR (mathematical expressions). See CONVERT.
fn parse(mode : Value, rbp : Value) -> Value raise {
  let mut left = nud_call(pop_c()) // Invoke the null left denotation
  while true {
    // Until next op lbp too low
    if num_ge(rbp, lbp(first_c())) {
      return convert(left, mode)
    }
    // and keep calling LED ops as needed
    left = led_call(pop_c(), left)
  }
  Nil
}

///|
/// Parses prefix forms -- eg, -X or NOT FOO. Returns
/// ( <mode> . ((<op>) <arg1>) )
fn parse_prefix(op : Value) -> Value raise {
  let p = pos(op)
  let h = mheader(op)
  let a = parse(rpos(op), rbp(op))
  list3(p, h, a)
}

///|
/// Parses postfix forms. eg, X!.
fn parse_postfix(op : Value, l : Value) -> Value raise {
  let p = pos(op)
  let h = mheader(op)
  let a = convert(l, lpos(op))
  list3(p, h, a)
}

///|
/// Parses infix (non-nary) forms. eg, 5 mod 3.
fn parse_infix(op : Value, l : Value) -> Value raise {
  let p = pos(op)
  let h = mheader(op)
  let a1 = convert(l, lpos(op))
  let a2 = parse(rpos(op), rbp(op))
  list4(p, h, a1, a2)
}

///|
/// Parses nary forms. Eg, form1*form2*... or form1+form2+...
fn parse_nary(op : Value, l : Value) -> Value raise {
  let p = pos(op)
  let h = mheader(op)
  let a1 = convert(l, lpos(op))
  let rest_ = prsnary(op, lpos(op), lbp(op))
  list_star([p, h, a1, rest_])
}

///|
/// Parses matchfix forms. eg, [form1,form2,...] or (form1,form2,...)
fn parse_matchfix(op : Value) -> Value raise {
  let p = pos(op)
  let h = mheader(op)
  let r = prsmatch(safe_get(op, q_match), lpos(op))
  list_star([p, h, r])
}

///|
/// Parses an operator of no args.
fn parse_nofix(op : Value) -> Value raise {
  let p = pos(op)
  list2(p, mheader(op))
}

///|
/// Parses an nary operator tail Eg, ...form2+form3+...
fn prsnary(op : Value, mode : Value, rbp : Value) -> Value raise {
  let mut nl = list1(parse(mode, rbp)) // Get at least one form
  while eq(op, first_c()) {
    pop_c() |> ignore
    nl = cons(parse(mode, rbp), nl)
  }
  nreverse(nl)
}

///|
/// Parses a matchfix sequence. Eg, [form1,form2,...] or (form1,form2,...)
fn prsmatch(match_ : Value, mode : Value) -> Value raise {
  if eq(match_, first_c()) {
    pop_c() |> ignore
    return Nil
  }
  let mut nl = list1(parse(mode, Fix(10L)))
  while !eq(match_, first_c()) {
    if eq(q_d_op_cm, first_c()) {
      pop_c() |> ignore
    } else {
      mread_synerr(Str("Missing ~A"), list1(mopstrip(match_))) |> ignore
    }
    nl = cons(parse(mode, Fix(10L)), nl)
  }
  pop_c() |> ignore
  nreverse(nl)
}

///|
/// Parser coercion function: <item> is ( <expressionmode> . <expression> ).
fn convert(item : Value, mode : Value) -> Value raise {
  if eq(mode, car(item)) || eq(q_d_any, mode) || eq(q_d_any, car(item)) {
    cdr(item)
  } else {
    mread_synerr(
      Str("Found ~A expression where ~A expression expected"),
      list2(get(car(item), q_english), get(mode, q_english)),
    )
  }
}

// Parser error diagnostics

///|
fn parse_err() -> Value raise {
  mread_synerr(Str("Syntax error"), Nil)
}

///|
fn parse_bug_err(op : Value) -> Value raise {
  mread_synerr(
    Str(
      "Parser bug in ~A. Please report this to the Maxima maintainers,~\n   ~%including the characters you just typed which caused the error. Thanks.",
    ),
    list1(mopstrip(op)),
  )
}

///|
fn delim_err(op : Value) -> Value raise {
  mread_synerr(Str("Illegal use of delimiter ~A"), list1(mopstrip(op)))
}

///|
fn erb_err(op : Value, l : Value) -> Value raise {
  ignore(l)
  mread_synerr(Str("Too many ~A's"), list1(mopstrip(op)))
}

///|
fn premterm_err(op : Value) -> Value raise {
  mread_synerr(
    Str("Premature termination of input at ~A."),
    list1(mopstrip(op)),
  )
}

// Operator specific parse functions (DEF-NUD / DEF-LED bodies)

///|
/// (def-led (|$[| 200.) (op left) ...)
fn nparse__lb_led(op : Value, left : Value) -> Value raise {
  ignore(op)
  let left = convert(left, q_d_any)
  if numberp(left) {
    parse_err() |> ignore // number[...] invalid
  }
  let header = if atom(left) {
    add_lineinfo(list2(amperchk(left), q_array))
  } else {
    add_lineinfo(list2(q_mqapply, q_array))
  }
  let right = prsmatch(q_d_op_rb, q_d_any) // get sublist in RIGHT
  if right is Nil {
    // 1 subscript minimum
    mread_synerr(Str("No subscripts given"), Nil)
  } else if atom(left) {
    // atom[...]
    cons(q_d_any, aliaslookup(cons(header, right)))
  } else {
    // exp[...]
    cons(q_d_any, cons(header, cons(left, right)))
  }
}

///|
/// (def-nud (|$(| 200.) (op) ...)
/// This optimizes out (exp) into just exp.
fn nparse__lparen_nud(op : Value) -> Value raise {
  ignore(op)
  let hdr = mheader(q_d_op_u0028) // make mheader first for lineinfo
  if eq(q_d_op_u0029, first_c()) {
    return parse_err() // () is illegal
  }
  let right = prsmatch(q_d_op_u0029, q_d_any)
  if right is Nil || cdr(right).truthy() {
    // No args to MPROGN??, or more than one arg.
    if suspicious_mprogn_p(right).truthy() {
      mtell(
        list1(
          Str(
            "warning: parser: I'll let it stand, but (...) doesn't recognize local variables.~%",
          ),
        ),
      )
      |> ignore
      mtell(
        list2(
          Str("warning: parser: did you mean to say: block(~M, ...) ?~%"),
          car(right),
        ),
      )
      |> ignore
    }
    cons(q_d_any, cons(hdr, right)) // Return an MPROGN
  } else {
    cons(q_d_any, car(right)) // Optimize out MPROGN
  }
}

///|
fn suspicious_mprogn_p(right : Value) -> Value raise {
  // Look for a Maxima list of symbols or assignments to symbols.
  if d_listp(car(right)).truthy() {
    lbool(
      every(
        e => symbolp(e) ||
          (consp(e) && eq(caar(e), q_msetq) && symbolp(second(e))),
        rest(car(right)),
      ),
    )
  } else {
    Nil
  }
}

///|
/// (def-led (|$(| 200.) (op left) ...)
fn nparse__lparen_led(op : Value, left : Value) -> Value raise {
  ignore(op)
  let left = convert(left, q_d_any) // De-reference LEFT
  if numberp(left) {
    parse_err() |> ignore // number(...) illegal
  }
  let hdr = if atom(left) { mheader(amperchk(left)) } else { Nil }
  let r = prsmatch(q_d_op_u0029, q_d_any) // Get arglist in R
  cons(
    q_d_any, // Result is type $ANY
    if atom(left) {
      cons(hdr, r) // (($atom) exp . args)
    } else {
      cons(list1(q_mqapply), cons(left, r)) // ((MQAPPLY) op . args)
    },
  )
}

///|
/// (def-nud (|$'|) (op) ...)
fn nparse__quote_nud(op : Value) -> Value raise {
  ignore(op)
  if eq(q_d_op_u0028, first_c()) {
    let h = mheader(q_d_op_quo)
    return list3(q_d_any, h, parse(q_d_any, Fix(190L)))
  }
  let right = parse(q_d_any, Fix(190L))
  if atom(right) ||
    memq(caar(right), list([q_mquote, q_mlist, q_d_set, q_mprog, q_mprogn, q_lambda])).truthy() {
    list3(q_d_any, mheader(q_d_op_quo), right)
  } else if eq(q_mqapply, caar(right)) {
    if eq(caaadr(right), q_lambda) {
      list3(q_d_any, mheader(q_d_op_quo), right)
    } else {
      rplaca(
        cdr(right),
        cons(cons(d_nounify(caaadr(right)), nparse__cdaadr(right)), cdadr(right)),
      )
      |> ignore
      cons(q_d_any, right)
    }
  } else {
    cons(q_d_any, cons(cons(d_nounify(caar(right)), cdar(right)), cdr(right)))
  }
}

///|
/// (def-nud (|$''|) (op) ...)
fn nparse__quote_quote_nud(op : Value) -> Value raise {
  ignore(op)
  if eq(q_d_op_u0028, first_c()) {
    return cons(q_d_any, meval(parse(q_d_any, Fix(190L))))
  }
  let right = parse(q_d_any, Fix(190L))
  if atom(right) {
    cons(q_d_any, meval1(right).0)
  } else if eq(q_mqapply, caar(right)) {
    rplaca(
      cdr(right),
      cons(cons(d_verbify(caaadr(right)), nparse__cdaadr(right)), cdadr(right)),
    )
    |> ignore
    cons(q_d_any, right)
  } else {
    cons(q_d_any, cons(cons(d_verbify(caar(right)), cdar(right)), cdr(right)))
  }
}

///|
/// (def-led ((|$^| |$^^|)) (op left) ...)
fn nparse__expt_led(op : Value, left : Value) -> Value raise {
  let h = mheader(op)
  let a1 = convert(left, lpos(op))
  let a2 = parse(rpos(op), rbp(op))
  cons(q_d_expr, aliaslookup(list3(h, a1, a2)))
}

///|
/// (def-led ((|$+| |$-|) 100.) (op left) ...)
fn nparse__plus_led(op : Value, left : Value) -> Value raise {
  let left = convert(left, q_d_expr)
  let first_ = if eq(op, q_d_op_) {
    let h = mheader(q_d_op_)
    list2(h, parse(q_d_expr, Fix(100L)))
  } else {
    parse(q_d_expr, Fix(100L))
  }
  let mut nl = list2(first_, left)
  while true {
    let fc = first_c()
    if !(eq(fc, q_d_op_plus) || eq(fc, q_d_op_)) {
      let h = mheader(q_d_op_plus)
      return list_star([q_d_expr, h, nreverse(nl)])
    }
    if eq(first_c(), q_d_op_plus) {
      pop_c() |> ignore
    }
    nl = cons(parse(q_d_expr, Fix(100L)), nl)
  }
  Nil
}

///|
/// (def-nud ($if) (op) ...)
fn nparse__if_nud(op : Value) -> Value raise {
  let p = pos(op)
  let h = mheader(op)
  list_star([p, h, parse_condition(op)])
}

///|
fn parse_condition(op : Value) -> Value raise {
  let c = parse(rpos(op), rbp(op))
  let then_ = if eq(first_c(), q_d_then) {
    parse(q_d_any, rbp(pop_c()))
  } else {
    mread_synerr(Str("Missing `then'"), Nil)
  }
  let fc = first_c()
  let else_ = if eq(fc, q_d_else) {
    list2(t, parse(q_d_any, rbp(pop_c())))
  } else if eq(fc, q_d_elseif) {
    parse_condition(pop_c())
  } else {
    list2(t, q_d_false)
  }
  list_star([c, then_, else_])
}

///|
/// The NUD of the `do' statement keywords.
fn parse__doldo(lex : Value) -> Value raise {
  let left = make_mdo()
  setf_car(left, mheader(q_mdo)) |> ignore
  let mut op = lex
  let mut active_bitmask : Value = Fix(0L)
  while true {
    if eq(op, q_d_op_col) {
      op = q_d_from
    }
    active_bitmask = collision_check(q_d_do, active_bitmask, op)
    let mut data = parse(rpos(op), rbp(op))
    if eq(op, q_d_do) {
      setf_car(nthcdr(7, left), data) |> ignore
      return cons(q_d_any, left)
    } else if eq(op, q_d_for) {
      setf_car(nthcdr(1, left), data) |> ignore
    } else if eq(op, q_d_from) {
      setf_car(nthcdr(2, left), data) |> ignore
    } else if eq(op, q_d_in) {
      setf_car(car(left), q_mdoin) |> ignore
      setf_car(nthcdr(2, left), data) |> ignore
    } else if eq(op, q_d_step) {
      setf_car(nthcdr(3, left), data) |> ignore
    } else if eq(op, q_d_next) {
      setf_car(nthcdr(4, left), data) |> ignore
    } else if eq(op, q_d_thru) {
      setf_car(nthcdr(5, left), data) |> ignore
    } else if eq(op, q_d_unless) || eq(op, q_d_while) {
      if eq(op, q_d_while) {
        data = list2(mheader(q_d_not), data)
      }
      let old = nth(6, left)
      setf_car(
        nthcdr(6, left),
        if old is Nil {
          data
        } else {
          list3(mheader(q_d_or), data, old)
        },
      )
      |> ignore
    } else {
      parse_bug_err(q_d_do) |> ignore
    }
    op = pop_c()
  }
  Nil
}

///|
/// kludge interface function to allow the use of lisp PRINC in places.
fn mopstrip(x : Value) -> Value raise {
  if x is Nil {
    nparse__q_false
  } else if eq(x, t) {
    nparse__q_true
  } else if numberp(x) {
    x
  } else if symbolp(x) {
    let ra = get(x, q_reversealias)
    if ra.truthy() {
      ra
    } else {
      let name = symbol_name(x)
      if name.length() > 0 &&
        (char_at(name, 0) == '$' || char_at(name, 0) == '%') {
        Str(name.substring(start=1))
      } else {
        Str(name)
      }
    }
  } else {
    x
  }
}

///|
/// The Lisp symbols FALSE and TRUE that MOPSTRIP returns for nil and t.
let nparse__q_false : Value = sym("false")

///|
let nparse__q_true : Value = sym("true")

// User extensibility

///|
fn d_prefix(
  operator : Value,
  rbp? : Value = Fix(180L),
  rpos? : Value = q_d_any,
  pos? : Value = q_d_any,
) -> Value raise {
  def_operator(
    operator,
    pos,
    Nil,
    Nil,
    rbp,
    rpos,
    Nil,
    t,
    cons(q_nud, q_parse_prefix),
    q_msize_prefix,
    q_dimension_prefix,
    Nil,
  )
  |> ignore
  operator
}

///|
fn d_postfix(
  operator : Value,
  lbp? : Value = Fix(180L),
  lpos? : Value = q_d_any,
  pos? : Value = q_d_any,
) -> Value raise {
  def_operator(
    operator,
    pos,
    lbp,
    lpos,
    Nil,
    Nil,
    t,
    Nil,
    cons(q_led, q_parse_postfix),
    q_msize_postfix,
    q_dimension_postfix,
    Nil,
  )
  |> ignore
  operator
}

///|
fn d_infix(
  operator : Value,
  lbp? : Value = Fix(180L),
  rbp? : Value = Fix(180L),
  lpos? : Value = q_d_any,
  rpos? : Value = q_d_any,
  pos? : Value = q_d_any,
) -> Value raise {
  def_operator(
    operator,
    pos,
    lbp,
    lpos,
    rbp,
    rpos,
    t,
    t,
    cons(q_led, q_parse_infix),
    q_msize_infix,
    q_dimension_infix,
    Nil,
  )
  |> ignore
  operator
}

///|
fn d_nary(
  operator : Value,
  bp? : Value = Fix(180L),
  argpos? : Value = q_d_any,
  pos? : Value = q_d_any,
) -> Value raise {
  def_operator(
    operator,
    pos,
    bp,
    argpos,
    bp,
    Nil,
    t,
    t,
    cons(q_led, q_parse_nary),
    q_msize_nary,
    q_dimension_nary,
    Nil,
  )
  |> ignore
  operator
}

///|
fn d_matchfix(
  operator : Value,
  match_ : Value,
  argpos? : Value = q_d_any,
  pos? : Value = q_d_any,
) -> Value raise {
  // shouldn't MATCH be optional?
  def_operator(
    operator,
    pos,
    Nil,
    argpos,
    Nil,
    Nil,
    Nil,
    Nil,
    cons(q_nud, q_parse_matchfix),
    q_msize_matchfix,
    q_dimension_match,
    match_,
  )
  |> ignore
  operator
}

///|
fn d_nofix(operator : Value, pos? : Value = q_d_any) -> Value raise {
  def_operator(
    operator,
    pos,
    Nil,
    Nil,
    Nil,
    Nil,
    Nil,
    Nil,
    cons(q_nud, q_parse_nofix),
    q_msize_nofix,
    q_dimension_nofix,
    Nil,
  )
  |> ignore
  operator
}

///|
/// (DEF-OPERATOR op pos lbp lpos rbp rpos sp1 sp2 parse-data grind-fn dim-fn
/// match). SP1/SP2 say if the DISSYM property needs a space on the
/// right/left; PARSE-DATA is (prop . fn); MATCH, if non-(), sets OP up as
/// matchfix with MATCH.
fn def_operator(
  op : Value,
  pos : Value,
  lbp : Value,
  lpos : Value,
  rbp : Value,
  rpos : Value,
  sp1 : Value,
  sp2 : Value,
  parse_data : Value,
  grind_fn : Value,
  dim_fn : Value,
  match_ : Value,
) -> Value raise {
  if rbp.truthy() && !integerp(rbp) {
    merror(
      Str("syntax extension: binding powers must be integers; found: ~M"),
      list1(rbp),
    )
    |> ignore
  }
  if lbp.truthy() && !integerp(lbp) {
    merror(
      Str("syntax extension: binding powers must be integers; found: ~M"),
      list1(lbp),
    )
    |> ignore
  }
  let op = if stringp(op) { define_symbol(op) } else { op }
  op_setup(op) |> ignore
  let noun = d_nounify(op)
  let mut dissym = cdr(exploden(op))
  let mut match_ = match_
  if match_ is Nil {
    dissym = append_n(
      [
        if sp1.truthy() {
          list1(Char(' '))
        } else {
          Nil
        },
        dissym,
        if sp2.truthy() {
          list1(Char(' '))
        } else {
          Nil
        },
      ],
    )
  } else {
    if stringp(match_) {
      match_ = define_symbol(match_)
    }
    op_setup(match_) |> ignore
    putprop(op, match_, q_match) |> ignore
    putprop(match_, Fix(5L), q_lbp) |> ignore
    dissym = cons(dissym, cdr(exploden(match_)))
  }
  putprop(op, pos, q_pos) |> ignore
  putprop(op, cdr(parse_data), car(parse_data)) |> ignore
  putprop(op, grind_fn, q_grind) |> ignore
  putprop(op, dim_fn, q_dimension) |> ignore
  putprop(noun, dim_fn, q_dimension) |> ignore
  putprop(op, dissym, q_dissym) |> ignore
  putprop(noun, dissym, q_dissym) |> ignore
  if rbp.truthy() {
    putprop(op, rbp, q_rbp) |> ignore
    putprop(noun, rbp, q_rbp) |> ignore
  }
  if lbp.truthy() {
    putprop(op, lbp, q_lbp) |> ignore
    putprop(noun, lbp, q_lbp) |> ignore
  }
  if lpos.truthy() {
    putprop(op, lpos, q_lpos) |> ignore
  }
  if rpos.truthy() {
    putprop(op, rpos, q_rpos) |> ignore
  }
  getopr(op)
}

///|
/// `(coerce x 'string)` for a string, symbol or list of characters.
fn nparse__coerce_string(x : Value) -> Value raise {
  match x {
    Str(_) => x
    Nil => Str("")
    Cons(_) => Str(char_list_to_string(x))
    Sym(_) => Str(symbol_name(x))
    Char(c) => Str(c.to_string())
    _ => Str(princ_to_string(x))
  }
}

///|
fn op_setup(op : Value) -> Value raise {
  let dummy = {
    let o = get(op, q_op)
    if o.truthy() {
      o
    } else {
      nparse__coerce_string(string_star(op))
    }
  }
  putprop(op, dummy, q_op) |> ignore
  putopr(dummy, op) |> ignore
  if nparse__operatorp1(op).truthy() &&
    memq(dummy, cdr(symval(q_d_props))) is Nil {
    set(q_ear_mopl, cons(dummy, symval(q_ear_mopl))) |> ignore
  }
  add2lnc(dummy, symval(q_d_props))
}

///|
fn kill_operator(op : Value) -> Value raise {
  let opr = get(op, q_op)
  let noun_form = d_nounify(op)
  // Refuse to kill an operator which appears on *BUILTIN-$PROPS*.
  if member_equal(opr, symval(q_ear_builtin__dolprops)) is Nil {
    undefine_symbol(opr) |> ignore
    remopr(opr) |> ignore
    rempropchk(opr) |> ignore
    for x in [
      q_nud, q_nud_expr, q_nud_subr, q_led, q_led_expr, q_led_subr, q_lbp, q_rbp,
      q_lpos, q_rpos, q_pos, q_grind, q_dimension, q_dissym, q_op, q_verb,
    ] {
      remprop(op, x) |> ignore
    }
    for x in [q_dimension, q_dissym, q_lbp, q_rbp, q_noun] {
      remprop(noun_form, x) |> ignore
    }
    return Nil
  }
  Nil
}

// Input stream line tracking (generic CL versions of GCL's debug.lsp)
//
// (defstruct instream stream (line 0 :type fixnum) stream-name)

///|
fn nparse__make_instream(stream : Value, name : Value) -> Value {
  make_struct("instream", [stream, Fix(0L), name])
}

///|
fn nparse__instream_stream(x : Value) -> Value raise {
  struct_ref(x, 0)
}

///|
fn nparse__instream_line(x : Value) -> Value raise {
  struct_ref(x, 1)
}

///|
fn nparse__instream_stream_name(x : Value) -> Value raise {
  struct_ref(x, 2)
}

///|
/// `(namestring x)` under errset: the file name of a file stream, the string
/// itself for a pathname string, else nil.
fn nparse__namestring(x : Value) -> Value {
  match x {
    Stream(s) => if s.name != "" && s.name != "*terminal-io*" {
        Str(s.name)
      } else {
        Nil
      }
    Str(_) => x
    _ => Nil
  }
}

///|
fn stream_name(path : Value) -> Value raise {
  nparse__namestring(path)
}

///|
fn instream_name(instr : Value) -> Value raise {
  let n = nparse__instream_stream_name(instr)
  if n.truthy() {
    n
  } else {
    stream_name(nparse__instream_stream(instr))
  }
}

///|
/// (closedp stream) checks if a stream is closed. how to do this in common
/// lisp!!
fn cleanup() -> Value raise {
  Nil
}

///|
fn get_instream(str : Value) -> Value raise {
  for v in symval(q_ear_stream_alist).iter() {
    if eq(str, nparse__instream_stream(v)) {
      return v
    }
  }
  let name = nparse__namestring(str)
  let alist = set(
    q_ear_stream_alist,
    cons(nparse__make_instream(str, name), symval(q_ear_stream_alist)),
  )
  car(alist)
}

///|
fn newline(str : Value) -> Value raise {
  let st = get_instream(str)
  struct_set(st, 1, num_add(nparse__instream_line(st), Fix(1L))) |> ignore
  Nil
}

///|
fn find_stream(stream : Value) -> Value raise {
  for v in symval(q_ear_stream_alist).iter() {
    if eq(stream, nparse__instream_stream(v)) {
      return v
    }
  }
  Nil
}

///|
/// Forget the line-tracking entry of STREAM (used after parsing from a
/// private string stream, to keep *STREAM-ALIST* from growing).
fn nparse__forget_stream(stream : Value) -> Unit {
  let keep = Collector::new()
  for v in symval(q_ear_stream_alist).iter() {
    match v {
      Struct(s) if s.slots.length() > 0 && eq(s.slots[0], stream) => ()
      _ => keep.add(v)
    }
  }
  set(q_ear_stream_alist, keep.result()) |> ignore
}

///|
fn add_lineinfo(lis : Value) -> Value raise {
  let ps = symval(q_ear_parse_stream)
  if atom(lis) ||
    eq(ps, symval(q_ear_parse_string_input_stream)) ||
    (eq(symval(q_ear_parse_window), symval(standard_input)) &&
    find_stream(ps) is Nil) {
    return lis
  }
  let st = get_instream(ps)
  let n = nparse__instream_line(st)
  let nam = instream_name(st)
  if nam is Nil {
    return lis
  }
  let cli = symval(q_ear_current_line_info)
  let info = if eq(cadr(cli), nam) {
    if eql(car(cli), n) {
      cli
    } else {
      cons(n, cdr(cli))
    }
  } else {
    list3(n, nam, q_src)
  }
  set(q_ear_current_line_info, info) |> ignore
  if cdr(lis) is Nil {
    list2(car(lis), info)
  } else {
    append(lis, list1(info))
  }
}

///|
/// Remove debugging stuff. STRIP-LINEINFO does not modify EXPR.
fn strip_lineinfo(expr : Value) -> Value raise {
  if atom(expr) || specrepp(expr).truthy() {
    expr
  } else {
    cons(strip_lineinfo_op(car(expr)), mapcar(e => strip_lineinfo(e), cdr(expr)))
  }
}

///|
/// If something in the operator looks like debugging stuff, remove it: a
/// list comprising an integer and a string (and maybe other stuff).
fn strip_lineinfo_op(maxima_op : Value) -> Value raise {
  remove_if(
    x => consp(x) && integerp(first(x)) && stringp(second(x)),
    maxima_op,
  )
}

///|
fn getalias(x : Value) -> Value raise {
  let a = get(x, q_alias)
  if a.truthy() {
    a
  } else if eq(x, q_d_false) {
    Nil
  } else {
    x
  }
}

///|
fn amperchk(name : Value) -> Value raise {
  if symbolp(name) {
    name
  } else if stringp(name) {
    let o = getopr0(name)
    getalias(
      if o.truthy() {
        o
      } else {
        implode(cons(Char('$'), string_to_char_list(lstring(name))))
      },
    )
  } else {
    name
  }
}

///|
/// Code for handling #$...$ in Lisp code: parse a Maxima expression and
/// return the corresponding internal Lisp representation.
fn macsyma_read_string(a_string : Value) -> Value raise {
  let mut s = lstring(a_string)
  if !(s.contains("$") || s.contains(";")) {
    s = s + "$"
  }
  let stream = make_string_input_stream(s)
  third(mread(list1(stream)))
}

///|
fn d__read_aux(arg : Value, stream : Value) -> Value raise {
  ignore(arg)
  with_special(q_ear_mread_prompt, Str(""), fn() raise {
    let mut meval_flag = true
    // (peek-char t stream): skip whitespace
    while true {
      match peek_char(stream~) {
        Char(' ' | '\t' | '\n' | '\r' | '\u{c}') => read_char(stream~) |> ignore
        _ => break
      }
    }
    if nparse__chr(peek_char(stream~), '$') {
      tyi(stream~) |> ignore
      meval_flag = false
    }
    let buf = StringBuilder()
    let mut ch : Value = Nil
    while !nparse__chr(ch, '$') {
      ch = tyi(stream~)
      match ch {
        Char(c) => buf.write_char(c)
        _ => break
      }
    }
    let s : Value = Str(buf.to_string())
    if meval_flag {
      list2(q_meval_star, list2(q_quote, macsyma_read_string(s)))
    } else {
      list2(q_quote, macsyma_read_string(s))
    }
  })
}

///|
fn x_dol_cl_macro_read(
  stream : Value,
  sub_char : Value,
  arg : Value,
) -> Value raise {
  ignore(arg)
  d__read_aux(sub_char, stream)
}

///|
/// The port has no Lisp readtables (`#$...$` is handled by `maxima_lit`).
fn find_lisp_readtable_for_macsyma() -> Value raise {
  symval(q_ear_macsyma_readtable)
}

///|
fn set_readtable_for_macsyma() -> Value raise {
  find_lisp_readtable_for_macsyma()
}

///|
/// Parse STR with the parser, binding *PARSE-STRING-INPUT-STREAM* to the
/// private stream so that no line info is attached, and calling F with the
/// stream. Line tracking for the stream is dropped afterwards.
fn[T] nparse__with_string_stream(
  str : String,
  f : (Value) -> T raise,
) -> T raise {
  let stream = make_string_input_stream(str)
  defer nparse__forget_stream(stream)
  with_special(q_ear_parse_string_input_stream, stream, () => f(stream))
}

///|
/// `#$expr$`: parse Maxima syntax once (cached) and return the expression.
/// As at read time, nothing is evaluated: the result is the parsed form of
/// `#$$expr$` (a leading `$`, as in `#$$...$`, is accepted and dropped). The
/// result is shared between callers and must not be mutated.
fn maxima_lit(s : String) -> Value raise {
  match nparse__lit_cache.get(s) {
    Some(v) => v
    None => {
      let mut src = string_left_trim(" \t\n\r", s)
      if src.has_prefix("$") {
        src = src.substring(start=1)
      }
      if !(src.contains("$") || src.contains(";")) {
        src = src + "$"
      }
      let v = with_special(q_ear_mread_prompt, Str(""), fn() raise {
        nparse__with_string_stream(src, stream => third(mread(list1(stream))))
      })
      nparse__lit_cache.set(s, v)
      v
    }
  }
}

///|
/// Parse every statement of S (for a REPL). Each element is what MREAD
/// returns: `(<header> <labels> <expr>)`, where the header is
/// `(displayinput)` for a statement terminated by `;` and
/// `(nodisplayinput)` for one terminated by `$`. A statement left without
/// terminator at the end of S is a syntax error, as in Maxima.
fn mread_all_from_string(s : String) -> Array[Value] raise {
  let out : Array[Value] = []
  nparse__with_string_stream(s, fn(stream) raise {
    let eof = list1(Nil)
    while true {
      // As MREAD does before each prompt: mark the start of a new input in
      // the parse window, so syntax error context starts here.
      let w = symval(q_ear_parse_window)
      if w.truthy() {
        setf_car(w, Nil) |> ignore
        set(q_ear_parse_window, cdr(w)) |> ignore
      }
      let r = mread_raw(stream, ear_mread_eof_obj=eof)
      if eq(r, eof) {
        break
      }
      out.push(r)
    }
  })
  out
}

// ---------------------------------------------------------------------------
// Top-level forms

///|
fn nparse__nud_fun(name : String, f : (Value) -> Value raise) -> Value {
  lfunc(name, args => f(arg(args, 0)))
}

///|
fn nparse__led_fun(name : String, f : (Value, Value) -> Value raise) -> Value {
  lfunc(name, args => f(arg(args, 0), arg(args, 1)))
}

///|
fn init_nparse() -> Unit raise {
  // *whitespace-chars*
  set(
    q_ear_unicode_space_chars_for_maxima,
    mapcar(
      c => Char(code_char(to_int(c))),
      symval(q_ear_unicode_space_char_codes_for_maxima),
    ),
  )
  |> ignore
  defvar_init(
    q_ear_whitespace_chars,
    append(
      symval(q_ear_ascii_space_chars_for_maxima),
      symval(q_ear_unicode_space_chars_for_maxima),
    ),
  )
  defvar_init(q_ear_parse_stream, Nil)
  defvar_init(q_ear_mread_eof_obj, Nil)
  // reference to the input stream used by parse-string (a closed stream)
  defvar_init(q_ear_parse_string_input_stream, make_string_input_stream(""))
  defvar_init(q_scan_buffered_token, list1(Nil))
  defvar_init(
    q_ear_sharp_read_buffer,
    make_array([140], elt="character", fill=0),
  )
  let f_delim_err = nparse__fn(q_delim_err)
  let f_erb_err = nparse__fn(q_erb_err)
  let f_parse_infix = nparse__fn(q_parse_infix)
  let f_parse_nary = nparse__fn(q_parse_nary)
  let f_parse_prefix = nparse__fn(q_parse_prefix)
  let f_parse_postfix = nparse__fn(q_parse_postfix)
  let f_premterm_err = nparse__fn(q_premterm_err)
  let f_parse_do = nparse__fn(q_parse__doldo)
  def_operatorp() |> ignore
  def_operatorp1() |> ignore

  // english names of the modes, used by CONVERT
  putprop(q_d_any, Str("untyped"), q_english) |> ignore
  putprop(q_d_clause, Str("logical"), q_english) |> ignore
  putprop(q_d_expr, Str("algebraic"), q_english) |> ignore
  def_mheader(q_d_box, list1(q_mbox)) |> ignore

  // ]
  def_nud_equiv(q_d_op_rb, f_delim_err) |> ignore
  def_led_equiv(q_d_op_rb, f_erb_err) |> ignore
  def_lbp(q_d_op_rb, Fix(5L)) |> ignore
  // [
  def_nud_equiv(q_d_op_lb, nparse__fn(q_parse_matchfix)) |> ignore
  def_match(q_d_op_lb, q_d_op_rb) |> ignore
  def_lbp(q_d_op_lb, Fix(200L)) |> ignore
  def_mheader(q_d_op_lb, list1(q_mlist)) |> ignore
  def_pos(q_d_op_lb, q_d_any) |> ignore
  def_lpos(q_d_op_lb, q_d_any) |> ignore
  putprop(q_d_op_lb, nparse__led_fun("$[-led", nparse__lb_led), q_led)
  |> ignore
  set_lbp_and_rbp(q_d_op_lb, Fix(200L), Nil) |> ignore
  // )
  def_nud_equiv(q_d_op_u0029, f_delim_err) |> ignore
  def_led_equiv(q_d_op_u0029, f_erb_err) |> ignore
  def_lbp(q_d_op_u0029, Fix(5L)) |> ignore
  // (
  def_mheader(q_d_op_u0028, list1(q_mprogn)) |> ignore
  putprop(q_d_op_u0028, nparse__nud_fun("$(-nud", nparse__lparen_nud), q_nud)
  |> ignore
  set_lbp_and_rbp(q_d_op_u0028, Fix(200L), Nil) |> ignore
  putprop(q_d_op_u0028, nparse__led_fun("$(-led", nparse__lparen_led), q_led)
  |> ignore
  set_lbp_and_rbp(q_d_op_u0028, Fix(200L), Nil) |> ignore
  // ' and ''
  def_mheader(q_d_op_quo, list1(q_mquote)) |> ignore
  putprop(q_d_op_quo, nparse__nud_fun("$'-nud", nparse__quote_nud), q_nud)
  |> ignore
  set_lbp_and_rbp(q_d_op_quo, Nil, Nil) |> ignore
  putprop(
    q_d_op_quo_quo,
    nparse__nud_fun("$''-nud", nparse__quote_quote_nud),
    q_nud,
  )
  |> ignore
  set_lbp_and_rbp(q_d_op_quo_quo, Nil, Nil) |> ignore
  // assignment operators
  for e in [
    (q_d_op_col, q_msetq),
    (q_d_op_col_col, q_mset),
    (q_d_op_col_eq, q_mdefine),
    (q_d_op_col_col_eq, q_mdefmacro),
  ] {
    def_led_equiv(e.0, f_parse_infix) |> ignore
    def_lbp(e.0, Fix(180L)) |> ignore
    def_rbp(e.0, Fix(20L)) |> ignore
    def_pos(e.0, q_d_any) |> ignore
    def_rpos(e.0, q_d_any) |> ignore
    def_lpos(e.0, q_d_any) |> ignore
    def_mheader(e.0, list1(e.1)) |> ignore
  }
  // !
  def_led_equiv(q_d_op_bang, f_parse_postfix) |> ignore
  def_lbp(q_d_op_bang, Fix(160L)) |> ignore
  def_pos(q_d_op_bang, q_d_expr) |> ignore
  def_lpos(q_d_op_bang, q_d_expr) |> ignore
  def_mheader(q_d_op_bang, list1(q_mfactorial)) |> ignore
  // ^
  def_lbp(q_d_op_hat, Fix(140L)) |> ignore
  def_rbp(q_d_op_hat, Fix(139L)) |> ignore
  def_pos(q_d_op_hat, q_d_expr) |> ignore
  def_lpos(q_d_op_hat, q_d_expr) |> ignore
  def_rpos(q_d_op_hat, q_d_expr) |> ignore
  def_mheader(q_d_op_hat, list1(q_mexpt)) |> ignore
  putprop(q_d_op_hat, nparse__led_fun("$^-led", nparse__expt_led), q_led)
  |> ignore
  inherit_propl(q_d_op_hat_hat, q_d_op_hat, led_propl()) |> ignore
  set_lbp_and_rbp(list2(q_d_op_hat, q_d_op_hat_hat), Nil, Nil) |> ignore
  // Make $** like $^
  for prop in [q_lbp, q_rbp, q_pos, q_rpos, q_lpos, q_mheader] {
    let propval = get(q_d_op_hat, prop)
    if propval.truthy() {
      putprop(q_d_op_star_star, propval, prop) |> ignore
    }
  }
  inherit_propl(q_d_op_star_star, q_d_op_hat, led_propl()) |> ignore
  // ^^
  def_lbp(q_d_op_hat_hat, Fix(140L)) |> ignore
  def_rbp(q_d_op_hat_hat, Fix(139L)) |> ignore
  def_pos(q_d_op_hat_hat, q_d_expr) |> ignore
  def_lpos(q_d_op_hat_hat, q_d_expr) |> ignore
  def_rpos(q_d_op_hat_hat, q_d_expr) |> ignore
  def_mheader(q_d_op_hat_hat, list1(q_mncexpt)) |> ignore
  // note y^^4.z gives an error because it scans the number 4 together with
  // the trailing '.' as a decimal place.    I think the error is correct.
  def_led_equiv(q_d_op_dot, f_parse_infix) |> ignore
  def_lbp(q_d_op_dot, Fix(130L)) |> ignore
  def_rbp(q_d_op_dot, Fix(129L)) |> ignore
  def_pos(q_d_op_dot, q_d_expr) |> ignore
  def_lpos(q_d_op_dot, q_d_expr) |> ignore
  def_rpos(q_d_op_dot, q_d_expr) |> ignore
  def_mheader(q_d_op_dot, list1(q_mnctimes)) |> ignore
  // Copy properties to noun operator.
  putprop(q_p_mnctimes, get(q_mnctimes, q_op), q_op) |> ignore
  // *
  def_led_equiv(q_d_op_star, f_parse_nary) |> ignore
  def_lbp(q_d_op_star, Fix(120L)) |> ignore
  def_pos(q_d_op_star, q_d_expr) |> ignore
  def_lpos(q_d_op_star, q_d_expr) |> ignore
  def_mheader(q_d_op_star, list1(q_mtimes)) |> ignore
  // /
  def_led_equiv(q_d_op_sl, f_parse_infix) |> ignore
  def_lbp(q_d_op_sl, Fix(120L)) |> ignore
  def_rbp(q_d_op_sl, Fix(120L)) |> ignore
  def_pos(q_d_op_sl, q_d_expr) |> ignore
  def_rpos(q_d_op_sl, q_d_expr) |> ignore
  def_lpos(q_d_op_sl, q_d_expr) |> ignore
  def_mheader(q_d_op_sl, list1(q_mquotient)) |> ignore
  // +
  def_nud_equiv(q_d_op_plus, f_parse_prefix) |> ignore
  def_lbp(q_d_op_plus, Fix(100L)) |> ignore
  def_rbp(q_d_op_plus, Fix(134L)) |> ignore // increased from 100 (DK 02/2010)
  def_pos(q_d_op_plus, q_d_expr) |> ignore
  def_rpos(q_d_op_plus, q_d_expr) |> ignore
  def_mheader(q_d_op_plus, list1(q_mplus)) |> ignore
  putprop(q_d_op_plus, nparse__led_fun("$+-led", nparse__plus_led), q_led)
  |> ignore
  inherit_propl(q_d_op_, q_d_op_plus, led_propl()) |> ignore
  set_lbp_and_rbp(list2(q_d_op_plus, q_d_op_), Fix(100L), Nil) |> ignore
  // -
  def_nud_equiv(q_d_op_, f_parse_prefix) |> ignore
  def_lbp(q_d_op_, Fix(100L)) |> ignore
  def_rbp(q_d_op_, Fix(134L)) |> ignore
  def_pos(q_d_op_, q_d_expr) |> ignore
  def_rpos(q_d_op_, q_d_expr) |> ignore
  def_mheader(q_d_op_, list1(q_mminus)) |> ignore
  // relational operators
  for e in [
    (q_d_op_eq, q_mequal),
    (q_d_op_hash, q_mnotequal),
    (q_d_op_gt, q_mgreaterp),
    (q_d_op_gt_eq, q_mgeqp),
    (q_d_op_lt, q_mlessp),
    (q_d_op_lt_eq, q_mleqp),
  ] {
    def_led_equiv(e.0, f_parse_infix) |> ignore
    def_lbp(e.0, Fix(80L)) |> ignore
    def_rbp(e.0, Fix(80L)) |> ignore
    def_pos(e.0, q_d_clause) |> ignore
    def_rpos(e.0, q_d_expr) |> ignore
    def_lpos(e.0, q_d_expr) |> ignore
    def_mheader(e.0, list1(e.1)) |> ignore
  }
  // not
  def_nud_equiv(q_d_not, f_parse_prefix) |> ignore
  def_rbp(q_d_not, Fix(70L)) |> ignore
  def_pos(q_d_not, q_d_clause) |> ignore
  def_rpos(q_d_not, q_d_clause) |> ignore
  def_lpos(q_d_not, q_d_clause) |> ignore
  def_mheader(q_d_not, list1(q_mnot)) |> ignore
  // and
  def_led_equiv(q_d_and, f_parse_nary) |> ignore
  def_lbp(q_d_and, Fix(65L)) |> ignore
  def_pos(q_d_and, q_d_clause) |> ignore
  def_lpos(q_d_and, q_d_clause) |> ignore
  def_mheader(q_d_and, list1(q_mand)) |> ignore
  // or
  def_led_equiv(q_d_or, f_parse_nary) |> ignore
  def_lbp(q_d_or, Fix(60L)) |> ignore
  def_pos(q_d_or, q_d_clause) |> ignore
  def_lpos(q_d_or, q_d_clause) |> ignore
  def_mheader(q_d_or, list1(q_mor)) |> ignore
  // ,
  def_led_equiv(q_d_op_cm, f_parse_nary) |> ignore
  def_lbp(q_d_op_cm, Fix(10L)) |> ignore
  def_pos(q_d_op_cm, q_d_any) |> ignore
  def_lpos(q_d_op_cm, q_d_any) |> ignore
  def_mheader(q_d_op_cm, list1(q_d_ev)) |> ignore
  // then, else, elseif
  def_nud_equiv(q_d_then, f_delim_err) |> ignore
  def_lbp(q_d_then, Fix(5L)) |> ignore
  def_rbp(q_d_then, Fix(25L)) |> ignore
  def_nud_equiv(q_d_else, f_delim_err) |> ignore
  def_lbp(q_d_else, Fix(5L)) |> ignore
  def_rbp(q_d_else, Fix(25L)) |> ignore
  def_nud_equiv(q_d_elseif, f_delim_err) |> ignore
  def_lbp(q_d_elseif, Fix(5L)) |> ignore
  def_rbp(q_d_elseif, Fix(45L)) |> ignore
  def_pos(q_d_elseif, q_d_any) |> ignore
  def_rpos(q_d_elseif, q_d_clause) |> ignore
  // if
  def_rbp(q_d_if, Fix(45L)) |> ignore
  def_pos(q_d_if, q_d_any) |> ignore
  def_rpos(q_d_if, q_d_clause) |> ignore
  def_mheader(q_d_if, list1(q_mcond)) |> ignore
  putprop(q_d_if, nparse__nud_fun("$if-nud", nparse__if_nud), q_nud) |> ignore
  set_lbp_and_rbp(q_d_if, Nil, Nil) |> ignore
  // do
  def_mheader(q_d_do, list1(q_mdo)) |> ignore
  for k in [
    q_d_for, q_d_from, q_d_step, q_d_next, q_d_thru, q_d_unless, q_d_while, q_d_do,
  ] {
    def_lbp(k, Fix(25L)) |> ignore
  }
  for k in [
    q_d_for, q_d_from, q_d_step, q_d_next, q_d_thru, q_d_unless, q_d_while, q_d_do,
  ] {
    def_nud_equiv(k, f_parse_do) |> ignore
  }
  for e in [
    (q_d_do, 25L),
    (q_d_for, 200L),
    (q_d_from, 95L),
    (q_d_in, 95L),
    (q_d_step, 95L),
    (q_d_next, 45L),
    (q_d_thru, 95L),
    (q_d_unless, 45L),
    (q_d_while, 45L),
  ] {
    def_rbp(e.0, Fix(e.1)) |> ignore
  }
  for e in [
    (q_d_do, q_d_any),
    (q_d_for, q_d_any),
    (q_d_from, q_d_any),
    (q_d_step, q_d_expr),
    (q_d_next, q_d_any),
    (q_d_thru, q_d_expr),
    (q_d_unless, q_d_clause),
    (q_d_while, q_d_clause),
  ] {
    def_rpos(e.0, e.1) |> ignore
  }
  def_collisions(
    q_d_do,
    list([
      list1(q_d_do),
      list2(q_d_for, q_d_for),
      list3(q_d_from, q_d_in, q_d_from),
      list([q_d_in, q_d_in, q_d_from, q_d_step, q_d_next, q_d_thru]),
      list4(q_d_step, q_d_in, q_d_step, q_d_next),
      list4(q_d_next, q_d_in, q_d_step, q_d_next),
      list3(q_d_thru, q_d_in, q_d_thru), // $IN didn't used to get checked for
      list1(q_d_unless),
      list1(q_d_while),
    ]),
  )
  |> ignore
  // statement terminators
  def_mheader(q_d_op_dol, list1(nparse__q_nodisplayinput)) |> ignore
  def_nud_equiv(q_d_op_dol, f_premterm_err) |> ignore
  def_lbp(q_d_op_dol, Fix(-1L)) |> ignore
  def_mheader(q_d_op_sc, list1(q_displayinput)) |> ignore
  def_nud_equiv(q_d_op_sc, f_premterm_err) |> ignore
  def_lbp(q_d_op_sc, Fix(-1L)) |> ignore
  def_nud_equiv(q_d_op_amp_amp, f_delim_err) |> ignore
  def_lbp(q_d_op_amp_amp, Fix(-1L)) |> ignore
  // Note: /. is looked for explicitly rather than existing in this chart:
  // it serves a dual role (as a decimal point). Same for // because of the
  // /* ... */ handling by the tokenizer.
  define_initial_symbols(
    list(
      [
        // Single character
        "+", "-", "*", "^", "<", "=", ">", "(", ")", "[", "]", ",", ":", "!", "#",
        "'", ";", "$", "&",
        // Two character
        "**", "^^", ":=", "::", "!!", "<=", ">=", "''", "&&",
        // Three character
        "::=",
      ].map(s => sym(s)),
    ),
  )
  |> ignore
  // !! FOLLOWING MOVED HERE FROM MLISP.LISP (DEFSTRUCT STUFF)
  define_symbol(Str("@")) |> ignore
}
