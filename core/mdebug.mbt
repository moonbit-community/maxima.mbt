// Port of src/mdebug.lisp: the Maxima debugger -- backtraces, the break
// loop entered on an error under debugmode(true), break commands (":bt",
// ":lisp", ":help", ...), breakpoints and stepping through Maxima
// functions with line information.
//
// *mlambda-call-stack* holds 5 entries per active Maxima function call:
//   bindlist, form, params, args, fname
// e.g. #(NIL ($X) (1) $FF ($BIL $X) ($Y) (36) $JOE ($Y $BIL $X) ($JJX) (36)
// To get to current values in ff we need to unbind bindlist down to
// ($BIL $X); to get to current values in joe down to ($Y $BIL $X).
//
// A line-info is a list (line file ...); a breakpoint (bkpt) is a list
// (form file file-line function), and a disabled one is (nil . bkpt).
//
// Break commands are keywords with a BREAK-COMMAND property: a function,
// called on the evaluated arguments, or one of the macros LISP-QUIET,
// LISP-EVAL and DO-BREAK, called on the arguments as read.

///|
/// X as CL prints it with ~A / ~S: the port's symbol names are CL's with
/// the case inverted.
fn mdebug__cl(x : Value) -> Value {
  match x {
    Sym(s) => Str(invert_case(s.name))
    _ => x
  }
}

///|
/// KEYWORDP, also for keywords such as :_NONE whose name does not start
/// with a letter (the runtime's KEYWORDP only accepts those, to tell
/// keywords from operator symbols such as ":" and "::=").
fn mdebug__keywordp(x : Value) -> Bool {
  match x {
    Sym(s) => keywordp(x) || s.name.has_prefix(":_")
    _ => false
  }
}

///|
/// (eval x) of an argument of a break command.
fn mdebug__eval_arg(x : Value) -> Value raise {
  match x {
    Nil => Nil
    Sym(_) => if keywordp(x) || eq(x, t) { x } else { symval(x) }
    Cons(_) => lisp_eval_form(x)
    _ => x
  }
}

///|
/// The keywords (the symbols of the KEYWORD package).
/// The iteration order of a CL package is unspecified; the keywords are
/// taken in name order (which is also the order SBCL shows for the break
/// commands).
fn mdebug__keywords() -> Array[Value] {
  let r : Array[Symbol] = []
  for s in all_symbols() {
    if s.name.has_prefix(":") {
      r.push(s)
    }
  }
  r.sort_by((a, b) => string_compare(a.name, b.name))
  r.map(s => Sym(s))
}

///|
fn mdebug__vector_length(v : Value) -> Int raise {
  match v {
    Vec(a) =>
      match a.fill {
        Some(f) => f
        None => a.data.length()
      }
    Nil => 0
    _ => length(v)
  }
}

///|
/// (macro f (op &rest args)): (the fixnum (op (the fixnum arg) ...))
fn f(op : Value, args : Value) -> Value raise {
  apply(op, args)
}

///|
/// (macro fb (op &rest args)): (op (the fixnum arg) ...)
fn fb(op : Value, args : Value) -> Value raise {
  apply(op, args)
}

///|
fn frame_info(n : Value) -> (Value, Value, Value, Value, Value, Value) raise {
  let ar = symval(q_ear_mlambda_call_stack)
  let mut m = mdebug__vector_length(ar)
  // just in case we do not have an even multiple
  m = m - m % 5 - to_int(n) * 5
  if m <= 0 {
    return (Nil, Nil, Nil, Nil, Nil, Nil)
  }
  let fname = aref1(ar, m - 1)
  let vals = aref1(ar, m - 2)
  let params = aref1(ar, m - 3)
  let backtr = aref1(ar, m - 4)
  let fp = fill_pointer(ar)
  let bdlist = if m < fp { aref1(ar, m) } else { symval(q_bindlist) }
  let lineinfo = if m < fp {
    get_lineinfo(aref1(ar, m + 1))
  } else {
    get_lineinfo(symval(q_ear_last_meval1_form))
  }
  (fname, vals, params, backtr, lineinfo, bdlist)
}

///|
fn print_one_frame(
  n : Value,
  print_frame_number : Value,
) -> (Value, Value, Value, Value, Value, Value) raise {
  let st = symval(q_ear_debug_io)
  let (fname, vals, params, backtr, lineinfo, bdlist) = frame_info(n)
  if fname is Nil {
    return (Nil, Nil, Nil, Nil, Nil, Nil)
  }
  princ(
    if print_frame_number.truthy() {
      d_sconcat(list([Str("#"), n, Str(": "), fname, Str("(")]))
    } else {
      d_sconcat(list([fname, Str("(")]))
    },
    stream=st,
  )
  |> ignore
  let mut v = params
  let mut w = vals
  while v.truthy() && w.truthy() {
    let mut val = d_sconcat(list1(car(w)))
    if string_length(lstring(val)) > 100 {
      val = d_sconcat(list([subseq(val, 0, end=100), Str("...")]))
    }
    format(st, "~(~a~)=~a~a", [
      d_sconcat(list1(car(v))),
      val,
      Str(if cdr(v).truthy() { "," } else { "" }),
    ])
    |> ignore
    v = cdr(v)
    w = cdr(w)
  }
  princ(Str(")"), stream=st) |> ignore
  if lineinfo.truthy() {
    format(st, " (~a line ~a)", [short_name(cadr(lineinfo)), car(lineinfo)])
    |> ignore
  }
  terpri(stream=st)
  (fname, vals, params, backtr, lineinfo, bdlist)
}

///|
fn break_call(key : Value, args : Value, prop : Value) -> Value raise {
  let mut fun = complete_prop(key, q_kw_keyword, prop)
  let key = fun
  if fun is Nil {
    return Nil
  }
  fun = get(fun, prop)
  if fun.truthy() {
    // (eval (cons fun args))
    if eq(fun, q_lisp_quiet) {
      lisp_quiet(args)
    } else if eq(fun, q_lisp_eval) {
      lisp_eval(args)
    } else if eq(fun, q_do_break) {
      do_break(name=car(args), cdr(args))
    } else {
      let argv = list_to_array(args).map(a => mdebug__eval_arg(a))
      funcall(fun, argv)
    }
  } else {
    suprv1__fmt(symval(q_ear_debug_io), "~&~A is an undefined break command.~%", [
      mdebug__cl(key),
    ])
  }
}

///|
fn complete_prop(
  sym_ : Value,
  package_ : Value,
  prop : Value,
  return_list? : Value = Nil,
) -> Value raise {
  ignore(package_)
  if symbolp(sym_) && get(sym_, prop).truthy() && mdebug__keywordp(sym_) {
    return sym_
  }
  let name = symbol_name(sym_)
  let all = Collector::new()
  let mut count = 0
  for vv in mdebug__keywords() {
    if get(vv, prop).truthy() && string_search(name, symbol_name(vv)) == 0 {
      all.add(vv)
      count += 1
    }
  }
  let all = all.result()
  let dbg = symval(q_ear_debug_io)
  if return_list.truthy() {
    all
  } else if count > 1 {
    suprv1__fmt(dbg, "~&Break command '~(~s~)' is ambiguous.~%", [sym_]) |> ignore
    format(dbg, "Perhaps you meant one of the following: ~(~{~s~^, ~}~).", [
      all,
    ])
    |> ignore
    finish_output(stream=dbg)
    Nil
  } else if count == 0 {
    suprv1__fmt(dbg, "~&Break command '~(~s~)' does not exist.", [sym_]) |> ignore
    finish_output(stream=dbg)
    Nil
  } else {
    car(all)
  }
}

///|
fn d_backtrace(n? : Value) -> Value raise {
  let n_p = n is Some(_)
  let n = n.unwrap_or(Fix(0L))
  if !(integerp(n) && !minusp(n)) {
    merr(
      "backtrace: number of frames must be a nonnegative integer; got ~M~%",
      [n],
    )
    |> ignore
  }
  with_special(q_d_display2d, Nil, () => {
    let mut i = 0
    let mut j = symval(q_ear_current_frame)
    while true {
      if n_p && num_eq(int(i), n) {
        return Nil
      }
      if print_one_frame(j, t).0 is Nil {
        break
      }
      i += 1
      j = num_add(j, Fix(1L))
    }
    Nil
  })
}

// if this is NIL then nothing more is checked in eval

///|
fn init_break_points() -> Value raise {
  set_fill_pointer(symval(q_ear_break_point_vector), 0)
  set(q_ear_break_points, symval(q_ear_break_point_vector))
}

///|
fn step_into(ignored? : Value = Nil) -> Value raise {
  ignore(ignored)
  if symval(q_ear_break_points) is Nil {
    init_break_points() |> ignore
  }
  set(q_ear_break_step, q_break_step_into) |> ignore
  q_kw_resume
}

///|
fn step_next(n? : Value = Fix(1L)) -> Value raise {
  let fun = current_step_fun()
  set(q_ear_step_next, cons(n, fun)) |> ignore
  if symval(q_ear_break_points) is Nil {
    init_break_points() |> ignore
  }
  set(q_ear_break_step, q_break_step_next) |> ignore
  q_kw_resume
}

///|
/// (position item vector) by EQL, NIL if absent.
fn mdebug__position(item : Value, v : Value) -> Value raise {
  let n = mdebug__vector_length(v)
  for i in 0..<n {
    if eql(aref1(v, i), item) {
      return int(i)
    }
  }
  Nil
}

///|
fn maybe_break(form : Value, line_info : Value, fun : Value, env : Value) -> Value raise {
  ignore(env)
  let pos = mdebug__position(form, line_info)
  if pos.truthy() {
    set(q_ear_break_step, Nil) |> ignore
    if !(mdebug__vector_length(symval(q_ear_break_points)) > 0) {
      set(q_ear_break_points, Nil) |> ignore
    }
    break_dbm_loop(make_break_point(fun, line_info, pos)) |> ignore
    t
  } else {
    Nil
  }
}

// These following functions, when they are the value of *break-step* are
// invoked by an inner hook in eval. They may choose to stop things.

///|
fn break_step_into(form : Value, env? : Value = Nil) -> Value raise {
  let fun = current_step_fun()
  let line_info = set_full_lineinfo(fun)
  if line_info.truthy() {
    maybe_break(form, line_info, fun, env)
  } else {
    Nil
  }
}

///|
fn break_step_next(form : Value, env? : Value = Nil) -> Value raise {
  let fun = current_step_fun()
  if eql(cdr(symval(q_ear_step_next)), fun) {
    let line_info = set_full_lineinfo(fun)
    maybe_break(form, line_info, fun, env)
  } else {
    Nil
  }
}

///|
/// (copy-seq vector): a simple vector of the active elements.
fn mdebug__copy_vector(v : Value) -> Value raise {
  let n = mdebug__vector_length(v)
  let data : Array[Value] = []
  for i in 0..<n {
    data.push(aref1(v, i))
  }
  Vec({ data, dims: [n], fill: None, elt: "t" })
}

///|
/// The lineinfo for a function will be a vector of forms such that each one
/// is the first form on a line.  We will walk thru the tree taking the
/// first occurrence for each line.
fn set_full_lineinfo(fname : Value) -> Value raise {
  let body = get(fname, q_lineinfo)
  if atom(body) {
    return body
  }
  if symval(q_ear_lineinfo_array_internal) is Nil {
    set(q_ear_lineinfo_array_internal, make_array([20], fill=0)) |> ignore
  } else {
    set_fill_pointer(symval(q_ear_lineinfo_array_internal), 0)
  }
  let ar = symval(q_ear_lineinfo_array_internal)
  let te = get_lineinfo(body)
  if te.truthy() {
    vector_push_extend(car(te), ar) |> ignore
    walk_get_lineinfo(body, ar) |> ignore
  }
  if fill_pointer(ar) > 0 {
    putprop(fname, mdebug__copy_vector(ar), q_lineinfo)
  } else {
    putprop(fname, Nil, q_lineinfo)
  }
}

///|
fn walk_get_lineinfo(form : Value, ar : Value) -> Value raise {
  if atom(form) {
    return Nil
  }
  let tem = get_lineinfo(form)
  if tem is Nil {
    return Nil
  }
  let i = to_int(car(tem)) - to_int(aref1(ar, 0)) + 1
  let fp = fill_pointer(ar)
  if i < fp {
    if aref1(ar, i) is Nil {
      aset1(ar, i, form) |> ignore
    }
  } else {
    // (loop for j from (fill-pointer ar) below i do (setf (aref ar j) nil))
    // (setf (fill-pointer ar) (f + i 1)) (setf (aref ar i) form)
    for _ in fp..<i {
      vector_push_extend(Nil, ar) |> ignore
    }
    vector_push_extend(form, ar) |> ignore
  }
  for v in cdr(form).iter() {
    if !atom(v) {
      walk_get_lineinfo(v, ar) |> ignore
    }
  }
  Nil
}

///|
fn first_form_line(form : Value, line : Value) -> Value raise {
  if atom(form) {
    return Nil
  }
  let tem = get_lineinfo(form)
  if tem.truthy() && eql(car(tem), line) {
    return form
  }
  for v in cdr(form).iter() {
    let tem = first_form_line(v, line)
    if tem.truthy() {
      return tem
    }
  }
  Nil
}

///|
/// Split string into a list of strings, split by any of a list of
/// characters in bag.
fn split_string_(string_ : Value, bag : Value, start? : Value = Fix(0L)) -> Value raise {
  let cs = string_chars(lstring(string_))
  let bagc = string_chars(lstring(bag))
  let all : Array[Char] = []
  let mut start = to_int(start)
  let mut i = start
  while i < cs.length() {
    let v = cs[i]
    start += 1
    if !bagc.contains(v) {
      all.push(v)
    } else if all.length() > 0 {
      break
    }
    i += 1
  }
  if all.length() > 0 {
    cons(Str(chars_to_string(all)), split_string_(string_, bag, start=int(start)))
  } else {
    Nil
  }
}

///|
/// READ-CHAR-NO-HANG: a character if one is already buffered, else NIL.
fn mdebug__read_char_no_hang(stream : Value) -> Value {
  let st = match stream {
    Stream(st) => Some(st)
    _ =>
      match symval(standard_input) {
        Stream(st) => Some(st)
        _ => None
      }
  }
  match st {
    Some(st) =>
      if st.unread.length() > 0 || st.pos < st.input.length() {
        match st.read_char() {
          Some(c) => Char(c)
          None => Nil
        }
      } else {
        Nil
      }
    None => Nil
  }
}

///|
/// (read-from-string line): the datum (here a break command keyword) and
/// the index after it.
fn mdebug__read_from_string(line : String) -> (Value, Int) raise {
  let cs = string_chars(line)
  let n = cs.length()
  let mut i = 0
  while i < n && (cs[i] == ' ' || cs[i] == '\t' || cs[i] == '\n') {
    i += 1
  }
  let start = i
  while i < n &&
        !(
          cs[i] == ' ' ||
          cs[i] == '\t' ||
          cs[i] == '\n' ||
          cs[i] == '(' ||
          cs[i] == ')' ||
          cs[i] == '"' ||
          cs[i] == ';'
        ) {
    i += 1
  }
  let datum = lread(chars_to_string(cs[start:i].to_array()))
  // the delimiting whitespace character is consumed
  if i < n && (cs[i] == ' ' || cs[i] == '\t' || cs[i] == '\n') {
    i += 1
  }
  (datum, i)
}

///|
/// STREAM, EOF-ERROR-P and EOF-VALUE are analogous to the corresponding
/// arguments to Lisp's READ.  REPEAT-IF-NEWLINE, when T, says to repeat the
/// last break command (if available) when only a newline is read.
fn dbm_read(
  stream? : Value,
  eof_error_p? : Value = t,
  eof_value? : Value = Nil,
  repeat_if_newline? : Value = Nil,
) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_input)
  }
  let mprompt = symval(q_ear_mread_prompt)
  with_special(q_ear_mread_prompt, Str(""), () => {
    let out = symval(standard_output)
    let mlen = match mprompt {
      Str(s) => string_length(s)
      Nil => 0
      _ => length(mprompt)
    }
    if symval(q_ear_need_prompt).truthy() && mlen > 0 {
      fresh_line(stream=out) |> ignore
      princ(mprompt, stream=out) |> ignore
      finish_output(stream=out)
      set(q_ear_prompt_on_read_hang, Nil) |> ignore
    } else {
      set(q_ear_prompt_on_read_hang, t) |> ignore
      set(q_ear_read_hang_prompt, mprompt) |> ignore
    }
    // Read a character to see what we should do.
    let mut ch : Value = Nil
    while true {
      ch = read_char(stream~, eof_value~)
      if ch is Char('\n') || ch is Char('\r') {
        if repeat_if_newline.truthy() && symval(q_ear_last_dbm_command).truthy() {
          return symval(q_ear_last_dbm_command)
        }
        continue
      }
      if physical_equal_value(ch, eof_value) || (ch is Nil && eof_value is Nil) {
        if eof_error_p.truthy() {
          raise LispError::SimpleError(
            "end of file on " + prin1_to_string(stream),
          )
        }
        return eof_value
      }
      break
    }
    let c = match ch {
      Char(c) => c
      _ => ' '
    }
    // Put that character back, so we can reread the line correctly.
    unread_char(c, stream~)
    // Figure out what to do
    if c == ':' {
      // This is a Maxima debugger command (I think)
      let line = match read_line(stream~) {
        Some(l) => l
        None =>
          if eof_error_p.truthy() {
            raise LispError::SimpleError(
              "end of file on " + prin1_to_string(stream),
            )
          } else {
            return eof_value
          }
      }
      let (keyword, n) = mdebug__read_from_string(line)
      let mut fun = complete_prop(keyword, q_kw_keyword, q_break_command)
      if consp(fun) {
        fun = car(fun)
      }
      let cmd = if fun is Nil {
        list1(kw("_none"))
      } else if get(fun, q_maxima_read).truthy() {
        cons(
          keyword,
          mapcar(
            s => macsyma_read_string(s),
            split_string_(Str(line), Str(" "), start=int(n)),
          ),
        )
      } else {
        let tem = d_sconcat(
          list([Str("("), Str(string_right_trim(";", line)), Str(")")]),
        )
        lread(lstring(tem))
      }
      set(q_ear_last_dbm_command, cmd)
    } else if c == '?' {
      // Process "?" lines.  This is either a call to describe or a quick
      // temporary escape to Lisp to call some Lisp function.
      //
      // First, read and discard the #\? since we don't need it anymore.
      read_char(stream~) |> ignore
      let next = peek_char(stream~, eof_value=Nil)
      if next is Char(' ') || next is Char('\t') || next is Char('!') {
        // Got "? <stuff>" or "?! <stuff>".  Invoke exact search on
        // <stuff>.
        let line = match read_line(stream~) {
          Some(l) => string_trim(" \t;$", substring(l, 1))
          None => ""
        }
        list([
          list1(q_displayinput),
          Nil,
          list([list1(q_d_describe), Str(line), sym("$exact")]),
        ])
      } else if next is Char('?') {
        // Got "?? <stuff>". Invoke inexact search on <stuff>.
        let line = match read_line(stream~) {
          Some(l) => string_trim(" \t;$", substring(l, 1))
          None => ""
        }
        list([
          list1(q_displayinput),
          Nil,
          list([list1(q_d_describe), Str(line), sym("$inexact")]),
        ])
      } else {
        // Got "?<stuff>" This means a call to a Lisp function.  Pass this
        // on to mread which can handle this.
        unread_char('?', stream~)
        mread(list([stream, eof_value]))
      }
    } else {
      set(q_ear_last_dbm_command, Nil) |> ignore
      let result = mread(list([stream, eof_value]))
      let next_char = mdebug__read_char_no_hang(stream)
      match next_char {
        Char('\n') | Char('\r') => set(q_ear_need_prompt, t) |> ignore
        Char(c) => {
          set(q_ear_need_prompt, Nil) |> ignore
          unread_char(c, stream~)
        }
        _ => set(q_ear_need_prompt, t) |> ignore
      }
      result
    }
  })
}

///|
fn set_env(bkpt : Value) -> Value raise {
  let dbg = symval(q_ear_debug_io)
  format(dbg, "(~a line ~a~@[, in function ~a~])", [
    short_name(nth(1, bkpt)),
    nth(2, bkpt),
    mdebug__cl(nth(3, bkpt)),
  ])
  |> ignore
  suprv1__fmt(dbg, "~&\u{1A}\u{1A}~a:~a::~%", [nth(1, bkpt), nth(2, bkpt)])
}

///|
/// The input side of *debug-io*: the debugger reads the terminal (the
/// console input, or what replaced it, such as a socket).
fn mdebug__debug_input() -> Value {
  match symval(q_ear_debug_io) {
    Stream(st) as s if st.is_input => s
    _ => console_in
  }
}

///|
fn break_dbm_loop(at : Value) -> Value raise {
  let quit_tags = cons(
    cons(symval(q_ear_break_level), symval(q_ear_quit_tag)),
    symval(q_ear_quit_tags),
  )
  let break_level = if at is Nil {
    symval(q_ear_break_level)
  } else {
    cons(t, symval(q_ear_break_level))
  }
  let quit_tag = cons(Nil, Nil)
  with_specials(
    [
      (q_ear_quit_tags, quit_tags),
      (q_ear_break_level, break_level),
      (q_ear_quit_tag, quit_tag),
      (q_ear_break_env, symval(q_ear_break_env)),
      (q_ear_mread_prompt, Str("")),
      (q_ear_diff_bindlist, Nil),
      (q_ear_diff_mspeclist, Nil),
    ],
    () => {
      if consp(at) {
        set_env(at) |> ignore
      }
      if at is Nil {
        break_frame(n=Fix(0L), print_frame_number=Nil) |> ignore
      }
      catch_tag(q_step_continue, () => catch_tag(quit_tag, () => {
        defer {
          (try Some(restore_bindings()) catch { _ => None }) |> ignore
        }
        let dbg = symval(q_ear_debug_io)
        while true {
          format_prompt(
            dbg,
            Str("~&~a"),
            list1(
              format(Nil, "~@[(~a:~a) ~]", [
                if stringp(at) {
                  Nil
                } else {
                  Str("dbm")
                },
                int(length(symval(q_ear_quit_tags))),
              ]),
            ),
          )
          |> ignore
          finish_output(stream=dbg)
          let mut resume = false
          let val = catch_tag(q_macsyma_quit, () => {
            let res = dbm_read(
              stream=mdebug__debug_input(),
              eof_error_p=Nil,
              eof_value=symval(q_ear_top_eof),
              repeat_if_newline=t,
            )
            if consp(res) && mdebug__keywordp(car(res)) {
              let value = break_call(car(res), cdr(res), q_break_command)
              if eq(value, q_kw_resume) {
                resume = true
              }
            } else if physical_equal_value(res, symval(q_ear_top_eof)) {
              funcall(get(kw("top"), q_break_command), []) |> ignore
            } else {
              set(q_d_op__, nth(2, res)) |> ignore
              set(q_d_op_pct, meval_star(symval(q_d_op__))) |> ignore
              set(q_d_op_, symval(q_d_op__)) |> ignore
              displa(symval(q_d_op_pct)) |> ignore
            }
            Nil
          })
          if resume {
            break
          }
          if eql(val, q_top) {
            throw_macsyma_top() |> ignore
          }
        }
        Nil
      }))
    },
  )
}

///|
fn break_quit(level? : Value = Fix(0L)) -> Value raise {
  let current_level = length(symval(q_ear_break_level))
  let level = to_int(level)
  if level >= 0 && level < current_level {
    let x = nth(current_level - level - 1, symval(q_ear_quit_tags))
    if eq(cdr(x), q_macsyma_quit) {
      throw_tag(q_macsyma_quit, q_top) |> ignore
    } else {
      throw_tag(cdr(x), cdr(x)) |> ignore
    }
  }
  throw_tag(q_macsyma_quit, q_top)
}

///|
fn break_current() -> Value raise {
  if symval(q_ear_break_level).truthy() {
    format(symval(q_ear_debug_io), "Back to level ~:@(~S~).", [
      int(length(symval(q_ear_break_level))),
    ])
    |> ignore
  } else {
    suprv1__fmt(symval(q_ear_debug_io), "~&Top level.", []) |> ignore
  }
  Nil
}

///|
fn def_break(keyword : Value, fun : Value, doc : Value) -> Value raise {
  putprop(keyword, fun, q_break_command) |> ignore
  if doc.truthy() {
    putprop(keyword, doc, q_break_doc)
  } else {
    Nil
  }
}

///|
fn break_help(key? : Value = Nil) -> Value raise {
  if key.truthy() {
    if keywordp(key) {
      let vs = complete_prop(key, q_kw_keyword, q_break_doc, return_list=t)
      // COMPLETE-PROP returns the keyword itself when it names a documented
      // command: DOLIST then signals a type error, as in Maxima.
      if !listp(vs) {
        raise LispError::SimpleError(
          "The value " + lstring(mdebug__cl(vs)) + " is not of type LIST",
        )
      }
      for v in vs.iter() {
        suprv1__fmt(t, "~&~%~(~s~)   ~a", [v, get(v, q_break_doc)]) |> ignore
      }
    }
    Nil
  } else {
    // Skip any undocumented break commands
    let mut all : Value = Nil
    let acc = Collector::new()
    for vv in mdebug__keywords() {
      if get(vv, q_break_command).truthy() && get(vv, q_break_doc).truthy() {
        acc.add(cons(vv, get(vv, q_break_doc)))
      }
    }
    all = sort_list(acc.result(), (a, b) => alphalessp(a, b).truthy())
    format(
      t,
      "Break commands start with ':'. Any unique substring may be used,~%eg :r :re :res all work for :resume.~2%Command      Description~%-----------  --------------------------------------",
      [],
    )
    |> ignore
    for vv in all.iter() {
      format(t, "~% ~(~12s~)", [car(vv)]) |> ignore
      format(t, lstring(cdr(vv)), []) |> ignore
    }
    finish_output(stream=symval(standard_output))
    Nil
  }
}

///|
/// The function *BREAK-POINTS*, called by MEVAL1 on a form that has a
/// breakpoint.
fn ear_break_points(form : Value) -> Value raise {
  let bps = symval(q_ear_break_points)
  let mut pos : Value = Nil
  for i in 0..<mdebug__vector_length(bps) {
    if eql(car(aref1(bps, i)), form) {
      pos = int(i)
      break
    }
  }
  format(symval(q_ear_debug_io), "Bkpt ~a: ", [pos]) |> ignore
  break_dbm_loop(aref1(bps, to_int(pos)))
}

///|
/// fun = function name eg '$|odeSeriesSolve| and li = offset from
/// beginning of function.  Or fun = string (filename) and li = absolute
/// position.
fn break_function(
  fun : Value,
  li? : Value = Fix(0L),
  absolute? : Value = Nil,
) -> Value raise {
  let mut fun = fun
  let mut li = li
  if !symval(q_ear_mdebug).truthy() {
    suprv1__fmt(t, "~&Turning on debugging debugmode(true)~%", []) |> ignore
    set(q_ear_mdebug, t) |> ignore
  }
  if stringp(fun) {
    let file = fun
    let mut found = false
    for s in all_symbols() {
      let vv : Value = Sym(s)
      let tem = set_full_lineinfo(vv)
      if tem is Vec(_) {
        let linfo = get_lineinfo(aref1(tem, 1))
        if linfo.truthy() && equal(file, cadr(linfo)) {
          let start = aref1(tem, 0)
          if num_ge(li, start) &&
            num_le(li, num_add(start, int(mdebug__vector_length(tem)))) {
            fun = vv
            li = num_add(num_sub(li, start), Fix(1L))
            found = true
            break
          }
        }
      }
    }
    if !found {
      format(t, "No line info for ~a ", [mdebug__cl(fun)]) |> ignore
      return Nil
    }
  }
  fun = d_concat(list1(fun))
  let tem = second(mgetl(fun, list2(q_mexpr, q_mmacro)))
  let form = third(tem)
  let info = if tem.truthy() { get_lineinfo(form) } else { Nil }
  if tem.truthy() && info.truthy() && eq(third(info), q_src) {
    let mut fun_line = fifth(info)
    if !fixnump(fun_line) {
      fun_line = car(info)
    }
    let i = num_add(
      if absolute.truthy() {
        Fix(0L)
      } else {
        fun_line
      },
      li,
    )
    let form = first_form_line(form, i)
    if form is Nil {
      if eql(li, Fix(0L)) {
        return break_function(fun, li=Fix(1L))
      }
      suprv1__fmt(t, "~& No instructions recorded for this line ~a of ~a", [
        li,
        d_sconcat(list1(fun)),
      ])
      |> ignore
      return Nil
    }
    let n = insert_break_point(list([form, cadr(info), i, fun]))
    suprv1__fmt(t, "~&Bkpt ~a for ~a (in ~a line ~a) ~%", [
      n,
      d_sconcat(list1(fun)),
      cadr(info),
      i,
    ])
    |> ignore
    n
  } else {
    format(t, "No line info for ~a ", [mdebug__cl(fun)])
  }
}

// note need to make the redefine function, fixup the break point list..

///|
fn make_break_point(fun : Value, ar : Value, i : Value) -> Value raise {
  let tem = aref1(ar, to_int(i))
  let linfo = get_lineinfo(tem)
  if linfo.truthy() {
    list([tem, cadr(linfo), car(linfo), fun])
  } else {
    Nil
  }
}

///|
fn dbm_up(n : Value) -> Value raise {
  let cur = to_int(symval(q_ear_current_frame))
  let m = mdebug__vector_length(symval(q_ear_mlambda_call_stack)) / 5
  let mut n = to_int(n) + cur
  if n > m {
    n = m
  } else if n < 0 {
    n = 0
  }
  break_frame(n=int(n), print_frame_number=Nil)
}

///|
fn insert_break_point(bpt : Value) -> Value raise {
  if symval(q_ear_break_points) is Nil {
    init_break_points() |> ignore
  }
  let bps = symval(q_ear_break_points)
  let at : Value = match mdebug__position(Nil, bps) {
    Value::Nil => {
      let l = mdebug__vector_length(bps)
      vector_push_extend(Nil, bps) |> ignore
      int(l)
    }
    p => p
  }
  let fun = nth(3, bpt)
  putprop(fun, cons(at, get(fun, q_break_points)), q_break_points) |> ignore
  aset1(bps, to_int(at), bpt) |> ignore
  at
}

///|
fn short_name(name : Value) -> Value raise {
  let cs = string_chars(lstring(name))
  let mut pos = -1
  for i, c in cs {
    if c == '/' {
      pos = i
    }
  }
  if pos >= 0 {
    Str(chars_to_string(cs[pos + 1:].to_array()))
  } else {
    name
  }
}

///|
fn show_break_point(n : Value) -> Value raise {
  let mut bpt = aref1(symval(q_ear_break_points), to_int(n))
  let mut disabled = false
  if bpt.truthy() {
    if car(bpt) is Nil {
      disabled = true
      bpt = cdr(bpt)
    }
    format(t, "Bkpt ~a: (~a line ~a)~@[ (disabled)~]", [
      n,
      short_name(second(bpt)),
      third(bpt),
      lbool(disabled),
    ])
    |> ignore
    let fun = fourth(bpt)
    format(t, " (line ~a of ~a)", [
      relative_line(fun, nth(2, bpt)),
      mdebug__cl(fun),
    ])
  } else {
    Nil
  }
}

///|
fn relative_line(fun : Value, l : Value) -> Value raise {
  let info = set_full_lineinfo(fun)
  if info.truthy() {
    num_sub(l, aref1(info, 0))
  } else {
    Fix(0L)
  }
}

///|
fn iterate_over_bkpts(l : Value, action : Value) -> Value raise {
  let bps = symval(q_ear_break_points)
  for i in 0..<mdebug__vector_length(bps) {
    if member(int(i), l).truthy() || l is Nil {
      let mut tem = aref1(bps, i)
      let newv : Value = if eq(action, kw("delete")) {
        if car(tem) is Nil {
          // disabled or already deleted bkpt
          tem = cdr(tem)
        }
        if tem.truthy() {
          let fun = nth(3, tem)
          putprop(fun, delete(int(i), get(fun, q_break_points)), q_break_points)
          |> ignore
        }
        Nil
      } else if eq(action, kw("enable")) {
        if car(tem) is Nil {
          cdr(tem)
        } else {
          tem
        }
      } else if eq(action, kw("disable")) {
        if tem.truthy() && !(car(tem) is Nil) {
          cons(Nil, tem)
        } else {
          tem
        }
      } else if eq(action, kw("show")) {
        if tem.truthy() {
          show_break_point(int(i)) |> ignore
          terpri(stream=symval(standard_output))
          finish_output(stream=symval(standard_output))
        }
        tem
      } else {
        Nil
      }
      aset1(bps, i, newv) |> ignore
    }
  }
  Nil
}

///|
/// Get the most recent function on the stack with step info.
fn current_step_fun() -> Value raise {
  for i in 0..<100000 {
    let fun = frame_info(int(i)).0
    if fun is Nil {
      break
    }
    if symbolp(fun) && set_full_lineinfo(fun).truthy() {
      return fun
    }
  }
  Nil
}

///|
/// The macro LISP-QUIET: evaluate the Lisp forms without printing a
/// prompt.
fn lisp_quiet(l_lisp_quiet : Value) -> Value raise {
  let prompt = symval(q_ear_mread_prompt)
  if !(prompt is Str("")) {
    set(q_ear_lisp_quiet_suppressed_prompt, prompt) |> ignore
  }
  set(q_ear_mread_prompt, Str("")) |> ignore
  lisp_eval_form(cons(q_progn, l_lisp_quiet)) |> ignore
  Nil
}

///|
/// The macro LISP-EVAL: evaluate the Lisp forms and print their values.
fn lisp_eval(l_lisp_eval : Value) -> Value raise {
  if symval(q_ear_mread_prompt) is Str("") {
    set(q_ear_mread_prompt, symval(q_ear_lisp_quiet_suppressed_prompt))
    |> ignore
  }
  let v_lisp_eval = lisp_eval_form(cons(q_progn, l_lisp_eval))
  fresh_line(stream=symval(standard_output)) |> ignore
  princ(v_lisp_eval) |> ignore
  Nil
}

///|
/// The macro DO-BREAK: set a breakpoint.
fn do_break(name? : Value = Nil, l : Value) -> Value raise {
  if name is Nil {
    let last = if boundp(q_ear_last_dbl_break) {
      symval(q_ear_last_dbl_break)
    } else {
      raise LispError::SimpleError(
        "The variable *LAST-DBL-BREAK* is unbound.",
      )
    }
    if last.truthy() {
      let fun = nth(3, last)
      break_function(fun, li=nth(2, last), absolute=t)
    } else {
      Nil
    }
  } else {
    // (eval `(break-function ',name ,@l))
    let args = list_to_array(l).map(a => mdebug__eval_arg(a))
    match args.length() {
      0 => break_function(name)
      1 => break_function(name, li=args[0])
      _ => break_function(name, li=args[0], absolute=args[1])
    }
  }
}

///|
/// This just sets up a counter for each stream.. we want it to start at
/// one.
fn get_lineinfo(form : Value) -> Value raise {
  if consp(form) {
    if consp(cadar(form)) {
      cadar(form)
    } else if consp(caddar(form)) {
      caddar(form)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// restore-bindings from an original binding list.
fn restore_bindings() -> Value raise {
  mbind(symval(q_ear_diff_bindlist), symval(q_ear_diff_mspeclist), Nil)
  |> ignore
  set(q_ear_diff_bindlist, Nil) |> ignore
  set(q_ear_diff_mspeclist, Nil)
}

///|
fn remove_bindings(the_bindlist : Value) -> Value raise {
  let mut v = symval(q_bindlist)
  while v.truthy() {
    if eq(v, the_bindlist) {
      break
    }
    let var_ = car(v)
    set(q_ear_diff_bindlist, cons(var_, symval(q_ear_diff_bindlist))) |> ignore
    set(q_ear_diff_mspeclist, cons(symval(var_), symval(q_ear_diff_mspeclist)))
    |> ignore
    if eq(car(symval(q_mspeclist)), symval(q_munbound)) {
      makunbound(var_) |> ignore
      // (setq $values (delete var $values :count 1 :test #'eq))
      let vals = symval(q_d_values)
      let mut prev : Value = Nil
      let mut cur = vals
      while cur.truthy() {
        if eq(car(cur), var_) {
          if prev is Nil {
            set(q_d_values, cdr(cur)) |> ignore
          } else {
            setf_cdr(prev, cdr(cur)) |> ignore
          }
          break
        }
        prev = cur
        cur = cdr(cur)
      }
    } else {
      with_special(q_munbindp, t, () => mset(var_, car(symval(q_mspeclist))))
      |> ignore
    }
    set(q_mspeclist, cdr(symval(q_mspeclist))) |> ignore
    set(q_bindlist, cdr(symval(q_bindlist))) |> ignore
    v = cdr(v)
  }
  Nil
}

///|
fn break_frame(n? : Value = Fix(0L), print_frame_number? : Value = t) -> Value raise {
  restore_bindings() |> ignore
  let (_fname, _vals, _params, _backtr, lineinfo, bdlist) = print_one_frame(
    n, print_frame_number,
  )
  remove_bindings(bdlist) |> ignore
  if lineinfo.truthy() {
    let dbg = symval(q_ear_debug_io)
    fresh_line(stream=dbg) |> ignore
    format(dbg, "\u{1A}\u{1A}~a:~a::~%", [cadr(lineinfo), num_add(Fix(0L), car(lineinfo))])
    |> ignore
  }
  Nil
}

///|
/// The breakpoint check of MEVAL1 under debugmode: if wanting to step, the
/// *break-points* variable will be set to a vector (possibly empty).  Always
/// false (the COND clause of MEVAL1 it stands for only has side effects).
fn mdebug__meval1_check(form : Value) -> Bool raise {
  let bps = symval(q_ear_break_points)
  if bps.truthy() {
    let step = symval(q_ear_break_step)
    if step is Nil || funcall(step, [form]) is Nil {
      let ar = symval(q_ear_break_points)
      for i in 0..<fill_pointer(ar) {
        if eq(car(aref1(ar, i)), form) {
          ear_break_points(form) |> ignore
          break
        }
      }
    }
  }
  false
}

///|
fn init_mdebug() -> Unit raise {
  defvar_init(q_ear_break_point_vector, make_array([10], fill=0))
  defvar_init(q_ear_top_eof, cons(Nil, Nil))
  def_break(
    kw("help"),
    q_break_help,
    Str(
      "Print help on a break command or with no arguments on\n             all break commands",
    ),
  )
  |> ignore
  // This is an undocumented break command which gets placed in
  // *LAST-DBM-COMMAND* when an invalid (nonexistent or ambiguous) break
  // command is read in.
  def_break(kw("_none"), lfunc("break-none", _ => Nil), Nil) |> ignore
  def_break(
    kw("next"),
    q_step_next,
    Str("Like :step, except that subroutine calls are stepped over"),
  )
  |> ignore
  def_break(
    kw("step"),
    q_step_into,
    Str("Step program until it reaches a new source line"),
  )
  |> ignore
  def_break(kw("quit"), q_break_quit, Str("Quit this level")) |> ignore
  def_break(
    kw("top"),
    lfunc("break-top", _ => throw_tag(q_macsyma_quit, q_top)),
    Str("Throw to top level"),
  )
  |> ignore
  def_break(
    kw("bt"),
    q_d_backtrace,
    Str("Print a backtrace of the stack frames"),
  )
  |> ignore
  def_break(
    kw("info"),
    lfunc("break-info", args => {
      let type_ = if args.length() > 0 { args[0] } else { Nil }
      if eq(type_, kw("bkpt")) {
        iterate_over_bkpts(Nil, kw("show")) |> ignore
        Nil
      } else {
        format(
          symval(q_ear_debug_io),
          "usage: :info :bkpt -- show breakpoints",
          [],
        )
      }
    }),
    Str("Print information about item"),
  )
  |> ignore
  def_break(
    kw("lisp-quiet"),
    q_lisp_quiet,
    Str("Evaluate the lisp form without printing a prompt"),
  )
  |> ignore
  def_break(
    kw("lisp"),
    q_lisp_eval,
    Str("Evaluate the lisp form following on the line"),
  )
  |> ignore
  def_break(
    kw("delete"),
    lfunc("break-delete", args => {
      iterate_over_bkpts(list(args), kw("delete")) |> ignore
      Nil
    }),
    Str(
      "Delete all breakpoints, or if arguments are supplied delete the\n             specified breakpoints",
    ),
  )
  |> ignore
  def_break(
    kw("frame"),
    q_break_frame,
    Str(
      "With an argument print the selected stack frame.\n             Otherwise the current frame.",
    ),
  )
  |> ignore
  def_break(
    kw("resume"),
    lfunc("break-resume", _ => q_kw_resume),
    Str("Continue the computation."),
  )
  |> ignore
  def_break(
    kw("continue"),
    lfunc("break-continue", _ => q_kw_resume),
    Str("Continue the computation."),
  )
  |> ignore
  def_break(
    kw("disable"),
    lfunc("break-disable", args => {
      iterate_over_bkpts(list(args), kw("disable")) |> ignore
      Nil
    }),
    Str("Disable the specified breakpoints, or all if none are specified"),
  )
  |> ignore
  def_break(
    kw("enable"),
    lfunc("break-enable", args => {
      iterate_over_bkpts(list(args), kw("enable")) |> ignore
      Nil
    }),
    Str("Enable the specified breakpoints, or all if none are specified"),
  )
  |> ignore
  def_break(
    kw("break"),
    q_do_break,
    Str(
      "Set a breakpoint in the specified FUNCTION at the\n             specified LINE offset from the beginning of the function.\n             If FUNCTION is given as a string, then it is presumed to be\n             a FILE and LINE is the offset from the beginning of the file.",
    ),
  )
  |> ignore
  // force the rest of the line to be broken at spaces, and each item read
  // as a maxima atom.
  putprop(kw("break"), t, q_maxima_read) |> ignore
}
