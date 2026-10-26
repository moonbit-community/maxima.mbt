// Port of src/mforma.lisp: a mini version of FORMAT for macsyma error
// messages -- the compile-time half: macros defining an MFORMAT string
// interpreter, the compile-time syntax checker and the open-compiler
// (MFORMAT-TRANSLATE-OPEN).  The run-time interpreter is in mformt.
//
// Most macros of this file expand into code with free variables (SSTRING,
// ARG-INDEX, N, TEXT-TEMP, ...) that only make sense inside an
// MFORMAT-LOOP definition; their declared functions return that
// expansion (Lisp code as data).  The definition macros
// (+DEF-MFORMAT-VAR, +DEF-MFORMAT-OP and their -C versions) perform their
// macroexpansion-time side effects on the type's property list.
// MFORMAT-TRANSLATE-OPEN is translated directly (the expansion of
// MFORMAT-LOOP-C with the -C ops inlined).  Backquoted code in these
// expansions is written as (backquote ...) / (comma ...) lists, since the
// runtime reader has no backquote syntax.

///|
let mforma__q_state_vars : Value = sym("mformat-state-vars")

///|
let mforma__q_ops : Value = sym("mformat-ops")

///|
let mforma__q_c : Value = sym("-c")

///|
let mforma__q_colon_flag : Value = sym(":-flag")

///|
let mforma__q_at_flag : Value = sym("@-flag")

///|
let mforma__q_parameter : Value = sym("parameter")

///|
let mforma__q_text_temp : Value = sym("text-temp")

///|
let mforma__q_code : Value = sym("code")

///|
let mforma__q_char : Value = sym("char")

///|
let mforma__q_want_open : Value = sym("*want-open-compiled-mformat*")

///|
let mforma__q_cant_open : Value = sym("*cant-open-compile-mformat*")

///|
/// `(+def-mformat-var type var val init-condition)`: record (VAR VAL)
/// among the state variables of TYPE reset when INIT-CONDITION holds.
fn n_plusdef_mformat_var(
  type_ : Value,
  var_ : Value,
  val : Value,
  init_condition : Value,
) -> Value raise {
  let mut entry = assoc(init_condition, get(type_, mforma__q_state_vars))
  if entry is Nil {
    entry = list1(init_condition)
    setf_get(
      type_,
      mforma__q_state_vars,
      cons(entry, get(type_, mforma__q_state_vars)),
    )
    |> ignore
  }
  rplacd(entry, cons(list2(var_, val), cdr(entry))) |> ignore
  var_
}

///|
/// `(+def-mformat-op type char &rest body)`: CHAR can also be a list of
/// characters.  Returns the name of the op.
fn n_plusdef_mformat_op(
  type_ : Value,
  char_ : Value,
  body : Value,
) -> Value raise {
  let chars = if atom(char_) { list1(char_) } else { char_ }
  setf_get(
    type_,
    mforma__q_ops,
    cons(cons(chars, body), get(type_, mforma__q_ops)),
  )
  |> ignore
  maknam(nconc(exploden(Str("mformat-")), mapcar(c => ascii(c), chars)))
}

///|
fn pop_mformat_arg() -> Value raise {
  lread(
    "(cond ((= arg-index n) (maxima-error \"POP-MFORMAT-ARG: ran out of mformat args ~a\" (listify n))) (t (incf arg-index) (arg arg-index)))",
  )
}

///|
/// To be called after we are done.
fn leftover_mformat_args_q() -> Value raise {
  lread(
    "(unless (= arg-index n) (maxima-error \"LEFTOVER-MFORMAT-ARGS?: extra mformat args ~a\" (listify n)))",
  )
}

///|
/// `(bind-mformat-state-vars type &rest body)`: `(let <state vars> ,@body)`
fn bind_mformat_state_vars(type_ : Value, body : Value) -> Value raise {
  let mut l : Value = Nil
  for v in get(type_, mforma__q_state_vars).iter() {
    for c in cdr(v).iter() {
      l = cons(c, l)
    }
  }
  cons(q_let, cons(l, body))
}

///|
fn pop_mformat_string() -> Value raise {
  lread(
    "(if (null sstring) (maxima-error \"POP-MFORMAT-STRING: 'mformat' string already exhausted.\") (pop sstring))",
  )
}

///|
fn null_mformat_string() -> Value raise {
  lread("(null sstring)")
}

///|
fn top_mformat_string() -> Value raise {
  lread(
    "(if (null sstring) (maxima-error \"TOP-MFORMAT-STRING: 'mformat' string already exhausted.\") (car sstring))",
  )
}

///|
fn cdr_mformat_string() -> Value raise {
  lread("(setq sstring (cdr sstring))")
}

///|
/// The dispatch on the directive character for the ops of TYPE, followed
/// by the resetting of the state variables.
fn mformat_dispatch_on_char(type_ : Value) -> Value raise {
  let char_equal = sym("char-equal")
  let clauses = mapcar(
    pair => {
      let test_ = if atom(car(pair)) {
        list3(char_equal, mforma__q_char, car(pair))
      } else {
        cons(
          sym("or"),
          mapcar(c => list3(char_equal, mforma__q_char, c), car(pair)),
        )
      }
      cons(test_, cdr(pair))
    },
    get(type_, mforma__q_ops),
  )
  let default_clause = list2(
    t,
    list4(
      sym("maxima-error"),
      Str("MFORMAT-DISPATCH-ON-CHAR: unknown format op. _~a_ ~a"),
      list2(q_quote, type_),
      list2(q_ascii, mforma__q_char),
    ),
  )
  let resets = mapcar(
    state => {
      list3(sym("if"), car(state), cons(q_setq, apply(q_append, cdr(state))))
    },
    get(type_, mforma__q_state_vars),
  )
  cons(
    q_progn,
    cons(cons(q_cond, append(clauses, list1(default_clause))), resets),
  )
}

///|
/// The whitespace characters skipped after ~.
fn white_space_p(x : Value) -> Value raise {
  let ws = list([
    Char('\n'),
    Char('\r'),
    Char(' '),
    Char('\t'),
    Char('\u{0C}'),
    Char('\u{0B}'),
  ])
  match x {
    Char(_) => member(x, ws)
    _ => raise type_error(x, "character")
  }
}

///|
/// `(+mformat-loop type &rest end-code)`: the interpreter loop.
fn n_plusmformat_loop(type_ : Value, end_code : Value) -> Value raise {
  let template = lread(
    "(do ((char)) ((null-mformat-string) (leftover-mformat-args?) %%end-code%%) (setq char (pop sstring)) (cond ((char= char #\\~) (do () (nil) (setq char (pop-mformat-string)) (cond ((char= char #\\@) (setq @-flag t)) ((char= char #\\:) (setq :-flag t)) ((char= char #\\~) (push char text-temp) (return nil)) ((white-space-p char) (do () ((not (white-space-p (top-mformat-string)))) (cdr-mformat-string)) (return nil)) ((or (char< char #\\0) (char> char #\\9)) %%dispatch%% (return nil)) (t (setq parameter (+ (- (char-code char) (char-code #\\0)) (* 10 parameter))))))) (t (push char text-temp))))",
  )
  // splice END-CODE into the end clause and the dispatch form
  let end_clause = caddr(template)
  let end_tail = cddr(end_clause)
  rplaca(end_tail, car(end_code)) |> ignore
  if end_code is Nil {
    rplacd(cdr(end_clause), Nil) |> ignore
  } else {
    rplacd(end_tail, cdr(end_code)) |> ignore
  }
  let body = subst(
    list2(sym("mformat-dispatch-on-char"), type_),
    sym("%%dispatch%%"),
    template,
  )
  list3(sym("bind-mformat-state-vars"), type_, body)
}

///|
/// `(def-mformat-op-c char &rest body)`
fn def_mformat_op_c(char_ : Value, body : Value) -> Value raise {
  n_plusdef_mformat_op(mforma__q_c, char_, body)
}

///|
/// `(def-mformat-var-c var val init)`
fn def_mformat_var_c(var_ : Value, val : Value, init_ : Value) -> Value raise {
  n_plusdef_mformat_var(mforma__q_c, var_, val, init_)
}

///|
/// `(mformat-loop-c &rest endcode)`
fn mformat_loop_c(endcode : Value) -> Value raise {
  n_plusmformat_loop(mforma__q_c, endcode)
}

///|
/// `(emitc x)` = `(push x code)`
fn emitc(x : Value) -> Value raise {
  list3(sym("push"), x, mforma__q_code)
}

///|
fn push_text_temp_c() -> Value raise {
  lread(
    "(and text-temp (progn (emitc (backquote (princ (quote (comma (maknam (nreverse text-temp)))) (comma stream)))) (setq text-temp nil)))",
  )
}

///|
/// Should remove extra calls to TERPRI around DISPLA.  Mainly want to
/// remove (PRINC FOO NIL) => (PRINC FOO) although I'm not sure this is
/// correct.
fn optimize_print_inst(l : Value) -> Value raise {
  let mut l = l
  let mut new : Value = Nil
  while !(l is Nil) {
    let a = car(l)
    l = cdr(l)
    if eq(car(a), q_terpri) {
      if cadr(a) is Nil {
        new = cons(list1(q_terpri), new)
      } else {
        new = cons(a, new)
      }
    } else if caddr(a) is Nil && !eq(car(a), q_mgrind) {
      if eq(car(a), q_displaf) {
        new = cons(list2(q_displa, cadr(a)), new)
      } else {
        new = cons(list2(car(a), cadr(a)), new)
      }
    } else {
      new = cons(a, new)
    }
  }
  cons(q_progn, new)
}

///|
/// Open-compile `(mformat stream "string" args...)` into Lisp printing
/// code.  N is the list of all arguments (a Maclisp lexpr).
fn mformat_translate_open(n : Value) -> Value raise {
  let nargs = length(n)
  let stream = narg1(Fix(1L), n)
  let mut sstring = exploden(narg1(Fix(2L), n))
  with_specials([(mforma__q_want_open, t), (mforma__q_cant_open, Nil)], () => {
    let mut arg_index = 2
    // state variables reset after each directive
    let mut colon_flag = false
    let mut at_flag = false
    let mut parameter = 0
    // state variables never reset
    let mut text_temp : Value = Nil
    let mut code : Value = Nil
    let pop_arg = () => {
      if arg_index == nargs {
        maxima_error(
          Str("POP-MFORMAT-ARG: ran out of mformat args ~a"),
          list1(listify1(int(nargs), n)),
        )
        |> ignore
      }
      arg_index += 1
      narg1(int(arg_index), n)
    }
    let push_text_temp = () => {
      if text_temp.truthy() {
        code = cons(
          list3(q_princ, list2(q_quote, maknam(nreverse(text_temp))), stream),
          code,
        )
        text_temp = Nil
      }
    }
    let pop_string = () => {
      if sstring is Nil {
        maxima_error(
          Str("POP-MFORMAT-STRING: 'mformat' string already exhausted."),
          Nil,
        )
        |> ignore
      }
      let c = car(sstring)
      sstring = cdr(sstring)
      c
    }
    let top_string = () => {
      if sstring is Nil {
        maxima_error(
          Str("TOP-MFORMAT-STRING: 'mformat' string already exhausted."),
          Nil,
        )
        |> ignore
      }
      car(sstring)
    }
    let want_open = () => symval(mforma__q_want_open).truthy()
    let dispatch = (ch : Char) => {
      let c = char_upcase(ch)
      if c == '%' || c == '&' {
        if want_open() {
          push_text_temp()
          if ch == '&' {
            code = cons(list2(sym("fresh-line"), stream), code)
          } else {
            code = cons(list2(q_terpri, stream), code)
          }
        }
      } else if c == 'M' {
        if want_open() {
          push_text_temp()
          let f = if colon_flag { q_mgrind } else { q_displaf }
          let g = if at_flag { q_getop } else { q_progn }
          code = cons(list3(f, list2(g, pop_arg()), stream), code)
        } else {
          pop_arg() |> ignore
        }
      } else if c == 'A' || c == 'S' {
        if want_open() {
          push_text_temp()
          let f = if c == 'A' { q_princ } else { q_prin1 }
          code = cons(list3(f, pop_arg(), stream), code)
        } else {
          pop_arg() |> ignore
        }
      } else {
        maxima_error(
          Str("MFORMAT-DISPATCH-ON-CHAR: unknown format op. _~a_ ~a"),
          list2(mforma__q_c, ascii(Char(ch))),
        )
        |> ignore
      }
      colon_flag = false
      at_flag = false
      parameter = 0
    }
    let is_ws = (c : Value) => white_space_p(c).truthy()
    while !(sstring is Nil) {
      let ch = car(sstring)
      sstring = cdr(sstring)
      if eql(ch, Char('~')) {
        while true {
          let c = pop_string()
          let cc = match c {
            Char(x) => x
            _ => raise type_error(c, "character")
          }
          if cc == '@' {
            at_flag = true
          } else if cc == ':' {
            colon_flag = true
          } else if cc == '~' {
            text_temp = cons(c, text_temp)
            break
          } else if is_ws(c) {
            while is_ws(top_string()) {
              sstring = cdr(sstring)
            }
            break
          } else if cc < '0' || cc > '9' {
            dispatch(cc)
            break
          } else {
            parameter = cc.to_int() - '0'.to_int() + 10 * parameter
          }
        }
      } else {
        text_temp = cons(ch, text_temp)
      }
    }
    ignore(parameter)
    // (leftover-mformat-args?)
    if arg_index != nargs {
      maxima_error(
        Str("LEFTOVER-MFORMAT-ARGS?: extra mformat args ~a"),
        list1(listify1(int(nargs), n)),
      )
      |> ignore
    }
    push_text_temp()
    if symval(mforma__q_cant_open).truthy() {
      maxima_error(
        Str(
          "MFORMAT-TRANSLATE-OPEN: can't open compile 'mformat' on this case: ~a",
        ),
        list1(listify1(int(nargs), n)),
      )
      |> ignore
    }
    optimize_print_inst(code)
  })
}

///|
/// `(mformat-open stream sstring &rest other-shit)`
fn mformat_open(
  stream : Value,
  sstring : Value,
  other_shit : Value,
) -> Value raise {
  if !stringp(sstring) {
    maxima_error(
      Str(
        "MFORMAT-OPEN: ~a is not a string, can't open-compile the 'mformat' call.",
      ),
      list1(sstring),
    )
  } else {
    mformat_translate_open(cons(stream, cons(sstring, other_shit)))
  }
}

///|
/// `(mtell-open message &rest other-shit)`
fn mtell_open(message : Value, other_shit : Value) -> Value raise {
  mformat_open(Nil, message, other_shit)
}

///|
fn init_mforma() -> Unit raise {
  macsyma_module(sym("mforma"), list1(q_macro)) |> ignore
  setf_get(mforma__q_c, mforma__q_ops, Nil) |> ignore
  setf_get(mforma__q_c, mforma__q_state_vars, Nil) |> ignore
  def_mformat_var_c(mforma__q_colon_flag, Nil, t) |> ignore
  def_mformat_var_c(mforma__q_at_flag, Nil, t) |> ignore
  def_mformat_var_c(mforma__q_parameter, Fix(0L), t) |> ignore
  def_mformat_var_c(mforma__q_text_temp, Nil, Nil) |> ignore
  def_mformat_var_c(mforma__q_code, Nil, Nil) |> ignore
  // The -C ops (their bodies are used by MFORMAT-DISPATCH-ON-CHAR; the
  // open-compiler above inlines them).
  def_mformat_op_c(
    list2(Char('%'), Char('&')),
    lread(
      "((cond (*want-open-compiled-mformat* (push-text-temp-c) (if (char= char #\\&) (emitc (backquote (fresh-line (comma stream)))) (emitc (backquote (terpri (comma stream))))))))",
    ),
  )
  |> ignore
  def_mformat_op_c(
    Char('M'),
    lread(
      "((cond (*want-open-compiled-mformat* (push-text-temp-c) (emitc (backquote ((comma (if :-flag 'mgrind 'displaf)) ((comma (if @-flag 'getop 'progn)) (comma (pop-mformat-arg))) (comma stream))))) (t (pop-mformat-arg))))",
    ),
  )
  |> ignore
  def_mformat_op_c(
    list2(Char('A'), Char('S')),
    lread(
      "((cond (*want-open-compiled-mformat* (push-text-temp-c) (emitc (backquote ((comma (if (char-equal char #\\A) 'princ 'prin1)) (comma (pop-mformat-arg)) (comma stream))))) (t (pop-mformat-arg))))",
    ),
  )
  |> ignore
}
