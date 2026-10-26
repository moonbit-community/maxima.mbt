// Lisp evaluator: the standard CL macros, written as MoonBit expanders
// (form, environment) -> expansion.

///|
type LeExpander = (Value, LeEnv) -> Value raise

///|
fn le__s(name : String) -> Value {
  sym(name)
}

///|
fn le__quote(x : Value) -> Value {
  list2(sym("quote"), x)
}

///|
fn le__progn(body : Value) -> Value {
  match body {
    Cons({ car: x, cdr: Nil }) => x
    _ => cons(sym("progn"), body)
  }
}

///|
fn le__gensym(prefix : String) -> Value {
  gensym(prefix~)
}

///|
fn le__make_builtin_macro_table() -> Map[String, LeExpander] {
  {
  "lambda": le__m_lambda,
  "when": le__m_when,
  "unless": le__m_unless,
  "cond": le__m_cond,
  "and": le__m_and,
  "or": le__m_or,
  "case": le__m_case,
  "ecase": le__m_ecase,
  "ccase": le__m_ecase,
  "typecase": le__m_typecase,
  "etypecase": le__m_etypecase,
  "ctypecase": le__m_etypecase,
  "do": le__m_do,
  "do*": le__m_do_star,
  "dolist": le__m_dolist,
  "dotimes": le__m_dotimes,
  "prog": le__m_prog,
  "prog*": le__m_prog_star,
  "prog1": le__m_prog1,
  "prog2": le__m_prog2,
  "return": le__m_return,
  "psetq": le__m_psetq,
  "psetf": le__m_psetq,
  "setf": le__m_setf,
  "incf": le__m_incf,
  "decf": le__m_decf,
  "push": le__m_push,
  "pushnew": le__m_pushnew,
  "pop": le__m_pop,
  "remf": le__m_remf,
  "shiftf": le__m_shiftf,
  "rotatef": le__m_rotatef,
  "multiple-value-list": le__m_mv_list,
  "multiple-value-setq": le__m_mv_setq,
  "nth-value": le__m_nth_value,
  "defvar": le__m_defvar,
  "defparameter": le__m_defparameter,
  "defconstant": le__m_defconstant,
  "defsetf": le__m_defsetf,
  "deftype": le__m_ignore_quoted_name,
  "declaim": le__m_declaim,
  "in-package": le__m_in_package,
  "defpackage": le__m_ignore_quoted_name,
  "check-type": le__m_check_type,
  "assert": le__m_assert,
  "with-output-to-string": le__m_with_output_to_string,
  "with-input-from-string": le__m_with_input_from_string,
  "with-open-file": le__m_with_open_file,
  "with-open-stream": le__m_with_open_stream,
  "with-standard-io-syntax": le__m_progn_body,
  "with-compilation-unit": le__m_with_compilation_unit,
  "handler-case": le__m_handler_case,
  "handler-bind": le__m_handler_bind,
  "ignore-errors": le__m_ignore_errors,
  "restart-case": le__m_restart_case,
  "with-simple-restart": le__m_with_simple_restart,
  "time": le__m_time,
  "loop": le__m_loop,
  "loop-finish": le__m_loop_finish,
  "defstruct": le__m_defstruct,
  "define-condition": le__m_define_condition,
  "do-symbols": le__m_do_symbols,
  "do-all-symbols": le__m_do_symbols,
  "do-external-symbols": le__m_do_symbols,
  "define-modify-macro": le__m_define_modify_macro,
  "defgeneric": le__m_defgeneric,
  "defmethod": le__m_defmethod,
  "defclass": le__m_ignore_quoted_name,
  "print-unreadable-object": le__m_print_unreadable_object,
  "with-slots": le__m_unsupported,
  "define-compiler-macro": le__m_ignore_quoted_name,
  "define-symbol-macro": le__m_define_symbol_macro,
  "step": le__m_progn_body,
  "trace": le__m_ignore,
  "si::modify-place": le__m_modify_place,
  "defmfun": le__m_defmfun,
  "untrace": le__m_ignore,
  }
}

///|
let le__builtin_macro_table : Ref[Map[String, LeExpander]?] = Ref(None)

///|
fn le__builtin_macros() -> Map[String, LeExpander] {
  match le__builtin_macro_table.val {
    Some(m) => m
    None => {
      let m = le__make_builtin_macro_table()
      le__builtin_macro_table.val = Some(m)
      m
    }
  }
}

///|
fn le__m_lambda(form : Value, _env : LeEnv) -> Value raise {
  list2(sym("function"), form)
}

///|
fn le__m_when(form : Value, _env : LeEnv) -> Value raise {
  list3(sym("if"), cadr(form), le__progn(cddr(form)))
}

///|
fn le__m_unless(form : Value, _env : LeEnv) -> Value raise {
  list4(sym("if"), cadr(form), Nil, le__progn(cddr(form)))
}

///|
fn le__m_cond(form : Value, _env : LeEnv) -> Value raise {
  let clauses = list_to_array(cdr(form))
  let mut r : Value = Nil
  for k = clauses.length() - 1; k >= 0; k = k - 1 {
    let cl = clauses[k]
    let tst = car(cl)
    let body = cdr(cl)
    if body is Nil {
      // (cond (x) ...) returns x's value
      if r is Nil {
        r = tst
      } else {
        let g = le__gensym("cond")
        r = list3(
          sym("let"),
          list1(list2(g, tst)),
          list4(sym("if"), g, g, r),
        )
      }
    } else if eq(tst, t) && r is Nil {
      r = le__progn(body)
    } else {
      r = list4(sym("if"), tst, le__progn(body), r)
    }
  }
  r
}

///|
fn le__m_and(form : Value, _env : LeEnv) -> Value raise {
  let args = list_to_array(cdr(form))
  if args.length() == 0 {
    return t
  }
  let mut r = args[args.length() - 1]
  for k = args.length() - 2; k >= 0; k = k - 1 {
    r = list3(sym("if"), args[k], r)
  }
  r
}

///|
fn le__m_or(form : Value, _env : LeEnv) -> Value raise {
  let args = list_to_array(cdr(form))
  if args.length() == 0 {
    return Nil
  }
  let mut r = args[args.length() - 1]
  for k = args.length() - 2; k >= 0; k = k - 1 {
    let g = le__gensym("or")
    r = list3(
      sym("let"),
      list1(list2(g, args[k])),
      list4(sym("if"), g, g, r),
    )
  }
  r
}

///|
fn le__case_expand(form : Value, error_kind : Int) -> Value {
  let g = le__gensym("key")
  let clauses = list_to_array(cddr(form))
  let mut r : Value = if error_kind == 1 {
    list3(
      sym("error"),
      Str("~S fell through ECASE expression."),
      g,
    )
  } else {
    Nil
  }
  for k = clauses.length() - 1; k >= 0; k = k - 1 {
    let cl = clauses[k]
    let keys = car(cl)
    let body = le__progn(cdr(cl))
    let body = if cdr(cl) is Nil { Value::Nil } else { body }
    if (eq(keys, t) || eq(keys, sym("otherwise"))) && k == clauses.length() - 1 {
      r = body
    } else {
      let tst = match keys {
        Nil => Value::Nil
        Cons(_) => list3(sym("si::memql"), g, le__quote(keys))
        _ => list3(sym("eql"), g, le__quote(keys))
      }
      r = list4(sym("if"), tst, body, r)
    }
  }
  list3(sym("let"), list1(list2(g, cadr(form))), r)
}

///|
fn le__m_case(form : Value, _env : LeEnv) -> Value raise {
  le__case_expand(form, 0)
}

///|
fn le__m_ecase(form : Value, _env : LeEnv) -> Value raise {
  le__case_expand(form, 1)
}

///|
fn le__typecase_expand(form : Value, err : Bool) -> Value {
  let g = le__gensym("key")
  let clauses = list_to_array(cddr(form))
  let mut r : Value = if err {
    list3(sym("error"), Str("~S fell through ETYPECASE expression."), g)
  } else {
    Nil
  }
  for k = clauses.length() - 1; k >= 0; k = k - 1 {
    let cl = clauses[k]
    let ty = car(cl)
    let body = if cdr(cl) is Nil { Value::Nil } else { le__progn(cdr(cl)) }
    if (eq(ty, t) || eq(ty, sym("otherwise"))) && k == clauses.length() - 1 {
      r = body
    } else {
      r = list4(sym("if"), list3(sym("typep"), g, le__quote(ty)), body, r)
    }
  }
  list3(sym("let"), list1(list2(g, cadr(form))), r)
}

///|
fn le__m_typecase(form : Value, _env : LeEnv) -> Value raise {
  le__typecase_expand(form, false)
}

///|
fn le__m_etypecase(form : Value, _env : LeEnv) -> Value raise {
  le__typecase_expand(form, true)
}

///|
/// DO / DO*: (block nil (let (vars) (tagbody top (if end (return ...))
/// body (psetq steps) (go top))))
fn le__do_expand(form : Value, star : Bool) -> Value {
  let specs = cadr(form)
  let end_clause = caddr(form)
  let (decls, body) = le__split_decls(cdddr(form))
  let bindings = Collector::new()
  let steps = Collector::new()
  for s in specs.iter() {
    match s {
      Cons({ car: v, cdr: rest }) => {
        bindings.add(list2(v, car(rest)))
        if cdr(rest) is Cons(_) {
          steps.add(v)
          steps.add(cadr(rest))
        }
      }
      _ => bindings.add(s)
    }
  }
  let top = le__gensym("top")
  let step_form = if steps.result() is Nil {
    Value::Nil
  } else {
    cons(sym(if star { "setq" } else { "psetq" }), steps.result())
  }
  let tb = Collector::new()
  tb.add(top)
  tb.add(
    list3(
      sym("if"),
      car(end_clause),
      list3(sym("return-from"), Nil, le__progn_or_nil(cdr(end_clause))),
    ),
  )
  tb.append_list(body)
  if !(step_form is Nil) {
    tb.add(step_form)
  }
  tb.add(list2(sym("go"), top))
  list3(
    sym("block"),
    Nil,
    list_star([
      sym(if star { "let*" } else { "let" }),
      bindings.result(),
      append(decls, list1(cons(sym("tagbody"), tb.result()))),
    ]),
  )
}

///|
fn le__progn_or_nil(body : Value) -> Value {
  if body is Nil {
    Nil
  } else {
    le__progn(body)
  }
}

///|
/// Leading declarations of a body, and the rest.
fn le__split_decls(body : Value) -> (Value, Value) {
  let d = Collector::new()
  let mut b = body
  while b is Cons({ car: Cons({ car: Sym({ name: "declare", .. }), .. }) as x, cdr: rest }) {
    d.add(x)
    b = rest
  }
  (d.result(), b)
}

///|
fn le__m_do(form : Value, _env : LeEnv) -> Value raise {
  le__do_expand(form, false)
}

///|
fn le__m_do_star(form : Value, _env : LeEnv) -> Value raise {
  le__do_expand(form, true)
}

///|
fn le__m_dolist(form : Value, _env : LeEnv) -> Value raise {
  let spec = cadr(form)
  let v = car(spec)
  let lst = cadr(spec)
  let result = caddr(spec)
  let (decls, body) = le__split_decls(cddr(form))
  let g = le__gensym("list")
  let top = le__gensym("top")
  // (block nil (let ((g lst) (v nil)) decls (tagbody top (if (endp g) (return-from nil (let ((v nil)) result))) (setq v (car g)) body (setq g (cdr g)) (go top))))
  let tb = Collector::new()
  tb.add(top)
  tb.add(
    list3(
      sym("if"),
      list2(sym("atom"), g),
      list3(
        sym("return-from"),
        Nil,
        if result is Nil {
          Nil
        } else {
          list3(sym("let"), list1(list2(v, Nil)), result)
        },
      ),
    ),
  )
  tb.add(list3(sym("setq"), v, list2(sym("car"), g)))
  tb.append_list(body)
  tb.add(list3(sym("setq"), g, list2(sym("cdr"), g)))
  tb.add(list2(sym("go"), top))
  list3(
    sym("block"),
    Nil,
    list_star([
      sym("let"),
      list2(list2(g, lst), list2(v, Nil)),
      append(decls, list1(cons(sym("tagbody"), tb.result()))),
    ]),
  )
}

///|
fn le__m_dotimes(form : Value, _env : LeEnv) -> Value raise {
  let spec = cadr(form)
  let v = car(spec)
  let count = cadr(spec)
  let result = caddr(spec)
  let (decls, body) = le__split_decls(cddr(form))
  let g = le__gensym("count")
  let top = le__gensym("top")
  let tb = Collector::new()
  tb.add(top)
  tb.add(
    list3(
      sym("if"),
      list3(sym(">="), v, g),
      list3(sym("return-from"), Nil, result),
    ),
  )
  tb.append_list(body)
  tb.add(list3(sym("setq"), v, list2(sym("1+"), v)))
  tb.add(list2(sym("go"), top))
  list3(
    sym("block"),
    Nil,
    list_star([
      sym("let*"),
      list2(list2(g, count), list2(v, Fix(0L))),
      append(decls, list1(cons(sym("tagbody"), tb.result()))),
    ]),
  )
}

///|
fn le__prog_expand(form : Value, star : Bool) -> Value {
  let (decls, body) = le__split_decls(cddr(form))
  list3(
    sym("block"),
    Nil,
    list_star([
      sym(if star { "let*" } else { "let" }),
      cadr(form),
      append(decls, list1(cons(sym("tagbody"), body))),
    ]),
  )
}

///|
fn le__m_prog(form : Value, _env : LeEnv) -> Value raise {
  le__prog_expand(form, false)
}

///|
fn le__m_prog_star(form : Value, _env : LeEnv) -> Value raise {
  le__prog_expand(form, true)
}

///|
fn le__m_prog1(form : Value, _env : LeEnv) -> Value raise {
  let g = le__gensym("prog1")
  list_star([
    sym("let"),
    list1(list2(g, cadr(form))),
    append(cddr(form), list1(g)),
  ])
}

///|
fn le__m_prog2(form : Value, _env : LeEnv) -> Value raise {
  list3(sym("progn"), cadr(form), cons(sym("prog1"), cddr(form)))
}

///|
fn le__m_return(form : Value, _env : LeEnv) -> Value raise {
  list3(sym("return-from"), Nil, cadr(form))
}

///|
fn le__m_psetq(form : Value, _env : LeEnv) -> Value raise {
  // (psetq a x b y) => (let ((g1 x) (g2 y)) (setf a g1) (setf b g2) nil)
  let binds = Collector::new()
  let sets = Collector::new()
  let mut l = cdr(form)
  while l is Cons({ car: place, cdr: Cons({ car: val, cdr: rest }) }) {
    let g = le__gensym("new")
    binds.add(list2(g, val))
    sets.add(list3(sym("setf"), place, g))
    l = rest
  }
  sets.add(Nil)
  list_star([sym("let"), binds.result(), sets.result()])
}

///|
fn le__m_mv_list(form : Value, _env : LeEnv) -> Value raise {
  list3(
    sym("multiple-value-call"),
    list2(sym("function"), sym("list")),
    cadr(form),
  )
}

///|
fn le__m_mv_setq(form : Value, _env : LeEnv) -> Value raise {
  let vars = list_to_array(cadr(form))
  let gs = vars.map(_ => le__gensym("v"))
  let sets = Collector::new()
  for i, v in vars {
    sets.add(list3(sym("setq"), v, gs[i]))
  }
  let first = if gs.length() > 0 { gs[0] } else { Nil }
  if gs.length() == 0 {
    return list2(sym("values"), caddr(form))
  }
  list_star([
    sym("multiple-value-bind"),
    list(gs),
    caddr(form),
    append(sets.result(), list1(first)),
  ])
}

///|
fn le__m_nth_value(form : Value, _env : LeEnv) -> Value raise {
  list3(sym("nth"), cadr(form), list2(sym("multiple-value-list"), caddr(form)))
}

///|
fn le__m_defvar(form : Value, _env : LeEnv) -> Value raise {
  let v = cadr(form)
  le__proclaim_special(v)
  let r = Collector::new()
  r.add(sym("progn"))
  r.add(list2(sym("si::proclaim-special"), le__quote(v)))
  if cddr(form) is Cons(_) {
    r.add(
      list3(
        sym("unless"),
        list2(sym("boundp"), le__quote(v)),
        list3(sym("set"), le__quote(v), caddr(form)),
      ),
    )
  }
  r.add(le__quote(v))
  r.result()
}

///|
fn le__m_defparameter(form : Value, _env : LeEnv) -> Value raise {
  let v = cadr(form)
  le__proclaim_special(v)
  list4(
    sym("progn"),
    list2(sym("si::proclaim-special"), le__quote(v)),
    list3(sym("set"), le__quote(v), caddr(form)),
    le__quote(v),
  )
}

///|
fn le__m_defconstant(form : Value, _env : LeEnv) -> Value raise {
  let v = cadr(form)
  list4(
    sym("progn"),
    list3(
      sym("unless"),
      list2(sym("boundp"), le__quote(v)),
      list3(sym("set"), le__quote(v), caddr(form)),
    ),
    list2(sym("si::proclaim-special"), le__quote(v)),
    le__quote(v),
  )
}

///|
fn le__m_ignore_quoted_name(form : Value, _env : LeEnv) -> Value raise {
  le__quote(cadr(form))
}

///|
fn le__m_ignore(_form : Value, _env : LeEnv) -> Value raise {
  Nil
}

///|
fn le__m_unsupported(form : Value, _env : LeEnv) -> Value raise {
  le__error(
    prin1_to_string(car(form)) + " is not supported by this port's Lisp evaluator",
  )
}

///|
fn le__m_progn_body(form : Value, _env : LeEnv) -> Value raise {
  cons(sym("progn"), cdr(form))
}

///|
fn le__m_with_compilation_unit(form : Value, _env : LeEnv) -> Value raise {
  cons(sym("progn"), cddr(form))
}

///|
fn le__m_declaim(form : Value, _env : LeEnv) -> Value raise {
  let r = Collector::new()
  r.add(sym("progn"))
  for spec in cdr(form).iter() {
    // proclaim specials right away (compile-time effect)
    le__proclaim(spec)
    r.add(list2(sym("proclaim"), le__quote(spec)))
  }
  r.result()
}

///|
fn le__proclaim(spec : Value) -> Unit {
  if car(spec) is Sym({ name: "special", .. }) {
    for v in cdr(spec).iter() {
      le__proclaim_special(v)
    }
  }
}

///|
fn le__m_in_package(form : Value, _env : LeEnv) -> Value raise {
  list2(sym("si::in-package"), le__quote(cadr(form)))
}

///|
fn le__m_check_type(form : Value, _env : LeEnv) -> Value raise {
  let place = cadr(form)
  let ty = caddr(form)
  list3(
    sym("unless"),
    list3(sym("typep"), place, le__quote(ty)),
    list([
      sym("error"),
      Str("The value of ~S is ~S, which is not of type ~S."),
      le__quote(place),
      place,
      le__quote(ty),
    ]),
  )
}

///|
fn le__m_assert(form : Value, _env : LeEnv) -> Value raise {
  list3(
    sym("unless"),
    cadr(form),
    if cdddr(form) is Cons(_) {
      cons(sym("error"), cdddr(form))
    } else {
      list3(
        sym("error"),
        Str("The assertion ~S failed."),
        le__quote(cadr(form)),
      )
    },
  )
}

///|
fn le__m_with_output_to_string(form : Value, _env : LeEnv) -> Value raise {
  // (with-output-to-string (var [string]) body) =>
  // (let ((var (make-string-output-stream))) body (get-output-stream-string var))
  let spec = cadr(form)
  let v = car(spec)
  let (decls, body) = le__split_decls(cddr(form))
  if cdr(spec) is Cons({ car: target, .. }) && !(target is Nil) {
    // output appended to a string with a fill pointer
    return list_star([
      sym("let"),
      list1(list2(v, list1(sym("make-string-output-stream")))),
      append(
        decls,
        list1(
          list3(
            sym("multiple-value-prog1"),
            le__progn_or_nil(body),
            list3(
              sym("si::string-append-fill"),
              target,
              list2(sym("get-output-stream-string"), v),
            ),
          ),
        ),
      ),
    ])
  }
  list_star([
    sym("let"),
    list1(list2(v, list1(sym("make-string-output-stream")))),
    append(
      decls,
      append(body, list1(list2(sym("get-output-stream-string"), v))),
    ),
  ])
}

///|
fn le__m_with_input_from_string(form : Value, _env : LeEnv) -> Value raise {
  let spec = cadr(form)
  let v = car(spec)
  let s = cadr(spec)
  let start = getf(cddr(spec), sym(":start"))
  let end_ = getf(cddr(spec), sym(":end"))
  let src = if start is Nil && end_ is Nil {
    s
  } else {
    list4(
      sym("subseq"),
      s,
      if start is Nil {
        Fix(0L)
      } else {
        start
      },
      end_,
    )
  }
  list_star([
    sym("let"),
    list1(list2(v, list2(sym("make-string-input-stream"), src))),
    cddr(form),
  ])
}

///|
fn le__m_with_open_file(form : Value, _env : LeEnv) -> Value raise {
  let spec = cadr(form)
  let v = car(spec)
  let (decls, body) = le__split_decls(cddr(form))
  list_star([
    sym("let"),
    list1(list2(v, cons(sym("open"), cdr(spec)))),
    append(
      decls,
      list1(
        list3(
          sym("unwind-protect"),
          le__progn_or_nil(body),
          list3(sym("when"), v, list2(sym("close"), v)),
        ),
      ),
    ),
  ])
}

///|
fn le__m_with_open_stream(form : Value, _env : LeEnv) -> Value raise {
  let spec = cadr(form)
  let v = car(spec)
  let (decls, body) = le__split_decls(cddr(form))
  list_star([
    sym("let"),
    list1(list2(v, cadr(spec))),
    append(
      decls,
      list1(
        list3(
          sym("unwind-protect"),
          le__progn_or_nil(body),
          list3(sym("when"), v, list2(sym("close"), v)),
        ),
      ),
    ),
  ])
}

///|
fn le__m_ignore_errors(form : Value, _env : LeEnv) -> Value raise {
  list3(
    sym("handler-case"),
    le__progn(cdr(form)),
    list3(
      sym("error"),
      list1(sym("si::c")),
      list3(sym("values"), Nil, sym("si::c")),
    ),
  )
}

///|
/// (handler-case form (type (var) body...) ... [(:no-error (vars) body)])
/// => (si::handler-case-fn (lambda () form) '(types...) (list (lambda (c) ...)...))
fn le__m_handler_case(form : Value, _env : LeEnv) -> Value raise {
  let types = Collector::new()
  let handlers = Collector::new()
  let mut no_error : Value = Nil
  for cl in cddr(form).iter() {
    let ty = car(cl)
    let ll = cadr(cl)
    let body = cddr(cl)
    if ty is Sym({ name: ":no-error", .. }) {
      no_error = list_star([sym("lambda"), ll, body])
      continue
    }
    let var_ = if ll is Nil { le__gensym("c") } else { car(ll) }
    types.add(ty)
    handlers.add(
      list_star([
        sym("lambda"),
        list1(var_),
        list2(sym("declare"), list2(sym("ignorable"), var_)),
        body,
      ]),
    )
  }
  let thunk = list3(sym("lambda"), Nil, cadr(form))
  let call = list([
    sym("si::handler-case-fn"),
    thunk,
    le__quote(types.result()),
    cons(sym("list"), handlers.result()),
  ])
  if no_error is Nil {
    call
  } else {
    // :no-error receives the values of the form
    list3(
      sym("multiple-value-call"),
      no_error,
      list([
        sym("si::handler-case-fn"),
        list3(sym("lambda"), Nil, cadr(form)),
        le__quote(types.result()),
        cons(sym("list"), handlers.result()),
      ]),
    )
  }
}

///|
/// (handler-bind ((type handler)...) body): handlers run before unwinding
/// in CL; here they run when the error reaches the HANDLER-BIND form, and
/// the error is re-signalled if the handler returns.
fn le__m_handler_bind(form : Value, _env : LeEnv) -> Value raise {
  let types = Collector::new()
  let handlers = Collector::new()
  for b in cadr(form).iter() {
    types.add(car(b))
    handlers.add(cadr(b))
  }
  list4(
    sym("si::handler-bind-fn"),
    list_star([sym("lambda"), Nil, cddr(form)]),
    le__quote(types.result()),
    cons(sym("list"), handlers.result()),
  )
}

///|
fn le__m_restart_case(form : Value, _env : LeEnv) -> Value raise {
  cadr(form)
}

///|
fn le__m_with_simple_restart(form : Value, _env : LeEnv) -> Value raise {
  le__progn_or_nil(cddr(form))
}

///|
fn le__m_time(form : Value, _env : LeEnv) -> Value raise {
  cadr(form)
}

///|
fn le__m_loop_finish(_form : Value, _env : LeEnv) -> Value raise {
  list2(sym("go"), sym("si::loop-end"))
}

///|
fn le__m_do_symbols(form : Value, _env : LeEnv) -> Value raise {
  let spec = cadr(form)
  list_star([
    sym("dolist"),
    list3(car(spec), list1(sym("si::all-symbols")), caddr(spec)),
    cddr(form),
  ])
}

///|
fn le__m_define_modify_macro(form : Value, _env : LeEnv) -> Value raise {
  // (define-modify-macro name (args) fn) => a macro using SETF
  let name = cadr(form)
  let ll = caddr(form)
  let fn_ = cadddr(form)
  let place = le__gensym("place")
  let args = Collector::new()
  for a in ll.iter() {
    if !le__is_amp(a) {
      args.add(match a {
        Cons({ car: v, .. }) => v
        _ => a
      })
    }
  }
  // (defmacro name (place . ll) (list 'si::modify place 'fn args...))
  list4(
    sym("defmacro"),
    name,
    cons(place, ll),
    list_star([
      sym("list"),
      le__quote(sym("si::modify-place")),
      place,
      le__quote(fn_),
      args.result(),
    ]),
  )
}

///|
fn le__m_defgeneric(form : Value, _env : LeEnv) -> Value raise {
  // generic functions are dispatched on the methods recorded by DEFMETHOD
  list2(sym("si::ensure-generic"), le__quote(cadr(form)))
}

///|
fn le__m_defmethod(form : Value, _env : LeEnv) -> Value raise {
  // (defmethod name [qualifiers] (specialized-ll) body)
  let name = cadr(form)
  let mut rest = cddr(form)
  while !(car(rest) is (Nil | Cons(_))) {
    rest = cdr(rest)
  }
  let sll = car(rest)
  let body = cdr(rest)
  let ll = Collector::new()
  let specs = Collector::new()
  let mut req = true
  for p in sll.iter() {
    if le__is_amp(p) {
      req = false
    }
    match p {
      Cons({ car: v, cdr: Cons({ car: spec, .. }) }) if req => {
        ll.add(v)
        specs.add(spec)
      }
      _ => {
        ll.add(p)
        if req {
          specs.add(t)
        }
      }
    }
  }
  list4(
    sym("si::add-method"),
    le__quote(name),
    le__quote(specs.result()),
    list_star([sym("lambda"), ll.result(), body]),
  )
}

///|
fn le__m_print_unreadable_object(form : Value, _env : LeEnv) -> Value raise {
  // (print-unreadable-object (obj stream &key type identity) body)
  let spec = cadr(form)
  let st = cadr(spec)
  list4(
    sym("progn"),
    list3(sym("write-string"), Str("#<"), st),
    le__progn_or_nil(cddr(form)),
    list3(sym("write-string"), Str(">"), st),
  )
}

///|
fn le__m_define_symbol_macro(form : Value, _env : LeEnv) -> Value raise {
  le__error(
    "define-symbol-macro is not supported by this port's Lisp evaluator: " +
    prin1_to_string(cadr(form)),
  )
}

///|
fn le__m_define_condition(form : Value, _env : LeEnv) -> Value raise {
  // (define-condition name (parents) slots options)
  let name = cadr(form)
  let parents = caddr(form)
  let mut report : Value = Nil
  for opt in cdr(cdddr(form)).iter() {
    if car(opt) is Sym({ name: ":report", .. }) {
      report = cadr(opt)
    }
  }
  let slots = Collector::new()
  for sl in cadddr(form).iter() {
    let sname = match sl {
      Cons({ car: n, .. }) => n
      _ => sl
    }
    let initarg = match sl {
      Cons({ cdr: opts, .. }) => getf(opts, sym(":initarg"))
      _ => Nil
    }
    let readers = Collector::new()
    match sl {
      Cons({ cdr: opts, .. }) => {
        let mut o = opts
        while o is Cons({ car: k, cdr: Cons({ car: v, cdr: r }) }) {
          if k is Sym({ name: ":reader" | ":accessor", .. }) {
            readers.add(v)
          }
          o = r
        }
      }
      _ => ()
    }
    slots.add(list3(sname, initarg, readers.result()))
  }
  list([
    sym("si::define-condition"),
    le__quote(name),
    le__quote(parents),
    le__quote(slots.result()),
    match report {
      Str(_) => report
      Nil => Nil
      Sym(_) => list2(sym("function"), report)
      _ => list2(sym("function"), report)
    },
  ])
}
