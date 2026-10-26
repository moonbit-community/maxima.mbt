// Port of src/defmfun-check.lisp: DEFMFUN / DEFUN-CHECKED / DEF-SIMPLIFIER
// support and the argument-count error helpers (WNA-ERR and friends).
//
// The definition macros themselves (defmfun, defun-checked-form,
// def-simplifier, collect) are expanded by tools/gen.py into
// gen_registry.mbt; what remains here are the run-time helpers they call
// and the (compile-time) lambda-list utilities borrowed from CMUCL.

///|
let defmfun_check__q_amp_optional : Value = sym("&optional")

///|
let defmfun_check__q_amp_rest : Value = sym("&rest")

///|
let defmfun_check__q_amp_key : Value = sym("&key")

///|
let defmfun_check__q_amp_allow_other_keys : Value = sym("&allow-other-keys")

///|
let defmfun_check__q_amp_aux : Value = sym("&aux")

///|
/// CL `lambda-list-keywords` (SBCL order).
let defmfun_check__lambda_list_keywords : Array[String] = [
  "&allow-other-keys", "&aux", "&body", "&environment", "&key", "&optional", "&rest",
  "&whole",
]

// ---------------------------------------------------------------------------
// The Collect macro helpers (borrowed from cmucl src/code/extensions.lisp).

///|
/// Collect-Normal-Expander: the macroexpansion for normal collection
/// macros.  N-VALUE names the variable holding the current value, FUN the
/// collecting function and FORMS the forms whose values are collected.
fn collect_normal_expander(
  n__value : Value,
  fun : Value,
  forms : Value,
) -> Value raise {
  let body = mapcar(
    form => list([q_setq, n__value, list([fun, form, n__value])]),
    forms,
  )
  cons(q_progn, append(body, list1(n__value)))
}

///|
/// Collect-List-Expander: the list collection case.  N-TAIL is the
/// pointer to the current tail of the list, NIL if the list is empty.
fn collect_list_expander(
  n__value : Value,
  n__tail : Value,
  forms : Value,
) -> Value raise {
  let n_res = gensym()
  let body = mapcar(
    form => {
      list([
        q_let,
        list1(list([n_res, list([q_cons, form, Nil])])),
        list([
          q_cond,
          list([
            n__tail,
            list([q_setf, list([q_cdr, n__tail]), n_res]),
            list([q_setq, n__tail, n_res]),
          ]),
          list([t, list([q_setq, n__tail, n_res, n__value, n_res])]),
        ]),
      ])
    },
    forms,
  )
  cons(q_progn, append(body, list1(n__value)))
}

///|
fn defmfun_check__is_lambda_list_keyword(arg : Value) -> Bool {
  match arg {
    Sym(s) => defmfun_check__lambda_list_keywords.contains(s.name)
    _ => false
  }
}

///|
/// Parse-Lambda-List: break a lambda-list into its component parts.  The
/// primary value is the list of required args; see
/// `parse_lambda_list_mv` for all eight values.
fn parse_lambda_list(list_ : Value) -> Value raise {
  parse_lambda_list_mv(list_).0
}

///|
/// All eight values of PARSE-LAMBDA-LIST:
///  1] A list of the required args.
///  2] A list of the optional arg specs.
///  3] True if a rest arg was specified.
///  4] The rest arg.
///  5] A boolean indicating whether keywords args are present.
///  6] A list of the keyword arg specs.
///  7] True if &allow-other-keys was specified.
///  8] A list of the &aux specifiers.
fn parse_lambda_list_mv(
  list_ : Value,
) -> (Value, Value, Value, Value, Value, Value, Value, Value) raise {
  let required = Collector::new()
  let optional = Collector::new()
  let keys = Collector::new()
  let aux = Collector::new()
  let mut restp : Value = Nil
  let mut rest_ : Value = Nil
  let mut keyp : Value = Nil
  let mut allowp : Value = Nil
  // states: "required" "&optional" "&rest" "post-rest" "&key"
  // "&allow-other-keys" "&aux"
  let mut state = "required"
  for arg in list_.iter() {
    // check for arguments that have the syntactic form of a keyword
    // argument without being a recognized lambda-list keyword
    match arg {
      Sym(s) if s.name.length() != 0 && s.name.has_prefix("&") =>
        if !defmfun_check__is_lambda_list_keyword(arg) {
          format(
            error_output,
            "~&WARNING: ~S uses lambda-list keyword naming convention, but is not a recognized lambda-list keyword.~%",
            [arg],
          )
          |> ignore
        }
      _ => ()
    }
    if defmfun_check__is_lambda_list_keyword(arg) {
      if eq(arg, defmfun_check__q_amp_optional) {
        if state != "required" {
          raise LispError::SimpleError(
            format_to_string("Misplaced &optional in lambda-list: ~S.", [list_]),
          )
        }
        state = "&optional"
      } else if eq(arg, defmfun_check__q_amp_rest) {
        if !(state == "required" || state == "&optional") {
          raise LispError::SimpleError(
            format_to_string("Misplaced &rest in lambda-list: ~S.", [list_]),
          )
        }
        state = "&rest"
      } else if eq(arg, defmfun_check__q_amp_key) {
        if !(state == "required" || state == "&optional" || state == "post-rest") {
          raise LispError::SimpleError(
            format_to_string("Misplaced &key in lambda-list: ~S.", [list_]),
          )
        }
        keyp = t
        state = "&key"
      } else if eq(arg, defmfun_check__q_amp_allow_other_keys) {
        if state != "&key" {
          raise LispError::SimpleError(
            format_to_string(
              "Misplaced &allow-other-keys in lambda-list: ~S.",
              [list_],
            ),
          )
        }
        allowp = t
        state = "&allow-other-keys"
      } else if eq(arg, defmfun_check__q_amp_aux) {
        if state == "&rest" {
          raise LispError::SimpleError(
            format_to_string("Misplaced &aux in lambda-list: ~S.", [list_]),
          )
        }
        state = "&aux"
      } else {
        // ECASE fall-through
        raise LispError::SimpleError(
          format_to_string(
            "~S fell through ECASE expression. Wanted one of (&OPTIONAL &REST &KEY &ALLOW-OTHER-KEYS &AUX).",
            [arg],
          ),
        )
      }
    } else {
      match state {
        "required" => required.add(arg)
        "&optional" => optional.add(arg)
        "&rest" => {
          restp = t
          rest_ = arg
          state = "post-rest"
        }
        "&key" => keys.add(arg)
        "&aux" => aux.add(arg)
        _ =>
          raise LispError::SimpleError(
            format_to_string(
              "Found garbage in lambda-list when expecting a keyword: ~S.",
              [arg],
            ),
          )
      }
    }
  }
  if state == "&rest" {
    raise LispError::SimpleError("&rest not followed by required variable.")
  }
  (
    required.result(),
    optional.result(),
    restp,
    rest_,
    keyp,
    keys.result(),
    allowp,
    aux.result(),
  )
}

///|
/// Parse the declarations and doc-string out of the body of a defun-like
/// form.  Returns the tail of BODY after the declarations and doc strings,
/// a list of declare forms, and the doc-string (or NIL).
fn parse_body(
  body : Value,
  environment : Value,
  doc_string_allowed~ : Value = t,
) -> (Value, Value, Value) raise {
  ignore(environment)
  let mut doc_allowed = doc_string_allowed.truthy()
  let mut decls : Value = Nil
  let mut doc : Value = Nil
  let mut tail = body
  while !(tail is Nil) {
    let form = car(tail)
    if stringp(form) && cdr(tail).truthy() {
      if doc_allowed {
        doc = form
        // Only one doc string is allowed.
        doc_allowed = false
      } else {
        return (tail, nreverse(decls), doc)
      }
    } else if !(consp(form) && symbolp(car(form))) {
      return (tail, nreverse(decls), doc)
    } else if eq(car(form), q_declare) {
      decls = cons(form, decls)
    } else {
      return (tail, nreverse(decls), doc)
    }
    tail = cdr(tail)
  }
  (tail, nreverse(decls), doc)
}

///|
/// Convert Maxima keyword options `(((mequal) $opt1 val1) ...)` into a
/// Lisp keyword list `(:opt1 val1 ...)`, checking them against
/// VALID-KEYWORDS (verb forms).
fn defmfun_keywords(
  fname : Value,
  options : Value,
  valid_keywords : Value,
) -> Value raise {
  if !listp(options) {
    merr("Invalid Maxima keyword options: ~M", [options]) |> ignore
  }
  let all_ok = every(
    o => {
      // Make sure every option has the right form.
      let ok = listp(o) && length(o) == 3 && eq(caar(o), q_mequal)
      if !ok {
        merr("~M: Badly formed keyword option: ~M", [fname, o]) |> ignore
      }
      ok
    },
    options,
  )
  if !all_ok {
    return Nil
  }
  mapcan(
    o => {
      let opt = cadr(o)
      let val = caddr(o)
      // The valid keywords are always verb forms ($foo), so we need to
      // convert OPT to a verb form to be able to match the keywords.
      if valid_keywords is Nil ||
        member(d_verbify(opt), valid_keywords).truthy() {
        let v = d_verbify(opt)
        let name = symbol_name(v)
        list2(kw(name.substring(start=1)), val)
      } else {
        merr("~M: Unrecognized keyword: ~M", [fname, opt])
      }
    },
    options,
  )
}

///|
/// `(defmfun-arity-error control fname expected nargs &rest args)`
fn defmfun_arity_error(
  control : Value,
  fname : Value,
  expected : Value,
  nargs : Value,
  args : Value,
) -> Value raise {
  merror(control, list([fname, expected, nargs, cons(list1(q_mlist), args)]))
}

///|
/// Helper function to check the number of subscripts and arguments to a
/// subscripted function.
fn sub_arg_count_check(
  required_sub_count : Value,
  required_arg_count : Value,
  expr : Value,
  pretty_name : Value,
) -> Value raise {
  let subs = subfunsubs(expr)
  let args = subfunargs(expr)
  let sub_count = length(subs)
  let arg_count = length(args)
  let subs_ok = num_eq(int(sub_count), required_sub_count)
  let args_ok = num_eq(int(arg_count), required_arg_count)
  if subs_ok && args_ok {
    // Handle the expected case first (fastest).
    t
  } else if !subs_ok && !args_ok {
    merr(
      "~M:~%    expected exactly ~M subscripts but got ~M: ~M;~%    expected exactly ~M arguments but got ~M: ~M",
      [
        pretty_name,
        required_sub_count,
        int(sub_count),
        cons(list1(q_mlist), subs),
        required_arg_count,
        int(arg_count),
        cons(list1(q_mlist), args),
      ],
    )
  } else if !subs_ok {
    merr("~M: expected exactly ~M subscripts but got ~M: ~M", [
      pretty_name,
      required_sub_count,
      int(sub_count),
      cons(list1(q_mlist), subs),
    ])
  } else {
    merr("~M: expected exactly ~M arguments but got ~M: ~M", [
      pretty_name,
      required_arg_count,
      int(arg_count),
      cons(list1(q_mlist), args),
    ])
  }
}

///|
/// WNA-ERR: Wrong Number of Arguments error.
///
/// If REQUIRED-ARG-COUNT is non-NIL, then we check that EXPR has the
/// correct number of arguments.  An informative error message is shown if
/// the number of arguments is not given.
///
/// Otherwise, EXPR must be a symbol and a generic message is printed.
fn wna_err(
  exprs : Value,
  required_arg_count~ : Value = Nil,
  pretty_name~ : Value = Nil,
) -> Value raise {
  if required_arg_count.truthy() {
    let op = if pretty_name.truthy() { pretty_name } else { caar(exprs) }
    let actual_count = length(cdr(exprs))
    merr("~M: expected exactly ~M arguments but got ~M: ~M", [
      op,
      required_arg_count,
      int(actual_count),
      cons(list1(q_mlist), cdr(exprs)),
    ])
  } else {
    merr("~:@M: wrong number of arguments.", [exprs])
  }
}

///|
fn improper_arg_err(exp_ : Value, fn_ : Value) -> Value raise {
  merr("~:M: improper argument: ~M", [fn_, exp_])
}

// These check for the correct number of operands within Macsyma
// expressions, not arguments in a procedure call as the name may imply.

///|
fn arg_count_check(
  required_arg_count : Value,
  expr : Value,
  pretty_name? : Value,
) -> Value raise {
  let pretty_name = match pretty_name {
    Some(p) => p
    None => caar(expr)
  }
  if !num_eq(required_arg_count, int(length(cdr(expr)))) {
    wna_err(expr, required_arg_count~, pretty_name~)
  } else {
    Nil
  }
}

///|
fn oneargcheck(expr : Value) -> Value raise {
  arg_count_check(Fix(1L), expr)
}

///|
fn twoargcheck(expr : Value) -> Value raise {
  arg_count_check(Fix(2L), expr)
}
