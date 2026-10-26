// Port of src/merror.lisp: Macsyma error signalling.
//
// MERROR sets $ERROR and raises
//   LispError::Condition(intern("maxima-$error"), <message text>, $error)
// where the Lisp code signals the MAXIMA-$ERROR condition (or throws to
// MACSYMA-QUIT at top level). As in Maxima, the message itself is printed
// by MERROR (via $ERRORMSG, when $ERRORMSG is true) unless
// *MERROR-SIGNALS-$ERROR-P* is set.

///|
/// Set while MERROR is formatting the message text of a condition, so that an
/// error during that formatting does not recurse.
let merror__formatting : Ref[Bool] = Ref(false)

///|
fn d_error(l : Value) -> Value raise {
  let x = fstringc(l)
  merror(car(x), cdr(x))
}

///|
fn d_warning(l : Value) -> Value raise {
  mwarning(l)
}

///|
fn error_size(exp_ : Value) -> Value raise {
  // Call SPECREPCHECK on the argument in case it's a specrep, but inhibit
  // simplification, since we may be here because simplification code is
  // complaining.
  let e = with_special(q_d_simp, Nil, fn() raise { specrepcheck(exp_) })
  if atom(e) {
    return Fix(0L)
  }
  let size = symval(q_d_error_size)
  let mut l = cdr(e)
  let mut n : Value = Fix(1L)
  // no need to go any further (also saves us from circular structures)
  while !(atom(l) || num_gt(n, size)) {
    let nn = num_add(num_add(n, error_size(car(l))), Fix(1L))
    l = cdr(l)
    n = nn
  }
  n
}

///|
/// Plain-text rendering of an error message, for the condition raised by
/// MERROR. Uses 1-D display.
fn merror__message_text(sstring : Value, l : Value) -> String {
  let raw = fn() {
    match sstring {
      Str(s) => s
      Sym(s) => s.name
      _ => prin1_to_string(sstring)
    }
  }
  if merror__formatting.val {
    return raw()
  }
  merror__formatting.val = true
  defer {
    merror__formatting.val = false
  }
  let r = (fn() -> String raise {
    let v = with_special(q_d_display2d, Nil, fn() raise {
      aformat(Nil, sstring, l)
    })
    string_trim(" \n", lstring(v))
  })() catch {
    _ => raw()
  }
  r
}

///|
fn merror__condition(sstring : Value, l : Value, text? : Bool = true) -> Error {
  let msg = if text {
    merror__message_text(sstring, l)
  } else {
    match sstring {
      Str(s) => s
      _ => prin1_to_string(sstring)
    }
  }
  LispError::Condition(intern("maxima-$error"), msg, symval(q_d_error))
}

///|
fn merror(sstring : Value, l : Value) -> Value raise {
  match merror__merror_cell.val {
    Some(f) => f(sstring, l)
    None => merror__merror_base(sstring, l)
  }
}

///|
/// The function cell of MERROR. Share packages (share/contrib/noninteractive/noninteractive.lisp) redefine
/// it at load time, as CL Maxima does with DEFUN; callers in the port reach
/// the current definition through this cell (None: the standard one).
let merror__merror_cell : Ref[((Value, Value) -> Value raise)?] = Ref(None)

///|
fn merror__merror_base(sstring : Value, l : Value) -> Value raise {
  set(q_d_error, cons(list2(q_mlist, q_simp), cons(sstring, l))) |> ignore
  if symval(q_ear_merror_signals__dolerror_p).truthy() {
    raise merror__condition(sstring, l, text=false)
  } else if eq(symval(q_ear_mdebug), q_d_lisp) {
    // Would go immediately into the Lisp debugger.
    raise merror__condition(sstring, l)
  } else if symval(q_ear_mdebug).truthy() {
    // The Maxima debugger is not ported: report the error as under errcatch.
    if symval(q_d_errormsg).truthy() {
      d_errormsg() |> ignore
    }
    raise merror__condition(sstring, l)
  } else if symval(q_errcatch).truthy() {
    if symval(q_d_errormsg).truthy() {
      d_errormsg() |> ignore
    }
    raise merror__condition(sstring, l)
  } else {
    with_special(standard_output, symval(error_output), fn() raise {
      if symval(q_d_errormsg).truthy() {
        d_errormsg() |> ignore
      }
      fresh_line() |> ignore
      // ($backtrace 3): the debugger's backtrace is not ported.
      fresh_line() |> ignore
      write_string(" -- an error. To debug this try: debugmode(true);\n")
      finish_output()
    })
    if symval(q_ear_quit_on_error).truthy() {
      d_quit(exit_code=Fix(1L)) |> ignore
    }
    throw_tag(q_macsyma_quit, q_maxima_error)
  }
}

///|
fn mwarning(l : Value) -> Value raise {
  let parts = mapcar(x => d_sconcat(list1(x)), l)
  let sb = StringBuilder()
  sb.write_string("Warning: ")
  let mut first = true
  for p in parts.iter() {
    if !first {
      sb.write_char(' ')
    }
    first = false
    sb.write_string(princ_to_string(p))
  }
  sb.write_char('\n')
  write_string(sb.to_string(), stream=symval(error_output))
  Nil
}

///|
fn assign_symbols(var_ : Value, val : Value) -> Value raise {
  if !(d_listp(val).truthy() && every(x => symbolp(x), cdr(val))) {
    merror(
      Str("assignment: assignment to ~M must be a list of symbols; found: ~M"),
      list2(var_, val),
    )
  } else {
    Nil
  }
}

///|
fn process_error_argl(l : Value) -> Value raise {
  // This returns things so that we could set or bind.
  let mut error_symbols : Value = Nil
  let mut error_values : Value = Nil
  let mut new_argl : Value = Nil
  let mut symbol_number = 0
  for form in l.iter() {
    if num_gt(error_size(form), symval(q_d_error_size)) {
      symbol_number += 1
      let s = nthcdr(symbol_number, symval(q_d_error_syms))
      let sym_ = if s.truthy() {
        car(s)
      } else {
        let n = sym("$errexp" + symbol_number.to_string())
        tuchus(symval(q_d_error_syms), n) |> ignore
        n
      }
      error_symbols = cons(sym_, error_symbols)
      error_values = cons(form, error_values)
      new_argl = cons(sym_, new_argl)
    } else {
      new_argl = cons(form, new_argl)
    }
  }
  list3(nreverse(error_symbols), nreverse(error_values), nreverse(new_argl))
}

///|
/// errormsg() redisplays the maxima-error message while in a `maxima-error'
/// break.
fn d_errormsg() -> Value raise {
  // Don't optimize out call to PROCESS-ERROR-ARGL in case of multiple calls
  // to $ERRORMSG, because the user may have changed the values of the
  // special variables controlling its behavior.
  let err = symval(q_d_error)
  let the_jig = process_error_argl(cddr(err))
  let mut syms = car(the_jig)
  let mut vals = cadr(the_jig)
  while syms.truthy() && vals.truthy() {
    set(car(syms), car(vals)) |> ignore
    syms = cdr(syms)
    vals = cdr(vals)
  }
  fresh_line() |> ignore
  let r = errset(fn() raise {
    mformat(list_star([Nil, cadr(err), caddr(the_jig)]))
  })
  if r is None {
    mtell(
      list2(
        Str("~%** error while printing error message **~%~A~%"),
        cadr(err),
      ),
    )
    |> ignore
  }
  fresh_line() |> ignore
  q_d_done
}

///|
/// Throw to the nearest enclosing RAT-ERR tag (set by IGNORE-RAT-ERROR or
/// RAT-ERROR-TO-MERROR).
fn rat_error(error_args : Value) -> Value raise {
  throw_tag(q_rat_err, error_args)
}

///|
/// The user-error function is called on "strings" and expressions. Cons up a
/// format string so that $ERROR can be bound.
fn fstringc(l : Value) -> Value raise {
  let mut sl : Value = Nil
  let mut se : Value = Nil
  let mut l = l
  while l.truthy() {
    let s = car(l)
    l = cdr(l)
    let sb = match s {
      Str(str) => {
        let c = Collector::new()
        for ch in str {
          c.add(Char(ch))
          if ch == '~' {
            c.add(Char(ch))
          }
        }
        c.result()
      }
      _ => {
        se = cons(s, se)
        list2(Char('~'), Char('M'))
      }
    }
    sl = nconc(sl, nconc(sb, if l is Nil { Nil } else { list1(Char(' ')) }))
  }
  cons(maknam(sl), nreverse(se))
}

///|
fn init_merror() -> Unit raise {
  // (defmvar $error_syms ... :properties ((assign 'assign-symbols)))
  putprop(q_d_error_syms, q_assign_symbols, q_assign) |> ignore
}
