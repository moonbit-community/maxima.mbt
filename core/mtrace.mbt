// Port of src/mtrace.lisp: trace/untrace/timer for Maxima functions.
//
// Trace works by storing away the real definition of a function and
// replacing it by a 'shadow' function. The shadow function prints a
// message, calls the real function, and then prints a message as it
// leaves.
//
//   Maxima function   shadow type   hook type   mget
//   expr              expr          expr
//   mexpr             expr          expr        t
//   mfexpr*           mfexpr*       expr
//
// In the port, an "expr" is a symbol's function cell (`Symbol.func`), so
// tracing replaces the function cell; calls made through the symbol
// (meval, funcall, apply) see the hook, direct MoonBit calls do not.
//
// Maxima offers no user-level mechanism for multiple return values; the
// port's functions return a single value, so only the primary value is
// propagated through traced or timed functions.

// ---- Structures (macros in the Lisp source)

///|
fn trace_p(x : Value) -> Value raise {
  mget(x, q_trace)
}

///|
fn trace_type(x : Value) -> Value raise {
  mget(x, q_trace_type)
}

///|
fn trace_level(x : Value) -> Value raise {
  mget(x, q_trace_level)
}

///|
fn trace_options(x : Value) -> Value raise {
  d_get(x, q_d_trace_options)
}

///|
fn trace_oldfun(x : Value) -> Value raise {
  mget(x, q_trace_oldfun)
}

///|
fn trace_hook(x : Value) -> Value raise {
  mget(x, q_trace_hook)
}

///|
/// `(setf (symbol-function s) f)` for a function value `f`.
fn mtrace__set_symbol_function(s : Value, f : Value) -> Unit raise {
  match (s, f) {
    (Sym(sy), Func(lf)) => sy.func = Some(lf)
    (Sym(_), Sym(_)) => mtrace__set_symbol_function(s, symbol_function(f))
    _ => raise LispError::SimpleError("(setf symbol-function): bad arguments")
  }
}

///|
/// `(or (get fun 'impl-name) fun)`
fn mtrace__impl_name(fun : Value) -> Value {
  let i = get(fun, q_impl_name)
  if i.truthy() {
    i
  } else {
    fun
  }
}

///|
/// `(and (fboundp fun) (symbol-function (or (get fun 'impl-name) fun)))`
fn mtrace__current_function(fun : Value) -> Value raise {
  if fboundp(fun) {
    symbol_function(mtrace__impl_name(fun))
  } else {
    Nil
  }
}

///|
/// Destructive `(delete item l :test #'eq)` (splices the conses of `l`).
fn mtrace__delete_eq(item : Value, l : Value) -> Value {
  let mut head = l
  while head.truthy() && eq(car(head), item) {
    head = cdr(head)
  }
  let mut prev = head
  while prev.truthy() {
    let next = cdr(prev)
    if next.truthy() && eq(car(next), item) {
      rplacd(prev, cdr(next)) |> ignore
    } else {
      prev = next
    }
  }
  head
}

// ---- User interface functions.

///|
/// totally random utility function
fn mlistcan__dolall(fun : Value, llist : Value, default : Value) -> Value raise {
  with_special(q_trace_allp, Nil, () => {
    if llist is Nil {
      default
    } else {
      let items = if eq(car(llist), q_d_all) || eq(car(llist), q_d_functions) {
        set(q_trace_allp, t) |> ignore
        mapcar(x => caar(x), cdr(symval(q_d_functions)))
      } else {
        llist
      }
      cons(list1(q_mlist), mapcan(x => funcall(fun, [x]), items))
    }
  })
}

///|
fn d_trace(form : Value) -> Value raise {
  mlistcan__dolall(q_macsyma_trace, cdr(form), symval(q_d_trace))
}

///|
fn d_trace_it(function : Value) -> Value raise {
  cons(list1(q_mlist), macsyma_trace(function))
}

///|
fn d_untrace(form : Value) -> Value raise {
  let funs = if cdr(form).truthy() { cdr(form) } else { cdr(symval(q_d_trace)) }
  cons(list1(q_mlist), mapcan(f => macsyma_untrace(f), funs))
}

///|
fn d_untrace_it(function : Value) -> Value raise {
  cons(list1(q_mlist), macsyma_untrace(function))
}

///|
fn d_trace_options(form : Value) -> Value raise {
  d_put(cadr(form), cons(list1(q_mlist), cddr(form)), q_d_trace_options)
}

// ---- System interface functions.

///|
fn macsyma_trace(fun : Value) -> Value raise {
  macsyma_trace_sub(fun, q_trace_handler, symval(q_d_trace))
}

///|
fn macsyma_trace_sub(fun : Value, handler : Value, ilist : Value) -> Value raise {
  let fun = getopr(fun)
  if !symbolp(fun) {
    mtell(
      list([
        Str(
          "trace: argument is apparently not a function or operator: ~M~%",
        ),
        fun,
      ]),
    )
    |> ignore
    return Nil
  }
  if trace_p(fun).truthy() && symval(q_trace_allp).truthy() {
    // If trace(all) is invoked, quietly skip already traced functions.
    return Nil
  }
  // If it's already traced, untrace it first before proceeding.
  if trace_p(fun).truthy() {
    mtell(
      list([
        Str("trace: function ~@:M is already traced; untracing it first.~%"),
        fun,
      ]),
    )
    |> ignore
    macsyma_untrace_sub(fun, handler, ilist) |> ignore
  }
  // Now proceed with standard tracing.
  if memq(fun, symval(q_hard_to_trace)).truthy() {
    mtell(list([Str("trace: ~@:M cannot be traced.~%"), fun])) |> ignore
    return Nil
  }
  let temp = car(macsyma_fsymeval(fun))
  if temp is Nil {
    mtell(list([Str("trace: ~@:M has no functional properties.~%"), fun]))
    |> ignore
    Nil
  } else if eq(temp, q_mmacro) || eq(temp, q_translated_mmacro) {
    mtell(
      list([
        Str(
          "trace: ~@:M is a macro, so it won't trace well; try 'macroexpand' to debug it.~%",
        ),
        fun,
      ]),
    )
    |> ignore
    Nil
  } else if get(temp, q_shadow).truthy() {
    put_trace_info(fun, temp, ilist) |> ignore
    trace_fshadow(fun, temp, make_trace_hook(fun, temp, handler)) |> ignore
    list1(getop(fun))
  } else {
    mtell(list([Str("trace: ~@:M is an unknown type of function.~%"), fun]))
    |> ignore
    Nil
  }
}

///|
fn macsyma_untrace(fun : Value) -> Value raise {
  macsyma_untrace_sub(fun, q_trace_handler, symval(q_d_trace))
}

///|
fn macsyma_untrace_sub(
  fun : Value,
  handler : Value,
  ilist : Value,
) -> Value raise {
  let fun = getopr(fun)
  let result : Value = if !symbolp(fun) {
    mtell(
      list([
        Str(
          "untrace: argument is apparently not a function or operator: ~M~%",
        ),
        fun,
      ]),
    )
    |> ignore
    Nil
  } else if trace_p(fun) is Nil {
    mtell(list([Str("untrace: ~@:M is not traced.~%"), fun])) |> ignore
    Nil
  } else {
    trace_unfshadow(fun, trace_type(fun)) |> ignore
    rem_trace_info(fun, ilist) |> ignore
    list1(getop(fun))
  }
  if memq(fun, symval(q_trace_handling_stack)).truthy() {
    // yes, he has re-defined or untraced the function during the
    // trace-handling application. This is not strange, in fact it happens
    // all the time when the user is using the $ERRORCATCH option!
    macsyma_trace_sub(fun, handler, ilist) |> ignore
  }
  result
}

///|
fn put_trace_info(fun : Value, type_ : Value, ilist : Value) -> Value raise {
  mputprop(fun, fun, q_trace) |> ignore // needed for MEVAL at this time also.
  mputprop(fun, type_, q_trace_type) |> ignore
  mputprop(fun, mtrace__current_function(fun), q_trace_oldfun) |> ignore
  let sym_ = gensym()
  set(sym_, Fix(0L)) |> ignore
  mputprop(fun, sym_, q_trace_level) |> ignore
  rplacd(ilist, cons(getop(fun), cdr(ilist))) |> ignore
  list1(fun)
}

///|
fn rem_trace_info(fun : Value, ilist : Value) -> Value raise {
  mputprop(fun, Nil, q_trace) |> ignore
  if memq(fun, symval(q_trace_handling_stack)) is Nil {
    mputprop(fun, Nil, q_trace_level) |> ignore
  }
  mputprop(fun, Nil, q_trace_type) |> ignore
  mputprop(fun, Nil, q_trace_hook) |> ignore
  mtrace__delete_eq(getop(fun), ilist) |> ignore
  list1(fun)
}

///|
fn get_bang(x : Value, y : Value) -> Value raise {
  let v = get(x, y)
  if v.truthy() {
    v
  } else {
    maxima_error(
      Str("GET!: property ~a of symbol ~a undefined."),
      list2(y, x),
    )
  }
}

///|
fn trace_fshadow(fun : Value, type_ : Value, value : Value) -> Value raise {
  let shadow = get_bang(type_, q_shadow)
  mputprop(fun, value, q_trace_hook) |> ignore
  if eq(type_, q_mexpr) && mget(fun, q_mfexprp).truthy() {
    // We're tracing an mexpr with special evaluation rules (mfexpr). Put a
    // Maxima lambda expression on the plist that calls the trace hook; the
    // evaluator's mlambda then does the work for us.
    let lambda_list = cadr(mget(fun, q_mexpr))
    let params = mparams(lambda_list)
    let body = if mget(fun, q_mlexprp).truthy() {
      // This is the mfexpr+mlexpr case (we have at least one quoted arg
      // and a rest arg).
      let call_hook = lfunc("call-hook", args => {
        let restarg = arg(args, 0)
        let nonrestargs = rest_args(args, 1)
        apply(value, append(nonrestargs, cdr(restarg)))
      })
      cons(list1(q_funcall), cons(call_hook, cons(car(last(params)), butlast(params))))
    } else {
      cons(list1(q_funcall), cons(value, params))
    }
    putprop(fun, list3(list1(q_lambda), lambda_list, body), q_mfexpr)
  } else if eq(shadow, q_expr) || eq(shadow, q_subr) {
    mputprop(fun, mtrace__current_function(fun), q_trace_oldfun) |> ignore
    mtrace__set_symbol_function(mtrace__impl_name(fun), value)
    value
  } else {
    set_symbol_plist(fun, list_star([shadow, value, symbol_plist(fun)]))
  }
}

///|
fn trace_unfshadow(fun : Value, type_ : Value) -> Value raise {
  // At this point, we know that FUN is traced.
  if eq(type_, q_mexpr) && safe_get(fun, q_mfexpr).truthy() {
    remprop(fun, q_mfexpr)
  } else if eq(type_, q_expr) || eq(type_, q_subr) {
    let oldf = trace_oldfun(fun)
    let currentf = mtrace__current_function(fun)
    let hookf = trace_hook(fun)
    if eq(currentf, hookf) {
      // Function hasn't been redefined, safe to restore old definition.
      if oldf.truthy() {
        mtrace__set_symbol_function(mtrace__impl_name(fun), oldf)
        oldf
      } else {
        fmakunbound(fun)
      }
    } else {
      // Function has been redefined (e.g. by loading a Lisp file).
      // Don't restore the old definition.
      mtell(
        list([
          Str(
            "untrace: function ~@:M was redefined while traced; leaving new definition intact.~%",
          ),
          fun,
        ]),
      )
    }
  } else {
    remprop(fun, get_bang(type_, q_shadow)) |> ignore
    fmakunbound(fun)
  }
}

///|
/// Find the original function of FUN, which is being traced. The original
/// definition may be hidden on the property list behind the shadow
/// function.
fn trace_fsymeval(fun : Value) -> Value raise {
  let type_of = trace_type(fun)
  let v = if get(type_of, q_mget).truthy() {
    if eq(get_bang(type_of, q_shadow), type_of) {
      mget(cdr(mgetl(fun, list1(type_of))), type_of)
    } else {
      mget(fun, type_of)
    }
  } else if eq(get_bang(type_of, q_shadow), q_expr) {
    trace_oldfun(fun)
  } else if eq(get_bang(type_of, q_shadow), type_of) {
    cadr(getl(cdr(getl(fun, list1(type_of))), list1(type_of)))
  } else {
    get(fun, type_of)
  }
  if v.truthy() {
    v
  } else {
    trace_fsymeval(
      merr("internal error: trace property for ~:@M went away without hook.", [
        fun,
      ]),
    )
  }
}

// ---- The handling of a traced call.

///|
/// `(macsyma-errset form)`: the macro evaluates FORM under ERRSET with
/// ERRCATCH bound, undoing Maxima bindings on error. The function form of
/// the contract receives an already evaluated value, so it can only wrap
/// it; the trace handler uses `mtrace__macsyma_errset` with a thunk.
fn macsyma_errset(form : Value) -> Value raise {
  mtrace__macsyma_errset(() => form)
}

///|
fn mtrace__macsyma_errset(f : () -> Value raise) -> Value raise {
  let ec = cons(symval(q_bindlist), symval(q_loclist))
  with_special(q_errcatch, ec, () => {
    let ret = match errset(f) {
      Some(v) => list1(v)
      None => Nil
    }
    if ret is Nil {
      errlfun1(ec) |> ignore
    }
    ret
  })
}

///|
fn trace_slget_user_visible_args(
  fun : Value,
  iargs : Value,
) -> (Value, Value) raise {
  let ty = trace_type(fun)
  if eq(ty, q_mfexpr_star) || eq(ty, q_operators) {
    (margs(car(iargs)), cdr(iargs))
  } else {
    (iargs, Nil)
  }
}

///|
fn trace_slget_internal_args(
  fun : Value,
  uargs : Value,
  extras : Value,
) -> Value raise {
  let ty = trace_type(fun)
  if eq(ty, q_mfexpr_star) || eq(ty, q_operators) {
    cons(cons(list1(fun), uargs), extras)
  } else {
    uargs
  }
}

///|
fn trace_handler(fun : Value, largs : Value) -> (Value, Value) raise {
  if symval(q_return_to_trace_handle).truthy() ||
    (
      !atom(car(largs)) &&
      !atom(caar(largs)) &&
      eq(car(caar(largs)), q_d_untrace) &&
      eq(cadar(largs), fun)
    ) {
    // We were called by the trace-handler or by $untrace and the function
    // fun is to be untraced.
    let vals = mtrace__trace_apply_mvl(fun, largs)
    return (car(vals), cadr(vals))
  }
  let level_sym = trace_level(fun)
  with_specials(
    [
      (q_trace_indent_level, num_add(symval(q_trace_indent_level), Fix(1L))),
      (q_return_to_trace_handle, t),
      (q_trace_handling_stack, cons(fun, symval(q_trace_handling_stack))),
    ],
    () => {
      let level = num_add(symbol_value(level_sym), Fix(1L))
      with_specials([(level_sym, level), (q_predicate_arglist, Nil)], () => {
        let mut largs = largs
        while true {
          let (user_args0, extras) = trace_slget_user_visible_args(fun, largs)
          set(
            q_predicate_arglist,
            list([level, q_d_enter, fun, cons(list1(q_mlist), user_args0)]),
          )
          |> ignore
          let user_args = trace_enter_break(fun, level, user_args0)
          trace_enter_print(fun, level, user_args) |> ignore
          largs = trace_slget_internal_args(fun, user_args, extras)
          let mut continuation : Value = Nil
          let mut ret_vals : Value = Nil
          if trace_option_p(fun, q_d_errorcatch).truthy() {
            let fa = largs
            ret_vals = mtrace__macsyma_errset(() => trace_apply(fun, fa))
            if ret_vals is Nil {
              ret_vals = trace_error_break(fun, level, user_args)
              continuation = car(ret_vals)
              ret_vals = cdr(ret_vals)
            } else {
              continuation = q_exit
            }
          } else {
            continuation = q_exit
            ret_vals = mtrace__trace_apply_mvl(fun, largs)
          }
          if eq(continuation, q_exit) {
            set(q_predicate_arglist, list([level, q_d_exit, fun, car(ret_vals)]))
            |> ignore
            let rv = trace_exit_break(fun, level, ret_vals)
            trace_exit_print(fun, level, car(rv)) |> ignore
            return (car(rv), cadr(rv))
          } else if eq(continuation, q_retry) {
            largs = trace_slget_internal_args(fun, ret_vals, extras)
            mtell(
              list([Str("TRACE-HANDLER: reapplying the function ~:@M~%"), fun]),
            )
            |> ignore
          } else if eq(continuation, q_maxima_error) {
            merr(
              "~%TRACE-HANDLER: signaling 'maxima-error' for function ~:@M~%",
              [fun],
            )
            |> ignore
          }
        }
        (Nil, Nil)
      })
    },
  )
}

// The (Trace-options function) access is not optimized to take place only
// once per trace-handle call. This is so that the user may change options
// during his break loops.

///|
fn trace_option_p(function : Value, keyword : Value) -> Value raise {
  let options = trace_options(function)
  let opts : Value = if options is Nil {
    Nil
  } else if d_listp(options).truthy() {
    cdr(options)
  } else {
    mtell(
      list([
        Str(
          "TRACE-OPTION-P: trace options for ~:@M not a list, so ignored.~%",
        ),
        function,
      ]),
    )
    |> ignore
    Nil
  }
  for option in opts.iter() {
    if atom(option) {
      if eq(option, keyword) {
        return t
      }
    } else if eq(caar(option), keyword) {
      return with_special(
        q_return_to_trace_handle,
        symval(q_d_trace_safety),
        () => mapply(
          cadr(option),
          symval(q_predicate_arglist),
          Str("A trace option predicate"),
        ),
      )
    }
  }
  Nil
}

///|
fn trace_enter_print(fun : Value, lev : Value, largs : Value) -> Value raise {
  if trace_option_p(fun, q_d_noprint).truthy() {
    return Nil
  }
  let info = trace_option_p(fun, q_d_info)
  if trace_option_p(fun, q_d_lisp_print).truthy() {
    trace_print(append(list([lev, q_enter, fun, largs]), info))
  } else {
    trace_mprint(
      list([
        lev,
        Str(
          if eq(trace_type(fun), q_operators) {
            " Simp   "
          } else {
            " Call   "
          },
        ),
        mopstringnam(fun),
        Str(" "),
        cons(list1(q_mlist), largs),
        Str(if info.truthy() { " -> " } else { "" }),
        if info.truthy() {
          info
        } else {
          Str("")
        },
      ]),
    )
  }
}

///|
fn mopstringnam(x : Value) -> Value raise {
  maknam(mstring(getop(x)))
}

///|
fn trace_exit_print(fun : Value, lev : Value, ret_val : Value) -> Value raise {
  if trace_option_p(fun, q_d_noprint).truthy() {
    return Nil
  }
  let info = trace_option_p(fun, q_d_info)
  if trace_option_p(fun, q_d_lisp_print).truthy() {
    trace_print(append(list([lev, q_exit, fun, ret_val]), info))
  } else {
    trace_mprint(
      list([
        lev,
        Str(" Return "),
        mopstringnam(fun),
        Str(" "),
        ret_val,
        Str(if info.truthy() { " -> " } else { "" }),
        if info.truthy() {
          info
        } else {
          Str("")
        },
      ]),
    )
  }
}

///|
fn trace_enter_break(fun : Value, lev : Value, largs : Value) -> Value raise {
  if trace_option_p(fun, q_d_break).truthy() {
    with_specials(
      [
        (q_return_to_trace_handle, Nil),
        (q_d_trace_break_arg, cons(list1(q_mlist), largs)),
      ],
      () => {
        while true {
          d_break(list([Str("Trace entering"), fun, Str("level"), lev]))
          |> ignore
          if d_listp(symval(q_d_trace_break_arg)).truthy() {
            return cdr(symval(q_d_trace_break_arg))
          } else {
            mtell(
              list([
                Str("TRACE-ENTER-BREAK: 'trace_break_arg' must be a list.~%"),
              ]),
            )
            |> ignore
          }
        }
        Nil
      },
    )
  } else {
    largs
  }
}

///|
fn trace_exit_break(fun : Value, lev : Value, ret_vals : Value) -> Value raise {
  if trace_option_p(fun, q_d_break).truthy() {
    with_specials(
      [(q_d_trace_break_arg, car(ret_vals)), (q_return_to_trace_handle, Nil)],
      () => {
        d_break(list([Str("Trace exiting"), fun, Str("level"), lev])) |> ignore
        // If trace_break_arg is the same (in the sense of eq) now as when we
        // started the breakpoint, then return all of the original return
        // values from the function.
        if eq(symval(q_d_trace_break_arg), car(ret_vals)) {
          ret_vals
        } else {
          list1(symval(q_d_trace_break_arg))
        }
      },
    )
  } else {
    ret_vals
  }
}

///|
fn pred__dolread(
  predicate : Value,
  argl : Value,
  bad_message : Value,
) -> Value raise {
  while true {
    let ans = d_read(argl)
    if funcall(predicate, [ans]).truthy() {
      return ans
    }
    mtell(list([Str("PRED-$READ: unacceptable input: ~A~%"), bad_message]))
    |> ignore
  }
  Nil
}

///|
fn ask_choicep(llist : Value, header_message : Value) -> Value raise {
  let mut j = 0
  let mut dlist : Value = Nil
  let mut ilist = llist
  while ilist.truthy() {
    dlist = list_star([
      Char('\n'),
      mk(q_marrow, [int(j), car(ilist)]),
      dlist,
    ])
    j += 1
    ilist = cdr(ilist)
  }
  let dlist = nconc(header_message, cons(Char('\n'), nreverse(dlist)))
  let upper = j - 1
  pred__dolread(
    lfunc("ask-choicep-pred", args => {
      let v = arg(args, 0)
      lbool(
        integerp(v) && num_ge(v, Fix(0L)) && num_le(v, int(upper)),
      )
    }),
    dlist,
    Str("please reply with an integer from the menu."),
  )
}

///|
fn trace_error_break(fun : Value, level : Value, largs : Value) -> Value raise {
  let choice = ask_choicep(
    list([
      Str("Signal an `maxima-error', i.e. punt?"),
      Str("Retry with same arguments?"),
      Str("Retry with new arguments?"),
      Str("Exit with user supplied value"),
    ]),
    list([
      Str("Error during application of"),
      mopstringnam(fun),
      Str("at level"),
      level,
      Char('\n'),
      Str("Do you want to:"),
    ]),
  )
  if eql(choice, Fix(0L)) {
    list1(q_maxima_error)
  } else if eql(choice, Fix(1L)) {
    cons(q_retry, largs)
  } else if eql(choice, Fix(2L)) {
    cons(
      q_retry,
      with_special(q_d_trace_break_arg, cons(list1(q_mlist), largs), () => cdr(
        pred__dolread(
          q_d_listp,
          list2(Str("Enter new argument list for"), mopstringnam(fun)),
          Str("please enter a list."),
        ),
      )),
    )
  } else if eql(choice, Fix(3L)) {
    cons(q_exit, list1(d_read(list1(Str("Enter value to return")))))
  } else {
    Nil
  }
}

// ---- application dispatch, and the consing up of the trace hook.

///|
fn macsyma_fsymeval(fun : Value) -> Value raise {
  let try_ = macsyma_fsymeval_sub(fun)
  if try_.truthy() {
    try_
  } else if get(fun, q_autoload).truthy() {
    d_load(get(fun, q_autoload)) |> ignore
    let try_ = macsyma_fsymeval_sub(fun)
    if try_ is Nil {
      mtell(
        list([
          Str(
            "trace: ~@:M has no functional properties after autoloading.~%",
          ),
          fun,
        ]),
      )
      |> ignore
    }
    try_
  } else {
    try_
  }
}

///|
fn macsyma_fsymeval_sub(fun : Value) -> Value raise {
  let mprops = mgetl(fun, list2(q_mexpr, q_mmacro))
  let lprops = getl(fun, list3(q_translated_mmacro, q_mfexpr_star, q_mfexpr_stars))
  let fcell_props = getl_lm_fcn_prop(fun, list4(q_subr, q_lsubr, q_expr, q_macro))
  let op_props = getl(fun, list1(q_operators))
  let order = if symval(q_d_transrun).truthy() {
    // the default
    [lprops, fcell_props, mprops, op_props]
  } else {
    [mprops, lprops, fcell_props, op_props]
  }
  for p in order {
    if p.truthy() {
      return p
    }
  }
  Nil
}

///|
/// Argument handling according to FUN's TYPE is already done elsewhere:
/// HANDLER, meval...
fn make_trace_hook(fun : Value, type_ : Value, handler : Value) -> Value raise {
  ignore(type_)
  // The hook returns all the values of the handler (rules return two
  // values, see matcom.mbt): the multiple-valued version is registered in
  // matcom__mv_fns under the hook's unique name.
  let call_mv = (trace_args : Array[Value]) => if eq(handler, q_trace_handler) {
    trace_handler(fun, list(trace_args))
  } else if eq(handler, q_timer_handler) {
    let vals = mtrace__timer_handler_mvl(fun, list(trace_args))
    (car(vals), cadr(vals))
  } else {
    (funcall(handler, [fun, list(trace_args)]), Nil)
  }
  matcom__fn_counter.val += 1
  let id = "trace-hook-" + matcom__fn_counter.val.to_string()
  matcom__mv_fns[id] = call_mv
  lfunc(id, trace_args => call_mv(trace_args).0)
}

///|
fn trace_apply(fun : Value, largs : Value) -> Value raise {
  car(mtrace__trace_apply_mvl(fun, largs))
}

///|
/// `(multiple-value-list (trace-apply fun largs))`
fn mtrace__trace_apply_mvl(fun : Value, largs : Value) -> Value raise {
  let prop = trace_fsymeval(fun)
  let type_ = trace_type(fun)
  with_special(q_return_to_trace_handle, Nil, () => {
    if eq(type_, q_mexpr) {
      list1(mapply(prop, largs, Str("A traced function")))
    } else if eq(type_, q_expr) ||
      eq(type_, q_subr) ||
      eq(type_, q_lsubr) ||
      eq(type_, q_operators) {
      let lf = match prop {
        Func(lf) => Some(lf)
        Sym({ func: Some(lf), .. }) => Some(lf)
        _ => None
      }
      match lf {
        Some(lf) =>
          match matcom__mv_fns.get(lf.name) {
            Some(g) => {
              let (a, b) = g(list_to_array(largs))
              return list2(a, b)
            }
            None => ()
          }
        None => ()
      }
      list1(apply(prop, largs))
    } else if eq(type_, q_mfexpr_star) || eq(type_, q_mfexpr_stars) {
      list1(funcall(prop, [car(largs)]))
    } else {
      list1(Nil)
    }
  })
}

// ---- I/O cruft

///|
fn mtrace__spaceout_dimension(form : Value, result : Value) -> Value raise {
  let n = to_int(cadr(form))
  let c = Collector::new()
  for _ in 0..<n {
    c.add(Char(' '))
  }
  dimension_string(c.result(), result)
}

///|
fn mtrace__indent() -> Value raise {
  num_min(symval(q_d_trace_max_indent), symval(q_trace_indent_level))
}

///|
fn trace_mprint(l : Value) -> Value raise {
  mtell_open(
    Str("~M"),
    list1(
      cons(list1(q_mtext), cons(mk(q_spaceout, [mtrace__indent()]), l)),
    ),
  )
}

///|
fn trace_print(form : Value) -> Value raise {
  let mut j = to_int(mtrace__indent())
  while j > 0 {
    write_char(' ')
    j -= 1
  }
  prin1(form) |> ignore
  terpri()
  finish_output()
  Nil
}

// 9:02pm  Monday, 18 May 1981 -GJC
// A function benchmark facility using trace utilities.

///|
fn d_timer(form : Value) -> Value raise {
  mlistcan__dolall(q_macsyma_timer, cdr(form), symval(q_d_timer))
}

///|
fn d_untimer(form : Value) -> Value raise {
  let funs = if cdr(form).truthy() { cdr(form) } else { cdr(symval(q_d_timer)) }
  cons(list1(q_mlist), mapcan(f => macsyma_untimer(f), funs))
}

///|
/// `internal-time-units-per-second` (microseconds, as in SBCL).
let mtrace__internal_time_units_per_second : Int64 = 1000000L

///|
/// `(get-internal-run-time)` in internal time units.
fn mtrace__get_internal_run_time() -> Value {
  int64((cpu_time() * mtrace__internal_time_units_per_second.to_double()).to_int64())
}

///|
fn micro_to_sec(runtime : Value) -> Value raise {
  mul3(
    runtime,
    Flo(1.0 / mtrace__internal_time_units_per_second.to_double()),
    q_d_sec,
  )
}

///|
fn micro_per_call_to_sec(runtime : Value, calls : Value) -> Value raise {
  div(micro_to_sec(runtime), if zerop(calls) { Fix(1L) } else { calls })
}

///|
fn timer_mlist(
  function : Value,
  calls : Value,
  runtime : Value,
  gctime : Value,
) -> Value raise {
  mk_simp(q_mlist, [
    function,
    micro_per_call_to_sec(num_add(runtime, gctime), calls),
    calls,
    micro_to_sec(runtime),
    micro_to_sec(gctime),
  ])
}

///|
fn d_timer_info(form : Value) -> Value raise {
  let l = if cdr(form).truthy() { cdr(form) } else { cdr(symval(q_d_timer)) }
  let mut v : Value = Nil
  let mut total_runtime : Value = Fix(0L)
  let mut total_gctime : Value = Fix(0L)
  let mut total_calls : Value = Fix(0L)
  for f in l.iter() {
    let fun_opr = getopr(f)
    let runtime = d_get(fun_opr, q_d_runtime)
    let gctime = d_get(fun_opr, q_d_gctime)
    let calls = d_get(fun_opr, q_d_calls)
    if runtime.truthy() {
      total_calls = num_add(total_calls, calls)
      total_runtime = num_add(total_runtime, runtime)
      total_gctime = num_add(total_gctime, gctime)
      v = cons(timer_mlist(f, calls, runtime, gctime), v)
    }
  }
  cons(
    list2(q_d_matrix, q_simp),
    cons(
      mk_simp(q_mlist, [
        q_d_function,
        q_d_time_slcall,
        q_d_calls,
        q_d_runtime,
        q_d_gctime,
      ]),
      nconc(
        nreverse(v),
        list1(timer_mlist(q_d_total, total_calls, total_runtime, total_gctime)),
      ),
    ),
  )
}

///|
fn timer_reset_1(fun : Value) -> Value raise {
  let fun_opr = getopr(fun)
  d_put(fun_opr, Fix(0L), q_d_runtime) |> ignore
  d_put(fun_opr, Fix(0L), q_d_gctime) |> ignore
  d_put(fun_opr, Fix(0L), q_d_calls)
}

///|
fn macsyma_timer(fun : Value) -> Value raise {
  let r = macsyma_trace_sub(fun, q_timer_handler, symval(q_d_timer))
  timer_reset_1(fun) |> ignore
  r
}

///|
fn macsyma_untimer(fun : Value) -> Value raise {
  macsyma_untrace_sub(fun, q_timer_handler, symval(q_d_timer))
}

///|
fn d_timer_reset(maybe_funs : Value) -> Value raise {
  let funs = if maybe_funs.truthy() {
    maybe_funs
  } else {
    cdr(symval(q_d_timer))
  }
  mapcar(f => timer_reset_1(f), funs) |> ignore
  cons(list1(q_mlist), funs)
}

///|
/// N.B. Doesn't even try to account for use of DYNAMIC CONTROL such as
/// ERRSET ERROR and CATCH and THROW, as these are rare and the overhead
/// for the unwind-protect is high.
fn timer_handler(fun : Value, largs : Value) -> Value raise {
  car(mtrace__timer_handler_mvl(fun, largs))
}

///|
/// TIMER-HANDLER returning `(multiple-value-list ...)` of its
/// MULTIPLE-VALUE-PROG1.
fn mtrace__timer_handler_mvl(fun : Value, largs : Value) -> Value raise {
  let mut runtime = mtrace__get_internal_run_time()
  let mut gctime : Value = Fix(0L) // (status gctime) is 0
  let mut old_runtime_devalue = symval(q_runtime_devalue)
  let mut old_gctime_devalue = symval(q_gctime_devalue)
  let result = mtrace__trace_apply_mvl(fun, largs)
  old_runtime_devalue = num_sub(symval(q_runtime_devalue), old_runtime_devalue)
  old_gctime_devalue = num_sub(symval(q_gctime_devalue), old_gctime_devalue)
  runtime = num_sub(
    num_sub(mtrace__get_internal_run_time(), runtime),
    old_runtime_devalue,
  )
  gctime = num_sub(num_sub(Fix(0L), gctime), old_gctime_devalue)
  if symval(q_d_timer_devalue).truthy() {
    set(q_runtime_devalue, num_add(symval(q_runtime_devalue), runtime))
    |> ignore
    set(q_gctime_devalue, num_add(symval(q_gctime_devalue), gctime)) |> ignore
  }
  d_put(fun, num_add(d_get(fun, q_d_runtime), runtime), q_d_runtime) |> ignore
  d_put(fun, num_add(d_get(fun, q_d_gctime), gctime), q_d_gctime) |> ignore
  d_put(fun, num_add(d_get(fun, q_d_calls), Fix(1L)), q_d_calls) |> ignore
  result
}

///|
fn init_mtrace() -> Unit raise {
  // (defmvar $trace (list '(mlist)) :properties ((assign 'neverset)))
  defvar_init(q_d_trace, list1(list1(q_mlist)))
  putprop(q_d_trace, q_neverset, q_assign) |> ignore
  defvar_init(q_trace_handling_stack, Nil)
  // This data should be formalized somehow at the time of definition of
  // the DEFining form.
  putprop(q_subr, q_expr, q_shadow) |> ignore
  putprop(q_lsubr, q_expr, q_shadow) |> ignore
  putprop(q_expr, q_expr, q_shadow) |> ignore
  putprop(q_mfexpr_stars, q_mfexpr_star, q_shadow) |> ignore
  putprop(q_mfexpr_star, q_mfexpr_star, q_shadow) |> ignore
  putprop(q_operators, q_operators, q_shadow) |> ignore
  putprop(q_mexpr, t, q_mget) |> ignore
  putprop(q_mexpr, q_expr, q_shadow) |> ignore
  // (defmvar $trace_max_indent 15. :properties ((assign 'assign-mode-check)
  //                                            (mode '$fixnum)))
  putprop(q_d_trace_max_indent, q_assign_mode_check, q_assign) |> ignore
  putprop(q_d_trace_max_indent, q_d_fixnum, q_mode) |> ignore
  putprop(
    q_spaceout,
    lfunc("spaceout-dimension", args => mtrace__spaceout_dimension(
      arg(args, 0),
      arg(args, 1),
    )),
    q_dimension,
  )
  |> ignore
  // The mfexpr+trace lambda calls `((funcall) hook args...)` through the
  // evaluator; make sure the CL function FUNCALL is callable by name.
  if !fboundp(q_funcall) {
    defun(q_funcall, args => funcall(arg(args, 0), args[1:].to_array()))
  }
}
