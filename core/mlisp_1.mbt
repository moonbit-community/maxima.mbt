// Port of src/mlisp.lisp, part 1: the evaluator proper -- MEVAL, MEVAL1,
// MAPPLY1, MLAMBDA, variable binding (MBIND/MUNBIND), LOCAL, assignment
// (MSET) and the defstruct-like records (@, defstruct, new).

///|
/// `(delete x l :count 1 :test #'eq)`: destructively remove the first
/// element of `l` that is EQ to `x`; returns the resulting list.
fn mlisp__delete1_eq(x : Value, l : Value) -> Value {
  match l {
    Cons(c) =>
      if eq(c.car, x) {
        c.cdr
      } else {
        let mut p = l
        while cdr(p) is Cons(n) {
          if eq(n.car, x) {
            rplacd(p, n.cdr) |> ignore
            break
          }
          p = cdr(p)
        }
        l
      }
    _ => l
  }
}

///|
/// `(delete x l :count 1 :test #'equal)`.
fn mlisp__delete1_equal(x : Value, l : Value) -> Value {
  match l {
    Cons(c) =>
      if equal(c.car, x) {
        c.cdr
      } else {
        let mut p = l
        while cdr(p) is Cons(n) {
          if equal(n.car, x) {
            rplacd(p, n.cdr) |> ignore
            break
          }
          p = cdr(p)
        }
        l
      }
    _ => l
  }
}

///|
/// Lisp truth of `(or a b)` where both are already computed values.
fn mlisp__or(a : Value, b : () -> Value raise) -> Value raise {
  if a.truthy() {
    a
  } else {
    b()
  }
}

///|
/// The MBINDING / MBINDING-SUB macro: bind VARS to VALS as Maxima
/// variables around BODY, unbinding them on any exit.
fn mlisp__mbinding(
  vars : Value,
  vals : Value,
  fname : Value,
  body : () -> Value raise,
) -> Value raise {
  let mut win = false
  defer {
    if win {
      munbind(vars) |> ignore
    }
  }
  mbind(vars, vals, fname) |> ignore
  win = true
  body()
}

///|
/// The function value of `#'eq`, for :TEST arguments.
let mlisp__eq_fn : Value = lfunc("eq", args => lbool(eq(arg(args, 0), arg(args, 1))))

///|
/// Integer subscripts of a Lisp array reference.
fn mlisp__int_indices(sub : Value) -> Array[Int] raise {
  let r = []
  for x in sub.iter() {
    r.push(to_int(x))
  }
  r
}

///|
/// Get the compiled function for the Lisp lambda expression FN, using
/// *LAMBDA-EXPR-FUNS* as a cache to reduce compiler invocations.
fn lambda_expr_fun(fn_ : Value) -> Value raise {
  if num_eq(symval(q_ear_lambda_expr_funs_max), Fix(0L)) {
    return lisp_function_of_lambda(fn_)
  }
  let table = symval(q_ear_lambda_expr_funs)
  let (cached, found) = gethash2(fn_, table)
  if found && cached.truthy() {
    return cached
  }
  let n = hash_table_count(table)
  if n >= to_int(symval(q_ear_lambda_expr_funs_max)) {
    // Hash table at the limit - drop a random entry.
    match table {
      Hash(h) => {
        let entries = h.entries()
        let k = (wall_time_ms() % n.to_uint64()).to_int()
        remhash(entries[k].0, table) |> ignore
      }
      _ => ()
    }
  }
  let f = lisp_function_of_lambda(fn_)
  sethash(fn_, table, f) |> ignore
  f
}

///|
fn mapply1(fn_ : Value, args : Value, fnname : Value, form : Value) -> Value raise {
  let aryp = symval(q_aryp)
  if atom(fn_) {
    if functionp_(fn_).truthy() {
      return apply(fn_, args)
    }
    if symbolp(fn_) && fboundp(fn_) {
      return mapply1(symbol_function(fn_), args, fn_, form)
    }
    if symbolp(fn_) && get(fn_, q_array).truthy() {
      return mapply1(get(fn_, q_array), args, fn_, form)
    }
    let f = getopr(amperchk(fn_))
    badfunchk(fnname, f, Nil) |> ignore
    return with_special(q_noevalargs, t, () => meval(cons(list1(f), args)))
  }
  // extension for pdiff; additional extension are welcomed.
  if consp(fn_) && consp(car(fn_)) && symbolp(mop(fn_)) {
    let ext = get(mop(fn_), q_mapply1_extension)
    if ext.truthy() {
      let r = apply(ext, list([fn_, args, fnname, form]))
      if r.truthy() {
        return r
      }
    }
  }
  if eq(car(fn_), q_lambda) {
    apply(lambda_expr_fun(fn_), args)
  } else if eq(caar(fn_), q_lambda) {
    mlambda(fn_, args, fnname, t, form)
  } else if eq(caar(fn_), q_mquote) {
    cons(append(cdr(fn_), aryp), args)
  } else if aryp.truthy() &&
    (eq(caar(fn_), q_mlist) || eq(caar(fn_), q_d_matrix)) {
    if !(length(args) == 1 || (eq(caar(fn_), q_d_matrix) && length(args) == 2)) {
      merr("apply: wrong number of indices; found: ~M", [
        cons(list1(q_mlist), args),
      ])
      |> ignore
    }
    if member(Fix(0L), args).truthy() {
      merr("apply: no such ~M element: ~M", [
        Str(if eq(caar(fn_), q_mlist) { "list" } else { "matrix" }),
        cons(list1(q_mlist), args),
      ])
      |> ignore
    }
    let mut args1 = args
    while args1 is Cons(_) {
      if !fixnump(car(args1)) {
        if symval(q_evarrp).truthy() {
          throw_tag(q_evarrp, q_notexist) |> ignore
        }
        merr("apply: subscript must be an integer; found: ~M", [car(args1)])
        |> ignore
      }
      args1 = cdr(args1)
    }
    with_specials([(q_d_piece, symval(q_d_piece)), (q_d_partswitch, q_mapply)], () => d_inpart(
      cons(fn_, args),
    ))
  } else if aryp.truthy() {
    cons(list2(q_mqapply, q_array), cons(fn_, args))
  } else {
    cons(list1(q_mqapply), cons(fn_, args))
  }
}

///|
/// The last argument to mapply1 for the lineinfo is not correct here..
fn mcall(fn_ : Value, args : Value) -> Value raise {
  mapply1(fn_, args, fn_, Nil)
}

///|
fn mevalargs(args : Value) -> Value raise {
  if symval(q_noevalargs).truthy() {
    set(q_noevalargs, Nil) |> ignore
    args
  } else {
    mapcar(x => meval(x), args)
  }
}

///|
/// Deactivate the topmost function call frame info. Return the function
/// designator for this frame and check that it is EQ to FNNAME if the
/// latter is non-NIL. (The frame info for a function call consists of 5
/// consecutive entries in *MLAMBDA-CALL-STACK*.)
fn pop_mlambda_call_stack(fnname? : Value = Nil) -> Value raise {
  let ar = symval(q_ear_mlambda_call_stack)
  let fp = fill_pointer(ar)
  let mlambda = aref1(ar, fp - 1)
  if fnname.truthy() && !eq(mlambda, fnname) {
    raise LispError::SimpleError(
      format_to_string("Expected ~a but got ~a on mlambda call stack.", [
        fnname, mlambda,
      ]),
    )
  }
  set_fill_pointer(ar, fill_pointer(ar) - 5)
  mlambda
}

///|
fn mlambda(
  fn_ : Value,
  args : Value,
  fnname : Value,
  noeval : Value,
  form : Value,
) -> Value raise {
  // We assume that the lambda expression handed to us has been simplified,
  // or at least that it's well-formed.
  set(q_noevalargs, Nil) |> ignore
  let b_mlocp = bind(q_mlocp, t)
  defer unbind(b_mlocp)
  let mut params = cdadr(fn_)
  let mut args = args
  let mut a : Value = Nil
  let mut p : Value = Nil
  while true {
    if params is Nil || (args is Nil && !mdeflistp(params).truthy()) {
      args = nreconc(a, args)
      params = nreconc(p, params)
      break
    }
    if mdeflistp(params).truthy() {
      params = cdar(params)
      args = list1(cons(list1(q_mlist), args))
    }
    if symval(q_mfexprp).truthy() && mquotep(car(params)).truthy() {
      a = cons(car(args), a)
      p = cons(cadar(params), p)
    } else if atom(car(params)) {
      p = cons(car(params), p)
      a = cons(
        if noeval.truthy() {
          car(args)
        } else {
          meval(car(args))
        },
        a,
      )
    } else {
      merr(
        "lambda: formal argument must be a symbol or quoted symbol; found: ~M",
        [car(params)],
      )
      |> ignore
    }
    args = cdr(args)
    params = cdr(params)
  }
  let finish2032 = params
  let mut finish2033 = false
  defer {
    if finish2033 {
      let st = symval(q_ear_mlambda_call_stack)
      set_fill_pointer(st, fill_pointer(st) - 5)
      munlocal() |> ignore
      munbind(finish2032) |> ignore
    }
  }
  let ar = symval(q_ear_mlambda_call_stack)
  vector_push_extend(symval(q_bindlist), ar) |> ignore
  vector_push_extend(form, ar) |> ignore
  vector_push_extend(params, ar) |> ignore
  vector_push_extend(args, ar) |> ignore
  vector_push_extend(fnname, ar) |> ignore
  mbind(finish2032, args, fnname) |> ignore
  set(q_loclist, cons(Nil, symval(q_loclist))) |> ignore
  finish2033 = true
  let aexprp = symval(q_aexprp).truthy() &&
    !atom(caddr(fn_)) &&
    eq(caar(caddr(fn_)), q_lambda)
  with_special(q_aexprp, lbool(aexprp), () => if cddr(fn_) is Nil {
    merr("lambda: no body present.", [])
  } else if cdddr(fn_) is Cons(_) {
    mevaln(cddr(fn_))
  } else {
    meval(caddr(fn_))
  })
}

///|
fn mprogn(form : Value) -> Value raise {
  mevaln(cdr(form))
}

///|
/// Called in a few places externally.
fn mevaln(l : Value) -> Value raise {
  with_special(q_d_op_pct_pct, q_d_op_pct_pct, () => {
    let mut body = l
    while cdr(body) is Cons(_) {
      set(q_d_op_pct_pct, meval(car(body))) |> ignore
      body = cdr(body)
    }
    meval(car(body))
  })
}

///|
fn mqapply1(form : Value) -> Value raise {
  let fn0 = cadr(form)
  let argl = cddr(form)
  with_special(q_aexprp, Nil, () => {
    let fn_ = if mquotep(fn0).truthy() { fn0 } else { meval(fn0) }
    let aryp = symval(q_aryp)
    if atom(fn_) {
      meval(cons(cons(amperchk(fn_), aryp), argl))
    } else if eq(caar(fn_), q_lambda) {
      if aryp.truthy() {
        merr("lambda: cannot apply lambda as an array function.", [])
      } else {
        mlambda(fn_, argl, cadr(form), symval(q_noevalargs), form)
      }
    } else {
      mapply1(fn_, mevalargs(argl), cadr(form), form)
    }
  })
}

///|
fn meval(form : Value) -> Value raise {
  let (result, args_simplified) = meval1(form)
  simplifya(result, args_simplified)
}

///|
/// temporary hack to see what's going on:
fn safe_mgetl(atom_ : Value, inds : Value) -> Value raise {
  if symbolp(atom_) {
    let props = get(atom_, q_mprops)
    if props.truthy() {
      getl(props, inds)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn safe_mget(atom_ : Value, inds : Value) -> Value raise {
  if symbolp(atom_) {
    let props = get(atom_, q_mprops)
    if props.truthy() {
      getf(cdr(props), inds)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// Evaluate a symbol (the atomic case of MEVAL1).
fn mlisp__meval1_atom(form : Value) -> (Value, Value) raise {
  if !symbolp(form) {
    return (form, Nil)
  }
  if symval(q_d_numer).truthy() {
    let val = safe_mget(form, q_d_numer)
    if val.truthy() {
      return meval1(val)
    }
  }
  if !boundp(form) {
    let bindtest_value = safe_get(form, q_bindtest)
    if eq(bindtest_value, q_kw_deprecated) {
      // Variable is deprecated.  Print a warning, and set the value of the
      // variable so it can still be used.
      let info = cdr(assq(form, symval(q_ear_bindtest_deprecation_messages)))
      if info is Nil {
        merr(
          "Internal error: Deprecated variable ~M but no corresponding information found.",
          [form],
        )
        |> ignore
      }
      let msg = car(info)
      let val = cdr(info)
      mwarning(list1(aformat(Nil, msg, list1(form)))) |> ignore
      set(form, val) |> ignore
    } else if bindtest_value.truthy() {
      merr("evaluation: unbound variable ~:M", [form]) |> ignore
    } else {
      return (form, Nil)
    }
  }
  let val = symval(form)
  if symval(q_d_refcheck).truthy() &&
    memq(form, cdr(symval(q_d_values))).truthy() &&
    !memq(form, symval(q_ear_refchkl)).truthy() {
    set(q_ear_refchkl, cons(form, symval(q_ear_refchkl))) |> ignore
    mtell(list([Str("evaluation: ~:M has the value ~:M.~%"), form, val]))
    |> ignore
  }
  (val, Nil)
}

///|
fn meval1(form : Value) -> (Value, Value) raise {
  // timers of share/contrib/timeout.lisp (polled instead of interrupts)
  if share_timeout__deadline.val != 0UL {
    share_timeout__check_timers()
  }
  if atom(form) {
    return mlisp__meval1_atom(form)
  }
  let mut form = form
  if atom(car(form)) {
    form = cons(list1(car(form)), cdr(form))
  } else if !atom(caar(form)) {
    return (mapply1(caar(form), mevalargs(cdr(form)), caar(form), form), Nil)
  }
  let b_aryp = bind(q_aryp, Nil)
  defer unbind(b_aryp)
  let mut u : Value = Nil
  set(q_ear_last_meval1_form, form) |> ignore
  set(q_aryp, memq(q_array, cdar(form))) |> ignore
  // state: 0 = a, 1 = b, 2 = c
  let mut state = 0
  if !symval(q_aryp).truthy() &&
    (
      eq(caar(form), q_mplus) ||
      eq(caar(form), q_mtimes) ||
      eq(caar(form), q_mexpt) ||
      eq(caar(form), q_mnctimes)
    ) {
    state = 2
  } else if symval(q_ear_mdebug).truthy() && mdebug__meval1_check(form) {
    // (never taken: the breakpoint check only has side effects)
    ()
  } else if eq(caar(form), q_mqapply) {
    return (mqapply1(form), Nil)
  } else {
    badfunchk(caar(form), caar(form), Nil) |> ignore
  }
  while true {
    let aryp = symval(q_aryp)
    let op = caar(form)
    match state {
      0 => {
        // a
        u = safe_getl(op, list1(q_noun))
        if !u.truthy() &&
          symval(q_ear_nounsflag).truthy() &&
          symbolp(op) &&
          symbol_name(op).has_prefix("%") &&
          !(
            getl_lm_fcn_prop(op, list1(q_subr)).truthy() ||
            safe_getl(op, list1(q_mfexpr_star)).truthy()
          ) {
          d_verbify(op) |> ignore
          u = safe_getl(op, list1(q_noun))
        }
        if !u.truthy() && !aryp.truthy() && symval(q_d_transrun).truthy() {
          u = safe_getl(op, list1(q_translated_mmacro))
        }
        if !u.truthy() && !aryp.truthy() {
          let mut u2 = safe_mget(op, q_trace)
          if !u2.truthy() &&
            symval(q_d_transrun).truthy() &&
            safe_get(op, q_translated).truthy() &&
            !safe_mget(op, q_local_fun).truthy() {
            u2 = op
          }
          u = if u2.truthy() {
            getl_lm_fcn_prop(u2, list2(q_subr, q_mfexpr))
          } else {
            Nil
          }
        }
        if !u.truthy() {
          u = if aryp.truthy() {
            safe_mgetl(op, list2(q_hashar, q_array))
          } else {
            let m = safe_mgetl(op, list2(q_mexpr, q_mmacro))
            if m.truthy() {
              m
            } else {
              let f = safe_getl(op, list1(q_mfexpr_star))
              if f.truthy() {
                f
              } else {
                getl_lm_fcn_prop(op, list2(q_subr, q_macro))
              }
            }
          }
        }
        if u is Nil {
          state = 1
          continue
        }
        let ty = car(u)
        if eq(ty, q_hashar) {
          return (harrfind(cons(car(form), mevalargs(cdr(form)))), Nil)
        } else if eq(ty, q_subr) {
          return (apply(op, mevalargs(cdr(form))), Nil)
        } else if eq(ty, q_noun) {
          if memq(op, symval(q_ear_nounl)).truthy() ||
            symval(q_ear_nounsflag).truthy() {
            form = cons(cons(cadr(u), cdar(form)), cdr(form))
            state = 0
            continue
          } else if aryp.truthy() {
            state = 1
            continue
          } else if eq(op, q_p_sum) || eq(op, q_p_product) {
            let u3 = do_pctsum(cdr(form), op)
            set(q_noevalargs, Nil) |> ignore
            return (cons(list1(op), u3), Nil)
          } else {
            let args_simplified = lbool(!symval(q_noevalargs).truthy())
            return (meval2(mevalargs(cdr(form)), form), args_simplified)
          }
        } else if eq(ty, q_array) {
          return (arrfind(cons(car(form), mevalargs(cdr(form)))), Nil)
        } else if eq(ty, q_mexpr) {
          return (mlambda(cadr(u), cdr(form), op, symval(q_noevalargs), form), Nil)
        } else if eq(ty, q_mmacro) || eq(ty, q_translated_mmacro) {
          set(q_noevalargs, Nil) |> ignore
          return (meval(mmacro_apply(cadr(u), form)), Nil)
        } else if eq(ty, q_mfexpr_star) {
          set(q_noevalargs, Nil) |> ignore
          return (funcall(cadr(u), [form]), Nil)
        } else if eq(ty, q_mfexpr) {
          return (mlambda(cadr(u), cdr(form), op, symval(q_noevalargs), form), Nil)
        } else if eq(ty, q_macro) {
          set(q_noevalargs, Nil) |> ignore
          return (lisp_eval_form(cons(op, cdr(form))), Nil)
        } else {
          return (apply(cadr(u), mevalargs(cdr(form))), Nil)
        }
      }
      1 => {
        // b
        if !aryp.truthy() && symbolp(op) && load_function(op, t).truthy() {
          state = 0
          continue
        }
        badfunchk(op, op, Nil) |> ignore
        if symbolp(op) {
          u = lbool(boundp(op))
        } else {
          return (meval1_extend(form), Nil)
        }
        state = 2
        continue
      }
      _ => {
        // c
        let mut take_args = u is Nil ||
          (safe_get(op, q_operators).truthy() && !aryp.truthy())
        if !take_args {
          u = symval(op)
          take_args = eq(op, u)
        }
        if take_args {
          let args_simplified = lbool(!symval(q_noevalargs).truthy())
          let evaled_args = mevalargs(cdr(form))
          // If $NUMER is non-NIL, $%ENUMER is at its default value of NIL,
          // FORM is %e^exponent, and the exponent doesn't evaluate to a
          // number, then prevent the base %e from being replaced with its
          // numerical value.
          if symval(q_d_numer).truthy() &&
            !symval(q_d__pctenumer).truthy() &&
            eq(q_mexpt, caar(form)) &&
            eq(q_d__pcte, cadr(form)) &&
            !mnump(cadr(evaled_args)).truthy() {
            setf_car(evaled_args, q_d__pcte) |> ignore
          }
          form = meval2(evaled_args, form)
          let at_form = if safe_mget(caar(form), q_atvalues).truthy() {
            at1(form)
          } else {
            Nil
          }
          if at_form.truthy() {
            return (at_form, Nil)
          } else {
            return (form, args_simplified)
          }
        } else if aryp.truthy() && safe_get(op, q_nonarray).truthy() {
          let args_simplified = lbool(!symval(q_noevalargs).truthy())
          return (cons(cons(op, aryp), mevalargs(cdr(form))), args_simplified)
        } else if atom(u) {
          badfunchk(op, u, Nil) |> ignore
          // AMPERCHK turns a string into the same symbol the parser would
          // use, so F : "abc"$ F(2) behaves like "abc"(2).
          form = cons(cons(getopr(amperchk(u)), aryp), cdr(form))
          state = 0
          continue
        } else if eq(caar(u), q_lambda) {
          if aryp.truthy() {
            merr("lambda: cannot apply lambda as an array function.", [])
            |> ignore
          }
          return (mlambda(u, cdr(form), op, symval(q_noevalargs), form), Nil)
        } else {
          return (mapply1(u, mevalargs(cdr(form)), op, form), Nil)
        }
      }
    }
  }
  (Nil, Nil)
}

///|
fn getl_lm_fcn_prop(sym_ : Value, props : Value) -> Value raise {
  let mut fn_ = sym_
  let mut typ : Value = Nil
  if functionp_(fn_).truthy() {
    typ = q_subr
  } else if !symbolp(sym_) {
    ()
  } else if lisp_macro_p(sym_) {
    typ = q_macro
  } else {
    fn_ = get(sym_, q_array)
    if fn_.truthy() {
      typ = q_array
    } else {
      fn_ = get(sym_, q_mfexpr_star)
      if fn_.truthy() {
        typ = q_mfexpr_star
      } else {
        fn_ = get(sym_, q_mfexpr)
        if fn_.truthy() {
          typ = q_mfexpr
        }
      }
    }
  }
  if typ.truthy() && memq(typ, props).truthy() {
    list2(typ, fn_)
  } else {
    Nil
  }
}

///|
fn meval2(newargs : Value, old : Value) -> Value raise {
  let new_ = cons(car(old), newargs)
  if !memq(q_simp, cdar(old)).truthy() {
    if !eq(caar(new_), q_mlist) && equal(new_, old) {
      old
    } else {
      new_
    }
  } else {
    let nosimp = get(caar(new_), q_operators) is Nil
    if alike1(new_, old).truthy() {
      if nosimp {
        old
      } else {
        cons(delsimp(car(old)), cdr(old))
      }
    } else if nosimp {
      if symval(q_aryp).truthy() {
        new_
      } else {
        cons(cons(caar(new_), list1(q_simp)), newargs)
      }
    } else {
      cons(cons(caar(new_), symval(q_aryp)), newargs)
    }
  }
}

///|
fn mparam(var_ : Value) -> Value raise {
  if atom(var_) {
    var_
  } else if atom(cadr(var_)) {
    cadr(var_)
  } else {
    cadadr(var_)
  }
}

///|
fn mparams(vars : Value) -> Value raise {
  mapcar(v => mparam(v), cdr(vars))
}

///|
fn mop(form : Value) -> Value raise {
  if eq(caar(form), q_mqapply) {
    cadr(form)
  } else {
    caar(form)
  }
}

///|
fn badfunchk(fnname : Value, val : Value, flag : Value) -> Value raise {
  if flag.truthy() ||
    numberp(val) ||
    val is Nil ||
    eq(val, t) ||
    eq(val, q_d__pcte) ||
    eq(val, q_d__pctpi) ||
    eq(val, q_d__pcti) {
    let type_ = if symval(q_aryp).truthy() { "an array" } else { "a function" }
    if atom(fnname) && !equal(val, fnname) {
      merr("apply: found ~M evaluates to ~M where ~A was expected.", [
        fnname,
        val,
        Str(type_),
      ])
    } else {
      merr("apply: found ~M where ~A was expected.", [val, Str(type_)])
    }
  } else {
    Nil
  }
}

///|
fn symbol_values_in(expr : Value) -> Value raise {
  if atom(expr) {
    if symbolp(expr) {
      if boundp(expr) {
        // Do not take the actual value of $errormsg. It is always NIL at
        // this point, but the value which is stored in *$errormsg-value*.
        if eq(expr, q_d_errormsg) {
          symval(q_ear__dolerrormsg_value)
        } else {
          symval(expr)
        }
      } else {
        symval(q_munbound)
      }
    } else {
      expr
    }
  } else {
    cons(car(expr), mapcar(x => symbol_values_in(x), cdr(expr)))
  }
}

///|
/// Makes a new frame where the variables in the list LAMVARS are bound to
/// the corresponding elements in FNARGS.  Note that these elements are used
/// tels quels, without calling MEVAL. If FNNAME is non-NIL, it designates
/// a function call frame. This function does not handle errors properly,
/// use the MBIND wrapper for this.
fn mbind_doit(lamvars : Value, fnargs : Value, fnname : Value) -> Value raise {
  let mut vars = lamvars
  let mut args = fnargs
  while true {
    if vars.truthy() && args.truthy() {
      ()
    } else if vars is Nil && args is Nil {
      break
    } else {
      if fnname is Nil {
        raise LispError::SimpleError(
          "Expected a maxima function designator but got NIL.",
        )
      }
      merr("~A arguments supplied to ~M; found: ~M", [
        Str(if vars.truthy() { "Too few" } else { "Too many" }),
        if consp(fnname) && consp(car(fnname)) && eq(caar(fnname), q_lambda) {
          fnname
        } else {
          cons(list1(fnname), lamvars)
        },
        cons(list1(q_mlist), fnargs),
      ])
      |> ignore
    }
    let var_ = car(vars)
    if !(symbolp(var_) || every(x => symbolp(x), cdr(d_listofvars(var_)))) {
      merr("Only symbols can be bound; found: ~M", [var_]) |> ignore
    }
    let value = symbol_values_in(var_)
    with_special(q_mbindp, t, () => mset(var_, car(args))) |> ignore
    set(q_bindlist, cons(var_, symval(q_bindlist))) |> ignore
    set(q_mspeclist, cons(value, symval(q_mspeclist))) |> ignore
    vars = cdr(vars)
    args = cdr(args)
  }
  Nil
}

///|
/// Error-handling wrapper around MBIND-DOIT.
fn mbind(lamvars : Value, fnargs : Value, fnname : Value) -> Value raise {
  let r = try {
    let old_bindlist = symval(q_bindlist)
    // At this point store the value of $errormsg in a global. The macro
    // with-$error sets the value of $errormsg to NIL, but we need the
    // actual value in the routine mbind-doit.
    set(
      q_ear__dolerrormsg_value,
      if boundp(q_d_errormsg) {
        symval(q_d_errormsg)
      } else {
        symval(q_munbound)
      },
    )
    |> ignore
    let v = with_special(q_ear_merror_signals__dolerror_p, t, () => mbind_doit(
      lamvars, fnargs, fnname,
    )) catch {
      e => {
        let bl = symval(q_bindlist)
        if !eq(bl, old_bindlist) {
          munbind(nreverse(ldiff(bl, old_bindlist))) |> ignore
        }
        if fnname.truthy() {
          pop_mlambda_call_stack(fnname=fnname) |> ignore
        }
        raise e
      }
    }
    Some(v)
  } catch {
    LispError::Condition(s, _, payload) if s.name == "maxima-$error" => {
      merror(cadr(payload), cddr(payload)) |> ignore
      // Make absolutely sure that this handler (and mbind) doesn't return in
      // this situation since other code depends on this behaviour.
      throw_tag(q_macsyma_quit, t) |> ignore
      None
    }
    e => raise e
  }
  r.unwrap_or(Nil)
}

///|
fn munbind_makunbound(var_ : Value) -> Value raise {
  makunbound(var_) |> ignore
  // Remove VAR from $VALUES, like (DELETE VAR $VALUES :COUNT 1 :TEST #'EQ),
  // but without the overhead of a generic DELETE. This is called a lot.
  let mut l = symval(q_d_values)
  while !atom(cdr(l)) {
    if eq(cadr(l), var_) {
      rplacd(l, cddr(l)) |> ignore
      break
    }
    l = cdr(l)
  }
  Nil
}

///|
fn munbind(vars : Value) -> Value raise {
  for var_ in reverse(vars).iter() {
    with_special(q_munbindp, t, () => mset(var_, car(symval(q_mspeclist))))
    |> ignore
    set(q_mspeclist, cdr(symval(q_mspeclist))) |> ignore
    set(q_bindlist, cdr(symval(q_bindlist))) |> ignore
  }
  Nil
}

///|
/// This takes the place of something like
/// (DELETE (ASSOC (NCONS VAR) $DEPENDENCIES) $DEPENDENCIES 1)
fn mfunction_delete(var_ : Value, fn_a_list : Value) -> Value raise {
  mlisp__delete1_equal(assoc_equal(list1(var_), fn_a_list), fn_a_list)
}

///|
fn mlocal(l : Value) -> Value raise {
  set(q_loclist, cons(Nil, symval(q_loclist))) |> ignore
  with_special(q_mlocp, t, () => meval(cons(list1(q_d_local), cdr(l))))
}

///|
fn d_local(l : Value) -> Value raise {
  let l = cdr(l)
  if !symval(q_mlocp).truthy() {
    merr("local: must be called within a block or lambda.", []) |> ignore
  }
  for var_ in l.iter() {
    if !symbolp(var_) {
      improper_arg_err(var_, q_d_local) |> ignore
    } else if mget(var_, q_array).truthy() && arrayp(get(var_, q_array)) {
      merr("local: argument cannot be a declared array; found: ~M", [var_])
      |> ignore
    }
    set(q_mproplist, cons(get(var_, q_mprops), symval(q_mproplist))) |> ignore
    set(q_factlist, cons(get(var_, q_data), symval(q_factlist))) |> ignore
    // Record VAR on the LOCLIST frame right away, in lock-step with the
    // MPROPLIST/FACTLIST pushes above, so that MUNLOCAL restores everything
    // processed so far even if a later argument turns out to be invalid.
    let loclist = symval(q_loclist)
    rplaca(loclist, cons(var_, car(loclist))) |> ignore
    for fact in car(symval(q_factlist)).iter() {
      putprop_(fact, Fix(-1L), q_ulabs) |> ignore
    }
    mfunction_delete(var_, symval(q_d_functions)) |> ignore
    mfunction_delete(var_, symval(q_d_macros)) |> ignore
    mfunction_delete(var_, symval(q_d_dependencies)) |> ignore
    set(q_d_arrays, mlisp__delete1_eq(var_, symval(q_d_arrays))) |> ignore
    zl_remprop(var_, q_mprops) |> ignore
    zl_remprop(var_, q_data) |> ignore
  }
  set(q_mlocp, Nil) |> ignore
  q_d_done
}

///|
fn munlocal() -> Value raise {
  for var_ in car(symval(q_loclist)).iter() {
    let mprop = car(symval(q_mproplist))
    let fact = car(symval(q_factlist))
    remcompary(var_) |> ignore
    cput(var_, mprop, q_mprops) |> ignore
    let mut y = getf(cdr(mprop), q_mexpr)
    if y.truthy() {
      add2lnc(cons(list1(var_), cdadr(y)), symval(q_d_functions)) |> ignore
    } else {
      mfunction_delete(var_, symval(q_d_functions)) |> ignore
    }
    y = getf(cdr(mprop), q_mmacro)
    if y.truthy() {
      add2lnc(cons(list1(var_), cdadr(y)), symval(q_d_macros)) |> ignore
    } else {
      mfunction_delete(var_, symval(q_d_macros)) |> ignore
    }
    if getf(cdr(mprop), q_array).truthy() || getf(cdr(mprop), q_hashar).truthy() {
      add2lnc(var_, symval(q_d_arrays)) |> ignore
    } else {
      set(q_d_arrays, mlisp__delete1_eq(var_, symval(q_d_arrays))) |> ignore
    }
    y = getf(cdr(mprop), q_depends)
    if y.truthy() {
      add2lnc(cons(list1(var_), y), symval(q_d_dependencies)) |> ignore
    } else {
      mfunction_delete(var_, symval(q_d_dependencies)) |> ignore
    }
    rempropchk(var_) |> ignore
    for dat in get(var_, q_data).iter() {
      uncntxt(dat) |> ignore
      remov(dat) |> ignore
    }
    cput(var_, fact, q_data) |> ignore
    for u in fact.iter() {
      zl_remprop(u, q_ulabs) |> ignore
    }
    set(q_mproplist, cdr(symval(q_mproplist))) |> ignore
    set(q_factlist, cdr(symval(q_factlist))) |> ignore
  }
  set(q_loclist, cdr(symval(q_loclist)))
}

///|
/// A "run-time macro" needed by MATCOM/MATRUN.
fn msetq(l : Value) -> Value raise {
  twoargcheck(l) |> ignore
  let x = simplifya(cadr(l), Nil)
  mset(x, meval(caddr(l)))
}

///|
fn mset(x : Value, y : Value) -> Value raise {
  let mut y = y
  let setcheck = symval(q_d_setcheck)
  if setcheck is Nil || eq(setcheck, q_d_setcheck) {
    ()
  } else if (
      atom(setcheck) ||
      memalike(x, cdr(setcheck)).truthy() ||
      (!atom(x) && memalike(caar(x), cdr(setcheck)).truthy())
    ) &&
    !eq(x, y) {
    mtell(list([Str("~:M is being set to ~:M.~%"), x, y])) |> ignore
    if symval(q_d_setcheckbreak).truthy() && !eq(x, q_d_setval) {
      with_special(q_d_setval, y, () => {
        merrbreak(arg=t) |> ignore
        y = symval(q_d_setval)
      })
    }
  }
  let munbindp = symval(q_munbindp).truthy()
  if atom(x) {
    if !symbolp(x) || mget(x, q_d_numer).truthy() || get(x, q_sysconst).truthy() {
      if munbindp {
        return Nil
      }
      if mget(x, q_d_numer).truthy() {
        merr(
          "assignment: cannot assign to ~M; it is a declared numeric quantity.",
          [x],
        )
        |> ignore
      } else if stringp(x) {
        merr("assignment: cannot assign to string \"~M\"", [x]) |> ignore
      } else {
        merr("assignment: cannot assign to ~M", [x]) |> ignore
      }
    }
    if munbindp && eq(y, symval(q_munbound)) {
      munbind_makunbound(x) |> ignore
      return Nil
    }
    // Run the ASSIGN check. Skip it only for the self-binding (MSET VAR VAR)
    // that MBIND-DOIT performs for plain block and lambda variables, and for
    // MUNBIND restoring such a binding; a user-level X: 'X must be checked.
    let f = get(x, q_assign)
    if f.truthy() &&
      (
        !eq(x, y) ||
        !(symval(q_mbindp).truthy() || munbindp) ||
        eq(f, q_neverset)
      ) {
      if eq(funcall(f, [x, y]), q_munbindp) {
        return Nil
      }
    }
    let sm = get(x, q_setter_method)
    if sm.truthy() {
      // There's a setter method defined.  Call it to set the variable to
      // the appropriate value.  Return whatever the setter returns.
      return funcall(sm, [x, y])
    }
    if !boundp(x) && !symval(q_dsksetp).truthy() {
      add2lnc(x, symval(q_d_values)) |> ignore
    } else if !eq(x, y) && optionp(x).truthy() {
      if symval(q_d_optionset).truthy() {
        mtell(list([Str("assignment: assigning to option ~M"), x])) |> ignore
      }
      if !eq(x, q_d_linenum) {
        add2lnc(x, symval(q_d_myoptions)) |> ignore
      }
    }
    return set(x, y)
  }
  // Check to see if the operator has an mset_extension_operator. If so,
  // this says how to do assignments. Examples, a@b:x. Put
  // mset_extension_operator of mrecord-assign on the atom $@.  To allow
  // [a,b]:[3,4] put op on mlist.
  //
  // X is could be something like (($FOO ARRAY) 42), in which case it is
  // meaningful to look for an assignment operator associated either with
  // $FOO itself or with $FOO's object type, with "object type" = (CAAR
  // (SYMBOL-VALUE '$FOO)).
  let x_value = if boundp(caar(x)) { symval(caar(x)) } else { Nil }
  let mset_extension_op = {
    let e = get(caar(x), q_mset_extension_operator)
    if e.truthy() {
      e
    } else if !atom(x_value) &&
      get(caar(x_value), q_defstruct_template).truthy() {
      get(caar(x_value), q_mset_extension_operator)
    } else {
      Nil
    }
  }
  if mset_extension_op.truthy() {
    return funcall(mset_extension_op, [x, y])
  }
  if memq(q_array, cdar(x)).truthy() {
    arrstore(x, y)
  } else {
    merr("assignment: cannot assign to ~M", [x])
  }
}

// CHANGES WRT FATEMAN'S STUFF.
// (1) $NEW BARFS IF #ARGUMENTS != 1, OR ARGUMENT HAS NO DEFSTRUCT, OR WRONG
//     NUMBER OF INITIALIZERS.
// (2) $DEFSTRUCT ALLOWS 1 OR MORE ARGUMENTS, RETURNS A LIST OF DEFSTRUCTS.
// (3) USE $PUT AND $GET TO MAINTAIN DEFSTRUCT PROPERTIES (RENAMED TO
//     $DEFSTRUCT_DEFAULT AND $DEFSTRUCT_TEMPLATE).
// (4) @ EVALUATES LHS AND QUOTES RHS
// (5) $STRUCTURES INFOLIST
// (6) LBP = 200, RBP = 201 (HIGHER PRECEDENCE, LEFT-ASSOCIATIVE)
// (7) A@B => A@B WHEN B IS NOT BOUND TO SOMETHING OTHER THAN ITSELF
// (8) DISALLOW @ APPLIED TO EXPRESSIONS W/ OPERATOR NOT DECLARED BY DEFSTRUCT
// (9) MAKE RECORD AND LIST ASSIGNMENT FUNCTIONS LISP FUNCTIONS
// (10) EXTEND KILL TO TAKE ITEMS OFF $STRUCTURES AND REMOVE DEFSTRUCT
//      PROPERTIES
// (11) EXTEND KILL TO RECOGNIZE KILL(X@Y)
// (12) EVALUATE INITIALIZERS IN $DEFSTRUCT AND IN $NEW
// (13) DISPLAY FIELDS WHICH HAVE BEEN ASSIGNED VALUES AS FOO(X = BAR, Y = BAZ)
// (14) ASSIGN TRANSLATION PROPERTY TO 'DEFSTRUCT AND DEF-SAME%TR ALL
//      STRUCTURES

///|
/// Field index of FIELD in a record (an integer, or its position in the
/// template); -1 if there is none, or it is not a fixnum.
fn mlisp__field_index(field : Value, template : Value) -> Int? raise {
  if integerp(field) {
    match field {
      Fix(n) =>
        if n >= -2147483648L && n <= 2147483647L {
          Some(n.to_int())
        } else {
          Some(-1)
        }
      _ => Some(-1)
    }
  } else {
    let p = position(field, template)
    if p < 0 {
      None
    } else {
      Some(p)
    }
  }
}

///|
/// Assume @-expr is (($@..) instance-name field-name).
fn mrecord_assign(n_at_expr : Value, value : Value) -> Value raise {
  let instance = cadr(n_at_expr)
  let field = caddr(n_at_expr)
  let object = meval(instance)
  let template = if consp(object) && consp(car(object)) {
    get(caar(object), q_defstruct_template)
  } else {
    Nil
  }
  if !template.truthy() {
    merr(
      "MRECORD-ASSIGN: left-hand side doesn't appear to be a defstruct object:~%~M",
      [instance],
    )
  } else {
    let index = match mlisp__field_index(field, template) {
      Some(i) => i
      None => {
        merr("assignment: no such field: ~M @ ~M", [instance, field]) |> ignore
        -1
      }
    }
    if 0 < index && index < length(object) {
      rplaca(nthcdr(index, object), value) |> ignore
    } else {
      merr("assignment: no such field: ~M @ ~M", [instance, field]) |> ignore
    }
    value
  }
}

///|
/// MRECORD-KILL is very similar to MRECORD-ASSIGN.
fn mrecord_kill(n_at_expr : Value) -> Value raise {
  let instance = cadr(n_at_expr)
  let field = caddr(n_at_expr)
  let object = meval(instance)
  let template = if consp(object) && consp(car(object)) {
    get(caar(object), q_defstruct_template)
  } else {
    Nil
  }
  if !template.truthy() {
    merr(
      "MRECORD-KILL: left-hand side doesn't appear to be a defstruct object:~%~M",
      [instance],
    )
  } else {
    let index = match mlisp__field_index(field, template) {
      Some(i) => i
      None => {
        merr("kill: no such field: ~M @ ~M", [instance, field]) |> ignore
        -1
      }
    }
    if 0 < index && index < length(object) {
      let v = nth(index, template)
      rplaca(nthcdr(index, object), v) |> ignore
      v
    } else {
      merr("kill: no such field: ~M @ ~M", [instance, field])
    }
  }
}

///|
fn d_op_at(l : Value) -> Value raise {
  let a = cadr(l)
  let b = caddr(l)
  let e = d__at_function(meval(a), b)
  if eq(e, b) {
    l
  } else {
    e
  }
}

///|
fn d__at_function(in_ : Value, fn_ : Value) -> Value raise {
  if !listp(in_) {
    // noun form
    list3(list1(q_p_op_at), in_, fn_)
  } else if get(caar(in_), q_defstruct_template).truthy() {
    let index = match
      mlisp__field_index(fn_, get(caar(in_), q_defstruct_template)) {
      Some(i) => i
      None => {
        merr("@: no such field: ~M @ ~M", [in_, fn_]) |> ignore
        -1
      }
    }
    if 0 < index && index < length(in_) {
      nth(index, in_)
    } else {
      merr("@: no such field: ~M @ ~M", [in_, fn_])
    }
  } else {
    list3(list1(q_d_op_at), in_, fn_)
  }
}

///|
fn dimension_defstruct(form : Value, result : Value) -> Value raise {
  let l1 = cdr(get(caar(form), q_defstruct_template))
  let l2 = cdr(form)
  dimension_function(
    cons(
      car(form),
      mapcar2(
        (e1, e2) => if eq(e1, e2) { e1 } else { mk(q_mequal, [e1, e2]) },
        l1,
        l2,
      ),
    ),
    result,
  )
}

///|
/// L looks like defstruct (foo(...), bar(...), baz(...)). Process each
/// argument and return a list of declared structures.
fn d_defstruct(l : Value) -> Value raise {
  cons(list1(q_mlist), mapcar(z => defstruct1(z), cdr(l)))
}

///|
fn defstruct_translate(form : Value) -> Value raise {
  ignore(form)
  merr("translate: not supported in this port", [])
}

///|
/// z should look like (($whatever) $a $b $c)
fn defstruct1(z : Value) -> Value raise {
  if !(consp(z) && consp(car(z))) {
    merr("defstruct: expected a structure template; found ~M", [z]) |> ignore
  }
  let name = caar(z)
  // store the template
  putprop(name, namesonly(z), q_defstruct_template) |> ignore
  // set the initialization
  putprop(name, initializersmostly(z), q_defstruct_default) |> ignore
  putprop(name, q_dimension_defstruct, q_dimension) |> ignore
  // Replace any entry for the same structure so that a redefinition does
  // not leave a stale duplicate behind (KILL only removes one entry).
  let rest = {
    let c = Collector::new()
    let mut removed = false
    for s in cdr(symval(q_d_structures)).iter() {
      if !removed && eq(caar(s), name) {
        removed = true
      } else {
        c.add(s)
      }
    }
    c.result()
  }
  set(
    q_d_structures,
    cons(list1(q_mlist), append(rest, list1(get(name, q_defstruct_default)))),
  )
  |> ignore
  putprop(name, q_defstruct_translate, q_translate) |> ignore
  putprop(name, q_simpstruct, q_operators) |> ignore
  get(name, q_defstruct_default)
}

///|
/// SIMPSTRUCT is the general simplifier for all structures defined via
/// DEFSTRUCT. Its purpose is to prevent Maxima functions such as "append",
/// "cons", "delete" or "rest" from being used on structure instances and
/// create invalid ones. SIMPSTRUCT raises an error if the number of
/// arguments doesn't match the number of fields of the structure.
/// SIMPSTRUCT simplifies the structure's values like SIMPLIFYA would do.
fn simpstruct(expr : Value, unused : Value, args_simplified : Value) -> Value raise {
  ignore(unused)
  let struct_ = caar(expr)
  let template = get(struct_, q_defstruct_template)
  let num_fields = length(cdr(template))
  let num_args = length(cdr(expr))
  if num_args != num_fields {
    merr("structure ~M: wrong number of arguments; expected ~M, not ~M.", [
      struct_,
      int(num_fields),
      int(num_args),
    ])
    |> ignore
  }
  simpargs(expr, args_simplified)
}

///|
/// f(a,b,c) unchanged, f(a=3,b=4,c=5) -> f(a,b,c)
fn namesonly(r : Value) -> Value raise {
  cons(
    car(r),
    mapcar(
      z => if symbolp(z) {
        z
      } else if mequalp(z).truthy() {
        second(z)
      } else {
        merr("defstruct: expected a record initializer; found: ~M", [z])
      },
      cdr(r),
    ),
  )
}

///|
/// f(a=3,b,c=5) -> f(3,b,5)
fn initializersmostly(r : Value) -> Value raise {
  cons(
    car(r),
    mapcar(
      z => if symbolp(z) {
        z
      } else if mequalp(z).truthy() {
        meval(third(z))
      } else {
        merr("defstruct: expected a record initializer; found: ~M", [z])
      },
      cdr(r),
    ),
  )
}

///|
fn d_new(h : Value) -> Value raise {
  if length(cdr(h)) != 1 {
    merr("new: expected exactly one argument; found: ~M", [int(length(cdr(h)))])
    |> ignore
  }
  let recordname = cadr(h)
  if symbolp(recordname) {
    // the case of, e.g.  new(f);
    if get(recordname, q_defstruct_default) is Nil {
      merr("new: no such structure ~M", [recordname]) |> ignore
    }
    copy_tree(get(recordname, q_defstruct_default))
  } else if atom(recordname) {
    // Not a symbol and not a call like new (f(5,6,7)): Complain!
    merr("new: no such structure ~M", [recordname])
  } else {
    // assume there is some initialization here e.g. new (f(5,6,7))
    let recordop = caar(recordname)
    let recordargs = cdr(recordname)
    if get(recordop, q_defstruct_default) is Nil {
      merr("new: no such structure ~M", [recordop]) |> ignore
    }
    if length(recordargs) != length(cdr(get(recordop, q_defstruct_default))) {
      merr(
        "new: wrong number of arguments in initializer; expected ~M, not ~M.",
        [
          int(length(cdr(get(recordop, q_defstruct_default)))),
          int(length(recordargs)),
        ],
      )
      |> ignore
    }
    cons(car(recordname), mapcar(x => meval(x), cdr(recordname)))
  }
}

///|
/// PARALLEL LIST assignment: [a,b,c]:[x,y,z] means about the same as a:x,
/// b:y, c:z, but evaluates x,y,z BEFORE any assignments to a,b,c. Also
/// [a,b,c]:x evaluates x once and assigns it to a,b,c. The value returned
/// is [ex,ex,ex].
fn mlist_assign(tlist : Value, vlist : Value) -> Value raise {
  // tlist is ((mlist..) var[0]... var[n]) of targets; vlist is either
  // ((mlist..) val[0]... val[n]) of values or possibly just one value.
  if listp(vlist) && eq(caar(vlist), q_mlist) && length(tlist) != length(vlist) {
    merr("assignment: lists must be the same length; found: ~M, ~M", [
      tlist, vlist,
    ])
    |> ignore
  }
  let tlist = cons(
    list1(q_mlist),
    mapcar(
      x =>
        // Let atoms through to MSET, which gives the regular error for
        // non-symbols.
        if atom(x) || get(caar(x), q_mset_extension_operator).truthy() {
          x
        } else {
          cons(car(x), mapcar(y => meval(y), cdr(x)))
        },
      cdr(tlist),
    ),
  )
  let mut vlist = vlist
  if !(listp(vlist) && eq(caar(vlist), q_mlist)) {
    // if [a,b,c]:v  then make a list [v,v,v]
    let c = Collector::new()
    for _ in 0..<(length(tlist) - 1) {
      c.add(vlist)
    }
    vlist = cons(car(tlist), c.result())
  }
  let mut p = cdr(tlist)
  let mut q = cdr(vlist)
  while p is Cons(_) && q is Cons(_) {
    mset(car(p), car(q)) |> ignore
    p = cdr(p)
    q = cdr(q)
  }
  vlist
}
