// Port of src/matcom.lisp: the Match Compiler (matchdeclare, defmatch,
// tellsimp, tellsimpafter, defrule).
//
// The Lisp original compiles every rule into a Lisp LAMBDA expression and
// hands it to FSET/COERCE, i.e. to the Lisp compiler.  The port has no Lisp
// evaluator, so the compilation step is kept unchanged -- COMPILEMATCH,
// COMPILEPLUS, COMPILETIMES, COMPILEEACH, COMPILEATOM and GETDEC still EMIT
// exactly the same list of Lisp forms into the special PROGRAM -- but the
// resulting program is run by a small evaluator (`matcom__lisp_eval`) that
// understands the forms the compiler emits (COND, SETQ, MSETQ, QUOTE, NOT,
// EQUAL, EQ, MEMBER, LIST, CONS, WHEN, RETLIST, VALUES, MATCHERR, KAR, KDR,
// ... and calls of any function installed in a symbol's function cell, such
// as MEVAL, ALIKE1, PART+, FINDFUN, DEFINITELY-SO).  The LAMBDA wrappers
// built around the program by PROC-$DEFMATCH and friends are MoonBit
// closures with the same binding and CATCH structure, installed in the
// rule's function cell.  Rule symbols, pattern variables and the PROG
// variables are special (dynamically bound) exactly as in the Lisp code.
//
// Rules return two values (ANS RULE-HIT).  The closures return a tuple;
// `matcom__mcall_mv` recovers it for callers (APPLY1, APPLY2, ...) that use
// MULTIPLE-VALUE-BIND on (MCALL rule expr).

///|
let matcom__mv_fns : Map[String, (Array[Value]) -> (Value, Value) raise] = Map::new()

///|
let matcom__fn_counter : Ref[Int32] = { val: 0, }

///|
/// `(fset name (coerce '(lambda ...) 'function))` for a rule function that
/// returns multiple values.
fn matcom__fset_mv(
  name : Value,
  f : (Array[Value]) -> (Value, Value) raise,
) -> Unit {
  match name {
    Sym({ func: Some(old), .. }) => matcom__mv_fns.remove(old.name)
    _ => ()
  }
  matcom__fn_counter.val += 1
  let id = "rule-function-" + matcom__fn_counter.val.to_string()
  matcom__mv_fns[id] = f
  defun(name, args => f(args).0, name=id)
}

///|
/// `(multiple-value-bind (ans rule-hit) (mcall f args...))`
fn matcom__mcall_mv(f : Value, args : Array[Value]) -> (Value, Value) raise {
  let lf = match f {
    Func(lf) => Some(lf)
    Sym({ func: Some(lf), .. }) => Some(lf)
    _ => None
  }
  match lf {
    Some(lf) =>
      match matcom__mv_fns.get(lf.name) {
        Some(g) => return g(args)
        None => ()
      }
    None => ()
  }
  (mcall(f, list(args)), Nil)
}

///|
fn matcom__check_args(args : Array[Value], n : Int32) -> Unit raise {
  if args.length() != n {
    raise LispError::SimpleError(
      "invalid number of arguments: \{args.length()} (expected \{n})",
    )
  }
}

// ---------------------------------------------------------------------------
// The evaluator for compiled match programs.

///|
fn matcom__progn(forms : Value) -> Value raise {
  let mut v : Value = Nil
  for f in forms.iter() {
    v = matcom__lisp_eval(f)
  }
  v
}

///|
/// Evaluate a Lisp form as produced by the match compiler.
fn matcom__lisp_eval(form : Value) -> Value raise {
  match form {
    Nil => Nil
    Sym(_) => if eq(form, t) || keywordp(form) { form } else { symval(form) }
    Cons({ car: head, cdr: rest, }) => {
      if is_op(form, q_lambda) {
        // ((lambda (args) body...) actuals...)
        let f = matcom__lisp_function(head)
        return apply(f, mapcar(x => matcom__lisp_eval(x), rest))
      }
      match head {
        Sym(_) => ()
        _ => raise LispError::SimpleError("illegal function call: \{form}")
      }
      if eq(head, q_quote) {
        return car(rest)
      }
      if eq(head, q_function) {
        return matcom__lisp_function(car(rest))
      }
      if eq(head, q_cond) {
        for clause in rest.iter() {
          let v = matcom__lisp_eval(car(clause))
          if v.truthy() {
            return if cdr(clause) is Nil {
              v
            } else {
              matcom__progn(cdr(clause))
            }
          }
        }
        return Nil
      }
      if eq(head, q_when) {
        return if matcom__lisp_eval(car(rest)).truthy() {
          matcom__progn(cdr(rest))
        } else {
          Nil
        }
      }
      if eq(head, q_unless) {
        return if matcom__lisp_eval(car(rest)) is Nil {
          matcom__progn(cdr(rest))
        } else {
          Nil
        }
      }
      if eq(head, q_if) {
        return if matcom__lisp_eval(car(rest)).truthy() {
          matcom__lisp_eval(cadr(rest))
        } else {
          matcom__progn(cddr(rest))
        }
      }
      if eq(head, q_not) || eq(head, q_null) {
        return lbool(matcom__lisp_eval(car(rest)) is Nil)
      }
      if eq(head, q_and) {
        let mut v = t
        for x in rest.iter() {
          v = matcom__lisp_eval(x)
          if v is Nil {
            return Nil
          }
        }
        return v
      }
      if eq(head, q_or) {
        for x in rest.iter() {
          let v = matcom__lisp_eval(x)
          if v.truthy() {
            return v
          }
        }
        return Nil
      }
      if eq(head, q_progn) {
        return matcom__progn(rest)
      }
      if eq(head, q_setq) {
        let mut l = rest
        let mut v : Value = Nil
        while l.truthy() {
          v = set(car(l), matcom__lisp_eval(cadr(l)))
          l = cddr(l)
        }
        return v
      }
      if eq(head, q_msetq) {
        // (defmacro msetq (a b) `(mset ',a ,b))
        return mset(car(rest), matcom__lisp_eval(cadr(rest)))
      }
      if eq(head, q_values) {
        return matcom__eval_mv(form).0
      }
      if eq(head, q_retlist) {
        // (defquote retlist (&rest l) ...): arguments are not evaluated.
        return cons(
          list2(q_mlist, q_simp),
          mapcar(z => list3(list2(q_mequal, q_simp), z, meval(z)), rest),
        )
      }
      let args = list_to_array(mapcar(x => matcom__lisp_eval(x), rest))
      matcom__call(head, args)
    }
    _ => form
  }
}

///|
/// Call a function of the match program on evaluated arguments.  CL
/// built-ins are handled here; everything else goes through the symbol's
/// function cell.
fn matcom__call(head : Value, args : Array[Value]) -> Value raise {
  let a0 = arg(args, 0)
  let a1 = arg(args, 1)
  if eq(head, q_eq) {
    lbool(eq(a0, a1))
  } else if eq(head, q_equal) {
    lbool(equal(a0, a1))
  } else if eq(head, q_member) {
    member(a0, a1)
  } else if eq(head, q_list) {
    list(args)
  } else if eq(head, q_cons) {
    cons(a0, a1)
  } else if eq(head, q_car) {
    car(a0)
  } else if eq(head, q_cdr) {
    cdr(a0)
  } else if eq(head, q_atom) {
    lbool(atom(a0))
  } else if eq(head, q_matcherr) {
    matcherr()
  } else if eq(head, q_kar) {
    kar(a0)
  } else if eq(head, q_kdr) {
    kdr(a0)
  } else if eq(head, q_kaar) {
    kaar(a0)
  } else if eq(head, q_meval) {
    meval(a0)
  } else if eq(head, q_alike1) {
    alike1(a0, a1)
  } else {
    funcall(head, args)
  }
}

///|
/// Evaluate FORM keeping a second value: `(values a b)` yields both.
fn matcom__eval_mv(form : Value) -> (Value, Value) raise {
  if consp(form) && eq(car(form), q_values) {
    let vals = list_to_array(mapcar(x => matcom__lisp_eval(x), cdr(form)))
    (arg(vals, 0), arg(vals, 1))
  } else {
    (matcom__lisp_eval(form), Nil)
  }
}

///|
/// `(function f)` / `#'(lambda ...)`: a function value for F.
fn matcom__lisp_function(f : Value) -> Value raise {
  if eq(car(f), q_function) || eq(car(f), q_quote) {
    return matcom__lisp_function(cadr(f))
  }
  if eq(car(f), q_lambda) {
    let params = cadr(f)
    let body = cddr(f)
    return lfunc("lambda", fn(args) raise {
      let ps = list_to_array(params)
      matcom__check_args(args, ps.length())
      let bs = bind_all(ps.mapi((i, p) => (p, args[i])))
      defer unbind_all(bs)
      let mut v : Value = Nil
      for x in body.iter() {
        if !(consp(x) && eq(car(x), q_declare)) {
          v = matcom__lisp_eval(x)
        }
      }
      v
    })
  }
  f
}

///|
/// `(catch 'match (prog VARS (declare (special ...)) ,@PRE ,@PROGRAM
/// (return RET)))`; RET may be `(values x t)`.
fn matcom__run_match(
  vars : Value,
  pre : Array[Value],
  program : Value,
  ret : Value,
) -> (Value, Value) raise {
  let run = fn() -> (Value, Value) raise {
    let bs = bind_all(list_to_array(vars).map(v => (v, Nil)))
    defer unbind_all(bs)
    for f in pre {
      matcom__lisp_eval(f) |> ignore
    }
    for f in program.iter() {
      matcom__lisp_eval(f) |> ignore
    }
    matcom__eval_mv(ret)
  }
  run() catch {
    LispError::Throw(tag, v) if eq(tag, q_match) => (v, Nil)
    e => raise e
  }
}

///|
/// The form checking that the expression is an array expression iff the
/// pattern is: `(when (not (member 'array (kar X))) (matcherr))` or
/// `(when (member 'array (kar X)) (matcherr))`.
fn matcom__array_check(pt : Value, x : Value) -> Value {
  let tst = list3(q_member, list2(q_quote, q_array), list2(q_kar, x))
  if memq(q_array, car(pt)).truthy() {
    list3(q_when, list2(q_not, tst), list1(q_matcherr))
  } else {
    list3(q_when, tst, list1(q_matcherr))
  }
}

// ---------------------------------------------------------------------------

///|
fn d_matchdeclare(form : Value) -> Value raise {
  with_special(q_meta_prop_p, Nil, () => proc__dolmatchdeclare(cdr(form)))
}

///|
/// Generates a new interned symbol for the rule system or returns a
/// recycled existing one from the symbol pool (*RULE-SYMBOL-POOL*).
fn get_rule_symbol() -> Value raise {
  let pool = symval(q_ear_rule_symbol_pool)
  let s = if pool.truthy() {
    set(q_ear_rule_symbol_pool, cdr(pool)) |> ignore
    car(pool)
  } else {
    sym(symbol_name(gensym(prefix="rule-symbol-")))
  }
  set(q_ear_current_rule_symbols, cons(s, symval(q_ear_current_rule_symbols)))
  |> ignore
  s
}

///|
/// Frees the symbols SYMBOLS by clearing their values, functions and
/// property lists, then adding them to the symbol pool (*RULE-SYMBOL-POOL*)
/// for recycling.
fn free_rule_symbols(symbols : Value) -> Value raise {
  for s in symbols.iter() {
    makunbound(s) |> ignore
    match s {
      Sym({ func: Some(old), .. }) => matcom__mv_fns.remove(old.name)
      _ => ()
    }
    fmakunbound(s) |> ignore
    set_symbol_plist(s, Nil) |> ignore
    set(q_ear_rule_symbol_pool, cons(s, symval(q_ear_rule_symbol_pool)))
    |> ignore
  }
  Nil
}

///|
fn proc__dolmatchdeclare(x : Value) -> Value raise {
  if oddp(int(length(x))) {
    merr("matchdeclare: must be an even number of arguments.", []) |> ignore
  }
  let mut x = x
  while x.truthy() {
    if symbolp(car(x)) {
      let p = cadr(x)
      if !symbolp(p) &&
        (
          numberp(p) ||
          ({
            let o = caaadr(x)
            eq(o, q_mand) ||
            eq(o, q_mor) ||
            eq(o, q_mnot) ||
            eq(o, q_mcond) ||
            eq(o, q_mprog)
          })
        ) {
        improper_arg_err(p, q_d_matchdeclare) |> ignore
      }
      meta_add2lnc(car(x), q_d_props) |> ignore
      meta_mputprop(car(x), list1(p), q_matchdeclare) |> ignore
    } else if d_listp(car(x)) is Nil {
      improper_arg_err(car(x), q_d_matchdeclare) |> ignore
    } else {
      for l in cdar(x).iter() {
        proc__dolmatchdeclare(list2(l, cadr(x))) |> ignore
      }
    }
    x = cddr(x)
  }
  q_d_done
}

///|
fn compileatom(e : Value, p : Value) -> Value raise {
  let d = getdec(p, e)
  if d is Nil {
    emit(
      list2(
        q_cond,
        list2(
          list2(q_not, list3(q_equal, e, list2(q_quote, p))),
          list1(q_matcherr),
        ),
      ),
    )
  } else if memq(p, symval(q_boundlist)).truthy() {
    emit(
      list2(
        q_cond,
        list2(list2(q_not, list3(q_equal, e, p)), list1(q_matcherr)),
      ),
    )
  } else {
    set(q_boundlist, cons(p, symval(q_boundlist))) |> ignore
    emit(d)
  }
}

///|
fn emit(x : Value) -> Value raise {
  set(q_program, nconc(symval(q_program), list1(x)))
}

///|
fn memqargs(x : Value) -> Value raise {
  if numberp(x) || memq(x, symval(q_boundlist)).truthy() {
    x
  } else if symbolp(x) && x.truthy() && get(x, q_operators).truthy() {
    list2(q_quote, x)
  } else {
    list2(q_meval, list2(q_quote, x))
  }
}

///|
fn makepreds(l : Value, gg : Value) -> Value raise {
  if l is Nil {
    Nil
  } else {
    let first = if atom(car(l)) {
      let gg = get_rule_symbol()
      // (lambda (gg) (declare (special gg)) ,(getdec (car l) gg))
      let body = getdec(car(l), gg)
      lfunc("lambda", fn(args) raise {
        matcom__check_args(args, 1)
        let b = bind(gg, args[0])
        defer unbind(b)
        matcom__lisp_eval(body)
      })
    } else {
      defmatch1(car(l), get_rule_symbol())
    }
    ignore(gg)
    cons(first, makepreds(cdr(l), Nil))
  }
}

///|
fn defmatch1(pt : Value, e : Value) -> Value raise {
  let bs = bind_all([(q_topreflist, Nil), (q_program, Nil)])
  defer unbind_all(bs)
  set(q_topreflist, list1(e)) |> ignore
  if errset(() => compilematch(e, pt)) is None {
    merr("defmatch: failed to compile match for pattern ~M", [pt])
  } else {
    // NOTE TO TRANSLATORS: MEANING OF FOLLOWING TEXT IS UNKNOWN
    mtell(
      list([
        Str(
          "defmatch: ~M will be matched uniquely since sub-parts would otherwise be ambiguous.~%",
        ),
        pt,
      ]),
    )
    |> ignore
    let prog_variables = cdr(reverse(symval(q_topreflist)))
    let program = symval(q_program)
    // (lambda (e) (declare (special e))
    //   (catch 'match (prog ,prog-variables ,@program (return t))))
    lfunc("lambda", fn(args) raise {
      matcom__check_args(args, 1)
      let b = bind(e, args[0])
      defer unbind(b)
      matcom__run_match(prog_variables, [], program, t).0
    })
  }
}

///|
fn compileplus(e : Value, p : Value) -> Value raise {
  matcom__compile_sum_or_product(e, p, true)
}

///|
fn compiletimes(e : Value, p : Value) -> Value raise {
  matcom__compile_sum_or_product(e, p, false)
}

///|
/// `(meval '((mplus) e ((mminus) x)))` resp. `(meval '((mquotient) e x))`
fn matcom__remove_form(e : Value, x : Value, plus : Bool) -> Value {
  if plus {
    list2(
      q_meval,
      list2(q_quote, list3(list1(q_mplus), e, list2(list1(q_mminus), x))),
    )
  } else {
    list2(q_meval, list2(q_quote, list3(list1(q_mquotient), e, x)))
  }
}

///|
/// COMPILEPLUS (PLUS = true) and COMPILETIMES (PLUS = false).  The two Lisp
/// functions are the same PROG with tags A, A1 and FUNCTIONMATCH, differing
/// only in the identity, the inverse operation, the MTIMES coefficient
/// clause (COMPILEPLUS only) and the zero test after FINDBASE
/// (COMPILETIMES only).
fn matcom__compile_sum_or_product(
  e : Value,
  p : Value,
  plus : Bool,
) -> Value raise {
  let b = bind(q_reflist, Nil)
  defer unbind(b)
  let opname = if plus { q_mplus } else { q_mtimes }
  let mut p = p
  let mut f : Value = Nil
  let mut g : Value = Nil
  let mut h : Value = Nil
  let mut flag = false
  let mut leftover : Value = Nil
  // 0 = A, 1 = A1, 2 = FUNCTIONMATCH
  let mut state = 0
  while true {
    match state {
      0 => {
        p = cdr(p)
        state = 1
      }
      1 =>
        if p is Nil {
          if leftover is Nil {
            return emit(
              list2(
                q_cond,
                list2(
                  list2(
                    q_not,
                    list3(q_equal, e, if plus { Fix(0L) } else { Fix(1L) }),
                  ),
                  list1(q_matcherr),
                ),
              ),
            )
          } else if cdr(leftover) is Nil {
            return compilematch(e, car(leftover))
          } else {
            f = intersection(leftover, symval(q_boundlist), pred2=(a, b) => {
              equal(a, b)
            })
            if f.truthy() {
              emit(list3(q_setq, e, matcom__remove_form(e, car(f), plus)))
              |> ignore
              leftover = matcom__delete_equal(car(f), leftover)
              state = 1
            } else {
              // Almost nobody knows what this means. Just suppress the noise.
              set(
                q_boundlist,
                append(
                  symval(q_boundlist),
                  remove_if_not(x => atom(x), leftover),
                ),
              )
              |> ignore
              return emit(
                list3(
                  q_cond,
                  list1(
                    list4(
                      if plus {
                        q_part_plus
                      } else {
                        q_part_star
                      },
                      e,
                      list2(q_quote, leftover),
                      list2(q_quote, makepreds(leftover, Nil)),
                    ),
                  ),
                  list2(t, list1(q_matcherr)),
                ),
              )
            }
          }
        } else if fixedmatchp(car(p)).truthy() {
          emit(list3(q_setq, e, matcom__remove_form(e, car(p), plus))) |> ignore
          state = 0
        } else if atom(car(p)) {
          if cdr(p).truthy() {
            leftover = cons(car(p), leftover)
            p = cdr(p)
            state = 1
          } else if leftover.truthy() {
            leftover = cons(car(p), leftover)
            p = Nil
            state = 1
          } else {
            set(q_boundlist, cons(car(p), symval(q_boundlist))) |> ignore
            emit(getdec(car(p), e)) |> ignore
            if cdr(p) is Nil {
              return Nil
            }
            state = 0
          }
        } else if plus && eq(caaar(p), q_mtimes) {
          let c = cadar(p)
          if !(numberp(c) || (!atom(c) && eq(caar(c), q_rat))) &&
            fixedmatchp(c).truthy() {
            flag = false
            let r = genref()
            emit(
              list3(
                q_setq,
                r,
                list2(q_ratdisrep, list3(q_ratcoef, e, memqargs(c))),
              ),
            )
            |> ignore
            compiletimes(
              car(symval(q_reflist)),
              cons(list1(q_mtimes), cddar(p)),
            )
            |> ignore
            emit(
              list3(
                q_setq,
                e,
                list2(
                  q_meval,
                  list2(
                    q_quote,
                    list2(
                      list1(q_d_ratsimp),
                      list3(
                        list1(q_mplus),
                        e,
                        list4(
                          list1(q_mtimes),
                          Fix(-1L),
                          car(symval(q_reflist)),
                          c,
                        ),
                      ),
                    ),
                  ),
                ),
              ),
            )
            |> ignore
            state = 0
          } else if !flag {
            flag = true
            rplacd(car(p), reverse(cdar(p))) |> ignore
            state = 1
          } else {
            leftover = cons(car(p), leftover)
            state = 0
          }
        } else if eq(caaar(p), q_mexpt) {
          let mut go_fm = false
          if fixedmatchp(cadar(p)).truthy() {
            f = q_findexpon
            g = cadar(p)
            h = caddar(p)
          } else if fixedmatchp(caddar(p)).truthy() {
            f = q_findbase
            g = caddar(p)
            h = cadar(p)
          } else {
            go_fm = true
          }
          if go_fm {
            state = 2
          } else {
            let r = genref()
            g = memqargs(g)
            emit(list3(q_setq, r, list4(f, e, g, list2(q_quote, opname))))
            |> ignore
            let rl = car(symval(q_reflist))
            if !plus && eq(f, q_findbase) {
              emit(
                list2(
                  q_cond,
                  list2(list3(q_equal, rl, Fix(0L)), list1(q_matcherr)),
                ),
              )
              |> ignore
            }
            let pw = if eq(f, q_findexpon) {
              list3(list1(q_mexpt), g, rl)
            } else {
              list3(list1(q_mexpt), rl, g)
            }
            emit(list3(q_setq, e, matcom__remove_form(e, pw, plus))) |> ignore
            compilematch(rl, h) |> ignore
            state = 0
          }
        } else if fixedmatchp(caaar(p)) is Nil {
          if cdr(p).truthy() {
            leftover = cons(car(p), leftover)
            p = cdr(p)
            state = 1
          } else if leftover.truthy() {
            leftover = cons(car(p), leftover)
            p = Nil
            state = 1
          } else {
            set(q_boundlist, cons(caaar(p), symval(q_boundlist))) |> ignore
            emit(list3(q_msetq, caaar(p), list2(q_kaar, e))) |> ignore
            state = 2
          }
        } else {
          state = 2
        }
      _ => {
        // FUNCTIONMATCH
        let r = genref()
        emit(
          list3(
            q_setq,
            r,
            list4(q_findfun, e, memqargs(caaar(p)), list2(q_quote, opname)),
          ),
        )
        |> ignore
        if eq(caaar(p), opname) {
          if plus {
            mtell(
              list([
                Str("COMPILEPLUS: warning: '+' within '+' in: ~M~%"),
                car(p),
              ]),
            )
            |> ignore
            compileplus(car(symval(q_reflist)), car(p)) |> ignore
          } else {
            mtell(
              list([
                Str("COMPILETIMES: warning: '*' within '*' in: ~M~%"),
                car(p),
              ]),
            )
            |> ignore
            compiletimes(car(symval(q_reflist)), car(p)) |> ignore
          }
        } else {
          let r2 = genref()
          emit(list3(q_setq, r2, list2(q_kdr, cadr(symval(q_reflist)))))
          |> ignore
          compileeach(car(symval(q_reflist)), cdar(p)) |> ignore
        }
        emit(list3(q_setq, e, matcom__remove_form(e, car(p), plus))) |> ignore
        state = 0
      }
    }
  }
  Nil
}

///|
/// `(delete x l :test #'equal)`
fn matcom__delete_equal(x : Value, l : Value) -> Value {
  let c = Collector::new()
  for y in l.iter() {
    if !equal(x, y) {
      c.add(y)
    }
  }
  c.result()
}

///|
fn d_defmatch(form : Value) -> Value raise {
  proc__doldefmatch(cdr(form))
}

///|
fn proc__doldefmatch(l : Value) -> Value raise {
  let bs = bind_all([
    (q_ear_current_rule_symbols, Nil),
    (q_boundlist, Nil),
    (q_reflist, Nil),
    (q_topreflist, Nil),
    (q_program, Nil),
  ])
  defer unbind_all(bs)
  let name = car(l)
  let mut pt_star = simplify(cadr(l))
  let mut pt = copy_tree(pt_star)
  if atom(pt) {
    pt_star = meval(pt)
    pt = copy_tree(pt_star)
    mtell(
      list([Str("defmatch: evaluation of atomic pattern yields: ~M~%"), pt]),
    )
    |> ignore
  }
  let args = cddr(l)
  if allatoms(args) is Nil {
    mtell(list([Str("defmatch: some pattern variables are not atoms.")]))
    |> ignore
    return Nil
  }
  set(q_boundlist, args) |> ignore
  let a = genref()
  if errset(() => compilematch(a, pt)) is None {
    free_rule_symbols(symval(q_ear_current_rule_symbols)) |> ignore
    return merr("defmatch: failed to compile match for pattern ~M", [pt])
  }
  let tem = cdr(reverse(symval(q_topreflist)))
  let boundlist = symval(q_boundlist)
  let program = symval(q_program)
  let pre = if atom(pt) { [] } else { [matcom__array_check(pt, a)] }
  let params = list_to_array(cons(a, args))
  let ret = if boundlist.truthy() { cons(q_retlist, boundlist) } else { t }
  matcom__fset_mv(name, fn(actuals) raise {
    matcom__check_args(actuals, params.length())
    let pb = bind_all(params.mapi((i, p) => (p, actuals[i])))
    defer unbind_all(pb)
    matcom__run_match(tem, pre, program, ret)
  })
  add2lnc(name, symval(q_d_rules)) |> ignore
  mputprop(
    name,
    list3(list1(q_mlist), pt_star, cons(list1(q_mlist), args)),
    q_d_rule,
  )
  |> ignore
  free_rule_symbols(get(name, q_rule_symbols)) |> ignore
  putprop(name, symval(q_ear_current_rule_symbols), q_rule_symbols) |> ignore
  name
}

///|
fn d_tellsimp(form : Value) -> Value raise {
  twoargcheck(form) |> ignore
  proc__doltellsimp(cdr(form))
}

///|
fn d_clear_rules() -> Value raise {
  mapc(x => kill1(x) |> ignore, cdr(symval(q_d_rules))) |> ignore
  for v in [q_mexpt, q_mplus, q_mtimes] {
    mputprop(v, Nil, q_rulenum) |> ignore
  }
  Nil
}

///|
/// The name of the rule function: OP followed by "rule" and RULENUM.
fn matcom__rule_name(oname : Value, rulenum : Value) -> Value raise {
  implode(
    append(
      p_to_dol(explodec(oname)),
      append(list([sym("r"), sym("u"), sym("l"), sym("e")]), mexploden(rulenum)),
    ),
  )
}

///|
fn proc__doltellsimp(l : Value) -> Value raise {
  let bs = bind_all([
    (q_ear_current_rule_symbols, Nil),
    (q_boundlist, Nil),
    (q_reflist, Nil),
    (q_topreflist, Nil),
    (q_program, Nil),
  ])
  defer unbind_all(bs)
  let pt = copy_tree(simplifya(car(l), Nil))
  let mut name = pt
  let rhs = copy_tree(simplifya(cadr(l), Nil))
  if alike1(pt, rhs).truthy() {
    merr("tellsimp: circular rule attempted.", []) |> ignore
  } else if atom(pt) {
    merr("tellsimp: pattern must not be an atom; found: ~A", [
      fullstrip1(getop(name)),
    ])
    |> ignore
  } else if ({
      name = caar(pt)
      mget(name, q_matchdeclare).truthy()
    }) {
    merr(
      "tellsimp: main operator of pattern must not be match variable; found: ~A",
      [fullstrip1(getop(name))],
    )
    |> ignore
  } else if eq(name, q_mplus) || eq(name, q_mtimes) {
    mtell(
      list([
        Str(
          "tellsimp: warning: rule will treat '~M' as noncommutative and nonassociative.~%",
        ),
        name,
      ]),
    )
    |> ignore
  }
  let a = genref()
  if errset(() => compileeach(a, cdr(pt))) is None {
    free_rule_symbols(symval(q_ear_current_rule_symbols)) |> ignore
    merr("tellsimp: failed to compile match for pattern ~M", [cdr(pt)])
    |> ignore
  }
  let oldstuff = get(name, q_operators)
  let mut rulenum = mget(name, q_rulenum)
  if rulenum is Nil {
    rulenum = Fix(1L)
  }
  let oname = getop(name)
  let pgname = matcom__rule_name(oname, rulenum)
  mputprop(pgname, name, q_ruleof) |> ignore
  add2lnc(pgname, symval(q_d_rules)) |> ignore
  mputprop(name, one_plus(rulenum), q_rulenum) |> ignore
  let tem = nconc(symval(q_boundlist), cdr(reverse(symval(q_topreflist))))
  let program = symval(q_program)
  let pre = [matcom__array_check(pt, q_x)]
  let ret = list3(q_values, memqargs(rhs), t)
  let rname = name
  matcom__fset_mv(pgname, fn(args) raise {
    // (lambda (x a2 a3) (declare (special x a2 a3)) (prog (ans a rule-hit) ...))
    matcom__check_args(args, 3)
    let lb = bind_all([(q_x, args[0]), (q_a2, args[1]), (q_a3, args[2])])
    defer unbind_all(lb)
    let pb = bind_all([(q_ans, Nil), (a, Nil)])
    defer unbind_all(pb)
    let a3 = symval(q_a3)
    let x0 = symval(q_x)
    set(
      q_x,
      cons(
        car(x0),
        set(
          a,
          if a3.truthy() {
            cdr(x0)
          } else {
            mapcar(h => simplifya(h, a3), cdr(x0))
          },
        ),
      ),
    )
    |> ignore
    let (ans, rule_hit) = matcom__run_match(tem, pre, program, ret)
    set(q_ans, ans) |> ignore
    let x = symval(q_x)
    let a2 = symval(q_a2)
    let res = if !eq(rname, q_mtimes) && !eq(rname, q_mplus) {
      if rule_hit.truthy() {
        ans
      } else if symval(q_dosimp) is Nil && memq(q_simp, cdar(x)).truthy() {
        x
      } else if oldstuff.truthy() {
        funcall(oldstuff, [x, a2, t])
      } else {
        eqtest(x, x)
      }
    } else if equal(Fix(1L), a2) && rule_hit.truthy() {
      ans
    } else if rule_hit.truthy() {
      if eq(rname, q_mtimes) {
        meval(list3(list1(q_mexpt), q_ans, q_a2))
      } else {
        meval(list3(list1(q_mtimes), q_ans, q_a2))
      }
    } else if oldstuff.truthy() {
      funcall(oldstuff, [x, a2, symval(q_a3)])
    } else {
      eqtest(x, x)
    }
    (res, Nil)
  })
  mputprop(pgname, list3(list1(q_mequal), pt, rhs), q_d_rule) |> ignore
  if mget(name, q_oldrules) is Nil {
    mputprop(name, list1(get(name, q_operators)), q_oldrules) |> ignore
  }
  putprop(name, pgname, q_operators) |> ignore
  free_rule_symbols(get(pgname, q_rule_symbols)) |> ignore
  putprop(pgname, symval(q_ear_current_rule_symbols), q_rule_symbols) |> ignore
  cons(
    list1(q_mlist),
    mputprop(name, cons(pgname, mget(name, q_oldrules)), q_oldrules),
  )
}

///|
/// `(%to$ l)`: replace a leading % by $.
fn p_to_dol(l : Value) -> Value raise {
  if eq(car(l), sym("%")) {
    rplaca(l, sym("$"))
  } else {
    l
  }
}

///|
fn d_tellsimpafter(form : Value) -> Value raise {
  twoargcheck(form) |> ignore
  proc__doltellsimpafter(cdr(form))
}

///|
fn proc__doltellsimpafter(l : Value) -> Value raise {
  let bs = bind_all([
    (q_ear_current_rule_symbols, Nil),
    (q_boundlist, Nil),
    (q_reflist, Nil),
    (q_topreflist, Nil),
    (q_program, Nil),
  ])
  defer unbind_all(bs)
  let pt = copy_tree(simplifya(car(l), Nil))
  let mut name = pt
  let rhs = copy_tree(simplifya(cadr(l), Nil))
  if alike1(pt, rhs).truthy() {
    merr("tellsimpafter: circular rule attempted.", []) |> ignore
  } else if atom(pt) {
    merr("tellsimpafter: pattern must not be an atom; found: ~A", [
      fullstrip1(getop(name)),
    ])
    |> ignore
  } else if ({
      name = caar(pt)
      mget(name, q_matchdeclare).truthy()
    }) {
    merr(
      "tellsimpafter: main operator of pattern must not be match variable; found: ~A",
      [fullstrip1(getop(name))],
    )
    |> ignore
  }
  let a = genref()
  let plustimes = eq(name, q_mplus) || eq(name, q_mtimes)
  let ok = if plustimes {
    errset(() => compilematch(a, pt))
  } else {
    errset(() => compileeach(a, cdr(pt)))
  }
  if ok is None {
    free_rule_symbols(symval(q_ear_current_rule_symbols)) |> ignore
    merr("tellsimpafter: failed to compile match for pattern ~M", [cdr(pt)])
    |> ignore
  }
  let oldstuff = get(name, q_operators)
  let mut rulenum = mget(name, q_rulenum)
  if rulenum is Nil {
    rulenum = Fix(1L)
  }
  let oname = getop(name)
  let pgname = matcom__rule_name(oname, rulenum)
  let my_afterflag = get_rule_symbol()
  set(my_afterflag, Nil) |> ignore
  mputprop(pgname, name, q_ruleof) |> ignore
  add2lnc(pgname, symval(q_d_rules)) |> ignore
  mputprop(name, one_plus(rulenum), q_rulenum) |> ignore
  let tem = nconc(symval(q_boundlist), cdr(reverse(symval(q_topreflist))))
  let program = symval(q_program)
  let rhs_form = memqargs(rhs)
  let announce = symval(q_d_announce_rules_firing).truthy()
  let rname = name
  matcom__fset_mv(pgname, fn(args) raise {
    // (lambda (x ans a3) ...); ANS is special.
    matcom__check_args(args, 3)
    let mut x = args[0]
    let a3 = args[2]
    let ab = bind(q_ans, args[1])
    defer unbind(ab)
    x = if oldstuff.truthy() {
      funcall(oldstuff, [x, symval(q_ans), a3])
    } else {
      simpargs1(x, symval(q_ans), a3)
    }
    if symval(my_afterflag).truthy() {
      return (x, Nil)
    }
    // (prog (a my*afterflag rule-hit) (declare (special a my*afterflag)) ...)
    let pb = bind_all([(a, Nil), (my_afterflag, Nil)])
    defer unbind_all(pb)
    set(my_afterflag, t) |> ignore
    if oldstuff.truthy() && (atom(x) || !eq(caar(x), rname)) {
      return (x, Nil)
    }
    set(a, if plustimes { x } else { cdr(x) }) |> ignore
    // X is lexical in the Lisp code; the array check sees its value.
    let pre = [matcom__array_check(pt, list2(q_quote, x))]
    let ret = if announce {
      list3(
        q_values,
        list4(
          q_announce_rule_firing,
          list2(q_quote, pgname),
          list2(q_quote, x),
          rhs_form,
        ),
        t,
      )
    } else {
      list3(q_values, rhs_form, t)
    }
    let (ans, rule_hit) = matcom__run_match(tem, pre, program, ret)
    set(q_ans, ans) |> ignore
    (if rule_hit.truthy() { ans } else { eqtest(x, x) }, Nil)
  })
  mputprop(pgname, list3(list1(q_mequal), pt, rhs), q_d_rule) |> ignore
  if mget(name, q_oldrules) is Nil {
    mputprop(name, list1(get(name, q_operators)), q_oldrules) |> ignore
  }
  putprop(name, pgname, q_operators) |> ignore
  free_rule_symbols(get(pgname, q_rule_symbols)) |> ignore
  putprop(pgname, symval(q_ear_current_rule_symbols), q_rule_symbols) |> ignore
  cons(
    list1(q_mlist),
    mputprop(name, cons(pgname, mget(name, q_oldrules)), q_oldrules),
  )
}

///|
fn announce_rule_firing(
  rulename : Value,
  expr : Value,
  simplified_expr : Value,
) -> Value raise {
  with_specials([(q_d_display2d, Nil), (q_d_stringdisp, Nil)], () => {
    d_print(
      list([Str("By"), rulename, Str(","), expr, Str("-->"), simplified_expr]),
    )
  })
  |> ignore
  simplified_expr
}

///|
fn d_defrule(form : Value) -> Value raise {
  proc__doldefrule(cdr(form))
}

///|
fn proc__doldefrule(l : Value) -> Value raise {
  let bs = bind_all([
    (q_ear_current_rule_symbols, Nil),
    (q_boundlist, Nil),
    (q_reflist, Nil),
    (q_topreflist, Nil),
    (q_program, Nil),
  ])
  defer unbind_all(bs)
  if length(l) != 3 {
    wna_err(q_d_defrule) |> ignore
  }
  let name = car(l)
  if !symbolp(name) ||
    eq(t, name) ||
    name is Nil ||
    mopp(name).truthy() ||
    eq(name, q_d_all) ||
    eq(name, q_d_op_pct) {
    merr(
      "defrule: rule name must be a symbol other than 'true', 'false', an operator, 'all' or '%'; found: ~M",
      [name],
    )
    |> ignore
  }
  let lhs_star = simplify(cadr(l))
  let pt = copy_tree(lhs_star)
  let rhs_star = simplify(caddr(l))
  let rhs = copy_tree(rhs_star)
  let a = genref()
  if errset(() => compilematch(a, pt)) is None {
    free_rule_symbols(symval(q_ear_current_rule_symbols)) |> ignore
    return merr("defrule: failed to compile match for pattern ~M", [pt])
  }
  let tem = nconc(symval(q_boundlist), cdr(reverse(symval(q_topreflist))))
  let program = symval(q_program)
  let pre = if atom(pt) { [] } else { [matcom__array_check(pt, a)] }
  let ret = list3(q_values, memqargs(rhs), t)
  matcom__fset_mv(name, fn(args) raise {
    // (lambda (a) (declare (special a)) (catch 'match (prog ...)))
    matcom__check_args(args, 1)
    let b = bind(a, args[0])
    defer unbind(b)
    matcom__run_match(tem, pre, program, ret)
  })
  add2lnc(name, symval(q_d_rules)) |> ignore
  let l = list3(list1(q_mequal), lhs_star, rhs_star)
  mputprop(name, l, q_d_rule) |> ignore
  mputprop(name, q_d_defrule, q_d_ruletype) |> ignore
  free_rule_symbols(get(name, q_rule_symbols)) |> ignore
  putprop(name, symval(q_ear_current_rule_symbols), q_rule_symbols) |> ignore
  list3(list1(q_msetq), name, cons(list1(q_marrow), cdr(l)))
}

// GETDEC constructs an expression of the form ``if <match> then <assign
// value> else <match failed>''.  See matcom.lisp for examples of the code
// generated for the various kinds of matchdeclare predicates.

///|
/// Return T if $MAYBE returns T, otherwise NIL.  That makes all non-T
/// values (e.g. $UNKNOWN or noun expressions) act like NIL.
fn definitely_so(e : Value) -> Value raise {
  lbool(eq(mfuncall(q_d_maybe, list1(e)), t))
}

///|
fn getdec(pattern_variable : Value, match_against : Value) -> Value raise {
  let p = mget(pattern_variable, q_matchdeclare)
  if p is Nil {
    return Nil
  }
  // P is (<foo>) where <foo> is the matchdeclare predicate.  If <foo> is
  // an atom, it is T or the name of a Lisp or Maxima function; otherwise
  // <foo> is ((<op>) <args>).
  if atom(car(p)) &&
    (eq(car(p), q_d_true) || eq(car(p), t) || eq(car(p), q_d_all)) {
    // generated code always assigns gensym value to pattern variable
    return list3(q_msetq, pattern_variable, match_against)
  }
  let p_op = car(p)
  let test_expr = if atom(p_op) {
    // P-OP is the name of a function. Try to generate a Lisp function call.
    if fboundp(p_op) && get(p_op, q_translated) is Nil {
      list3(q_eq, t, list2(p_op, match_against))
    } else {
      list2(q_definitely_so, list2(q_quote, list2(list1(p_op), match_against)))
    }
  } else {
    // Otherwise P-OP is something like ((<op>) <args>).
    let p_args = cdr(p_op)
    if eq(caar(p_op), q_lambda) {
      list2(
        q_definitely_so,
        list5_(
          q_mapply1,
          list2(q_quote, p_op),
          list2(q_list, match_against),
          t,
          Nil,
        ),
      )
    } else if eq(caar(p_op), q_mqapply) {
      list2(
        q_definitely_so,
        list2(q_meval, list2(q_quote, append(p_op, list1(match_against)))),
      )
    } else {
      // Otherwise P-OP must be a function call with the last arg missing.
      let margs_ = mapcar(x => memqargs(x), p_args)
      if consp(car(p_op)) && mget(caar(p_op), q_mmacro).truthy() {
        list2(
          q_definitely_so,
          list3(
            q_cons,
            list2(q_quote, car(p_op)),
            cons(q_list, append(margs_, list1(match_against))),
          ),
        )
      } else {
        list2(
          q_definitely_so,
          list3(
            q_cons,
            list2(q_quote, car(p_op)),
            list2(q_quote, append(margs_, list1(match_against))),
          ),
        )
      }
    }
  }
  list3(
    q_cond,
    list2(test_expr, list3(q_msetq, pattern_variable, match_against)),
    list1(list1(q_matcherr)),
  )
}

///|
fn list5_(a : Value, b : Value, c : Value, d : Value, e : Value) -> Value {
  cons(a, list4(b, c, d, e))
}

///|
fn compilematch(e : Value, p : Value) -> Value raise {
  let b = bind(q_reflist, Nil)
  defer unbind(b)
  if fixedmatchp(p).truthy() {
    emit(
      list2(
        q_cond,
        list2(
          list2(q_not, list3(q_alike1, e, list2(q_meval, list2(q_quote, p)))),
          list1(q_matcherr),
        ),
      ),
    )
    |> ignore
  } else if atom(p) {
    compileatom(e, p) |> ignore
  } else if eq(caar(p), q_mplus) {
    compileplus(e, p) |> ignore
  } else if eq(caar(p), q_mtimes) {
    compiletimes(e, p) |> ignore
  } else {
    compileatom(list2(q_kaar, e), caar(p)) |> ignore
    let r = genref()
    emit(list3(q_setq, r, list2(q_kdr, e))) |> ignore
    compileeach(car(symval(q_reflist)), cdr(p)) |> ignore
  }
  symval(q_program)
}

///|
fn genref() -> Value raise {
  let a = get_rule_symbol()
  set(q_topreflist, cons(a, symval(q_topreflist))) |> ignore
  car(set(q_reflist, cons(a, symval(q_reflist))))
}

///|
fn compileeach(elist : Value, plist : Value) -> Value raise {
  let b = bind(q_reflist, Nil)
  defer unbind(b)
  let mut plist = plist
  let mut count = 0
  set(q_reflist, cons(elist, symval(q_reflist))) |> ignore
  while true {
    count += 1
    if plist is Nil {
      return emit(
        list2(
          q_cond,
          list2(list3(q_nthkdr, elist, int(count - 1)), list1(q_matcherr)),
        ),
      )
    }
    let r = genref()
    emit(list3(q_setq, r, list2(q_kar, cadr(symval(q_reflist))))) |> ignore
    compilematch(car(symval(q_reflist)), car(plist)) |> ignore
    plist = cdr(plist)
    set(
      q_reflist,
      cons(list2(q_kdr, cadr(symval(q_reflist))), symval(q_reflist)),
    )
    |> ignore
  }
  Nil
}

///|
fn fixedmatchp(x : Value) -> Value raise {
  if numberp(x) {
    t
  } else if atom(x) {
    if memq(x, symval(q_boundlist)).truthy() || mget(x, q_matchdeclare) is Nil {
      t
    } else {
      Nil
    }
  } else if memq(caar(x), symval(q_boundlist)).truthy() ||
    mget(caar(x), q_matchdeclare) is Nil {
    fmp1(cdr(x))
  } else {
    Nil
  }
}

///|
fn fmp1(x : Value) -> Value raise {
  if x is Nil {
    t
  } else if fixedmatchp(car(x)).truthy() {
    fmp1(cdr(x))
  } else {
    Nil
  }
}
