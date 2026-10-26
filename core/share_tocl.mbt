// Port of share/contrib/tocl.lisp (Barton Willis, 2006, 2007): convert a
// Maxima expression into a Common Lisp form.
//
// 'common_lisp' converts a Maxima expression into a Lisp lambda form,
// translating Maxima operators into their closest Common Lisp
// counterparts (Maxima addition becomes CL '+', ...), so the generated
// lambda form works with numerical inputs, not symbolic ones:
//
// (%i1) common_lisp(a+b*c);
// (LAMBDA (A B C) (+ (* B C) A))
// (%o1) done
//
// 'to_cl' doesn't generate a lambda form, and 'cl_eval' evaluates the
// generated CL code.

///|
/// CL PRIN1 of a Lisp form, as SBCL prints it with Maxima's readtable:
/// symbol names in CL case (the inverse of the port's naming convention).
fn share_tocl__prin1(sb : StringBuilder, x : Value) -> Unit raise {
  match x {
    Nil => sb.write_string("NIL")
    Sym(s) => {
      let name = invert_case(s.name)
      let mut escape = name.length() == 0
      for c in name {
        if lower_case_p(c) ||
          c == ' ' ||
          c == '(' ||
          c == ')' ||
          c == '"' ||
          c == ';' ||
          c == '\'' ||
          c == '|' ||
          c == '\\' {
          escape = true
        }
      }
      if escape {
        sb.write_char('|')
        for c in name {
          if c == '|' || c == '\\' {
            sb.write_char('\\')
          }
          sb.write_char(c)
        }
        sb.write_char('|')
      } else {
        sb.write_string(name)
      }
    }
    Cons({ car: Sym({ name: "quote", .. }), cdr: Cons({ car: q, cdr: Nil }) }) => {
      sb.write_char('\'')
      share_tocl__prin1(sb, q)
    }
    Cons({ car: Sym({ name: "function", .. }), cdr: Cons({ car: q, cdr: Nil }) }) => {
      sb.write_string("#'")
      share_tocl__prin1(sb, q)
    }
    Cons(_) => {
      sb.write_char('(')
      let mut l = x
      let mut first = true
      while l is Cons(_) {
        if !first {
          sb.write_char(' ')
        }
        first = false
        share_tocl__prin1(sb, car(l))
        l = cdr(l)
      }
      if l.truthy() {
        sb.write_string(" . ")
        share_tocl__prin1(sb, l)
      }
      sb.write_char(')')
    }
    _ => sb.write_string(prin1_to_string(x))
  }
}

///|
/// CL PRINT: newline, PRIN1, space.
fn share_tocl__print(x : Value) -> Value raise {
  let sb = StringBuilder::new()
  sb.write_char('\n')
  share_tocl__prin1(sb, x)
  sb.write_char(' ')
  write_string(sb.to_string(), stream=symval(standard_output))
  x
}

///|
fn d_common_lisp(e : Value) -> Value raise {
  with_special(q_d_listconstvars, Nil, () => {
    // listofvars('if x < 0 then 0 else 1) --> [x, true]
    let vars = delete(t, margs(d_listofvars(e)))
    share_tocl__print(
      list([
        q_lambda,
        sort_list(mapcar(v => stripdollar(v), vars), (a, b) => invert_case(
            symbol_name(a),
          ) <
          invert_case(symbol_name(b))),
        expr_to_cl(nformat(d_ratdisrep(e))),
      ]),
    )
    |> ignore
    q_d_done
  })
}

///|
fn d_to_cl(e : Value) -> Value raise {
  share_tocl__print(expr_to_cl(nformat(d_ratdisrep(e)))) |> ignore
  q_d_done
}

///|
fn d_cl_eval(e : Value) -> Value raise {
  lisp_eval_form(expr_to_cl(nformat(d_ratdisrep(e))))
}

///|
fn lambda_tr(f : Value) -> Value raise {
  list([
    q_lambda,
    mapcar(x => expr_to_cl(x), margs(first(f))),
    expr_to_cl(second(f)),
  ])
}

///|
fn block_tr(f : Value) -> Value raise {
  let mut acc : Value = Nil
  let f1 = margs(first(f))
  for ai in f1.iter() {
    acc = cons(
      if op_equalp(ai, list1(q_msetq)).truthy() {
        mapcar(x => expr_to_cl(x), margs(ai))
      } else {
        list1(expr_to_cl(ai))
      },
      acc,
    )
  }
  acc = list1(reverse(acc))
  cons(sym("let"), append(acc, mapcar(x => expr_to_cl(x), cdr(f))))
}

///|
fn cond_tr(f : Value) -> Value raise {
  let mut acc : Value = Nil
  let mut f = f
  while f.truthy() {
    let f1 = expr_to_cl(car(f))
    f = cdr(f)
    let f2 = expr_to_cl(car(f))
    f = cdr(f)
    acc = cons(list2(f1, f2), acc)
  }
  cons(q_cond, reverse(acc))
}

///|
fn mdefine_tr(f : Value) -> Value raise {
  list([
    q_defun,
    caaar(f),
    mapcar(x => expr_to_cl(x), cdar(f)),
    expr_to_cl(cadr(f)),
  ])
}

///|
fn mdo_tr(f : Value) -> Value raise {
  let k = expr_to_cl(nth(0, f))
  let lo = expr_to_cl(nth(1, f))
  let mut inc = expr_to_cl(nth(2, f))
  let hi = expr_to_cl(nth(4, f)) // skips (nth 3 f)?
  let mut pred = expr_to_cl(nth(5, f))
  let mut body = expr_to_cl(nth(6, f))
  let quote_done = list2(q_quote, q_d_done)
  if lo is Nil && hi is Nil && inc is Nil {
    list([sym("do"), Nil, list2(pred, quote_done), body])
  } else {
    if inc is Nil {
      inc = int(1)
    }
    let op = if num_gt(inc, int(0)) { sym(">") } else { sym("<") }
    pred = if pred.truthy() {
      list2(list([q_or, list([op, k, hi]), pred]), quote_done)
    } else {
      list2(list([op, k, hi]), quote_done)
    }
    body = expr_to_cl(nth(6, f))
    list([
      sym("do"),
      list1(list([k, lo, list([sym("incf"), k, inc])])),
      pred,
      body,
    ])
  }
}

///|
fn mapatom_expr_to_cl(e : Value) -> Value raise {
  if eq(e, q_d__pcti) {
    complex(int(0), i=int(1))
  } else if eq(e, q_d_true) || eq(e, t) {
    t
  } else if eq(e, q_d_false) || e is Nil {
    Nil
  } else if integerp(e) {
    e
  } else if d_ratnump(e).truthy() {
    list([sym("/"), d_num(e), d_denom(e)])
  } else if eq(e, q_d__pctpi) {
    Flo(@math.PI)
  } else if d_constantp(e).truthy() {
    d_float(e) // converts big floats to doubles
  } else {
    stripdollar(e)
  }
}

///|
fn expr_to_cl(e : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    mapatom_expr_to_cl(e)
  } else if get(mop(e), q_cl_translation_function).truthy() {
    apply(get(mop(e), q_cl_translation_function), margs(e))
  } else {
    let f = get(mop(e), q_cl_function)
    cons(
      if f.truthy() {
        f
      } else {
        stripdollar(mop(e))
      },
      mapcar(x => expr_to_cl(x), margs(e)),
    )
  }
}

///|
fn init_share_tocl() -> Unit raise {
  let fns = [
    (q_mplus, "+"),
    (q_mminus, "-"),
    (q_mtimes, "*"),
    (q_mquotient, "/"),
    (q_mexpt, "expt"),
    (q_mlessp, "<"),
    (q_mgreaterp, ">"),
    (q_mgeqp, ">="),
    (q_mleqp, "<="),
    (q_mprogn, "progn"),
    (q_mabs, "abs"),
    (q_msetq, "setq"),
    (q_mnot, "not"),
    (q_mand, "and"),
    (q_mor, "or"),
  ]
  for p in fns {
    putprop(p.0, sym(p.1), q_cl_function) |> ignore
  }
  putprop(q_lambda, q_lambda_tr, q_cl_translation_function) |> ignore
  putprop(q_mprog, q_block_tr, q_cl_translation_function) |> ignore
  putprop(q_mcond, q_cond_tr, q_cl_translation_function) |> ignore
  putprop(q_mdefine, q_mdefine_tr, q_cl_translation_function) |> ignore
  putprop(q_mdo, q_mdo_tr, q_cl_translation_function) |> ignore
}
