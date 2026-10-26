// Port of share/contrib/noninteractive/asksign1.lisp (Robert Dodier,
// 2007): with no_questions true, asksign, askprop and askequal queries
// throw ((asksign) expr domain), ((askprop) object property) or
// ((askequal) a b), which noninteractive.mac catches to build conditional
// expressions.
//
// Loading the file redefines MEVAL*, $ERRCATCH, ENSURE-SIGN, ASK-PROP and
// $ASKEQUAL; the port installs the redefinitions in the core's function
// cells (`suprv1__meval_star_cell`, `compar__ensure_sign_cell`,
// `askp__ask_prop_cell`, `compar__d_askequal_cell`) and in the MFEXPR*
// property of $errcatch.

///|
/// Adapted from $CATCH in src/suprv1.lisp; CLEARSIGN call copied from
/// MEVAL* in src/suprv1.lisp.
fn share_asksign1__meval_star(e : Value) -> Value raise {
  with_special(q_d_e_pct, e, () => {
    let mcatch = cons(symval(q_bindlist), symval(q_loclist))
    let r = catch_tag(q_mcatch, () => mfuncall(
      share_noninteractive__q_meval1,
      list1(symval(q_d_e_pct)),
    ))
    // Clear the facts from asksign and friends.
    clearsign() |> ignore
    errlfun1(mcatch) |> ignore
    r
  })
}

///|
/// Adapted from MEVALN in src/mlisp.lisp; calls MEVAL* instead of MEVAL.
fn meval_starn(l : Value) -> Value raise {
  with_special(q_d_op_pct_pct, q_d_op_pct_pct, () => {
    let mut body = l
    while cdr(body).truthy() {
      set(q_d_op_pct_pct, meval(car(body))) |> ignore
      body = cdr(body)
    }
    meval_star(car(body))
  })
}

///|
/// Adapted from $ERRCATCH in src/suprv1.lisp: calls MEVAL*N instead of
/// MEVALN; also a special case for MERROR.
fn share_asksign1__errcatch(form : Value) -> Value raise {
  with_special(q_errcatch, cons(symval(q_bindlist), symval(q_loclist)), () => {
    let ret : Value = with_special(q_ear_mdebug, Nil, () => {
      match errset(() => meval_starn(cdr(form))) {
        Some(v) => list1(v)
        None => Nil
      }
    })
    if ret is Nil {
      errlfun1(symval(q_errcatch)) |> ignore
    }
    if consp(car(ret)) && eq(caar(car(ret)), q_merror) {
      mtell(cdr(car(ret))) |> ignore
      fresh_line() |> ignore
      list1(list1(q_mlist))
    } else {
      cons(list1(q_mlist), ret)
    }
  })
}

///|
/// Replaces ENSURE-SIGN in compar.lisp.
fn share_asksign1__ensure_sign(
  expr : Value,
  domain : Value,
  squared : Value,
) -> Value raise {
  if symval(q_d_no_questions).truthy() {
    let s = match_sign(symval(q_sign), domain, expr, squared)
    if s.truthy() {
      s
    } else {
      // PUT SQUARED HERE AS WELL ??
      meval(
        list2(
          list1(q_d_throw),
          list2(
            q_quote,
            list([
              list1(q_d_asksign),
              expr,
              if domain.truthy() {
                domain
              } else {
                q_d_pnz
              },
            ]),
          ),
        ),
      )
    }
  } else {
    // (funcall *interactive-ensure-sign*) calls the saved function with no
    // arguments
    raise LispError::SimpleError("invalid number of arguments: 0")
  }
}

///|
/// Replaces ASK-PROP in askp.lisp.
fn share_asksign1__ask_prop(
  object_ : Value,
  property : Value,
  fun_or_number : Value,
) -> Value raise {
  ignore(fun_or_number)
  if symval(q_d_no_questions).truthy() {
    meval(
      list2(
        list1(q_d_throw),
        list2(q_quote, list([list1(q_d_askprop), object_, property])),
      ),
    )
  } else {
    // (funcall *real-ask-prop*) calls the saved function with no arguments
    raise LispError::SimpleError("invalid number of arguments: 0")
  }
}

///|
/// Replaces $ASKEQUAL in src/compar.lisp.
fn share_asksign1__askequal(a : Value, b : Value) -> Value raise {
  if symval(q_d_no_questions).truthy() {
    // Throw askequal(a, b) only if askequal would actually ask the user
    // (i.e., askequal can't figure out the answer by itself). Following is
    // adapted from $ASKEQUAL in src/compar.lisp.
    let answer = meqp(sratsimp(a), sratsimp(b))
    if eq(answer, t) {
      q_d_yes
    } else if answer is Nil {
      q_d_no
    } else {
      meval(
        list2(
          list1(q_d_throw),
          list2(q_quote, list([list1(q_d_askequal), a, b])),
        ),
      )
    }
  } else {
    compar__d_askequal_base(a, b)
  }
}

///|
fn init_share_asksign1() -> Unit raise {
  suprv1__meval_star_cell.val = Some(share_asksign1__meval_star)
  register_mspec(q_d_errcatch, share_asksign1__errcatch)
  compar__ensure_sign_cell.val = Some(share_asksign1__ensure_sign)
  askp__ask_prop_cell.val = Some(share_asksign1__ask_prop)
  compar__d_askequal_cell.val = Some(share_asksign1__askequal)
}
