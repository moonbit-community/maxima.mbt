// Port of src/acall.lisp: run-time support for translated code, mainly
// array reference and assignment for the subscript syntax. In Maxima
// arrays go by an atomic name; lists and matrices may be hacked with the
// array syntax, which is convenient.

///|
fn interval_error(fun : Value, low : Value, high : Value) -> Value raise {
  merr("~@:M: lower bound ~M is greater than upper bound ~M", [fun, low, high])
}

///|
fn mfuncall(f : Value, l : Value) -> Value raise {
  if functionp_(f).truthy() {
    apply(f, l)
  } else {
    // (MACRO-FUNCTION F) / (SPECIAL-OPERATOR-P F) are always false here:
    // the port has no Lisp macros or special operators as symbols.
    mapply(f, l, f)
  }
}

///|
/// The element type of a Lisp array: FLONUM, FIXNUM or T.
fn acall__elt_type(a : Value) -> Value {
  match a {
    Vec(arr) =>
      match arr.elt {
        "fixnum" => q_fixnum
        "flonum" | "double-float" => q_flonum
        "t" => t
        _ => Nil
      }
    _ => Nil
  }
}

///|
/// ((MQAPPLY ARRAY) X Y) is a strange form, meaning (X)[Y].
fn marrayref(aarray : Value, ind1 : Value, inds : Value) -> Value raise {
  match aarray {
    Vec(_) | Str(_) =>
      if acall__elt_type(aarray).truthy() {
        aref(aarray, mlisp__int_indices(cons(ind1, inds)))
      } else {
        merr("MARRAYREF: encountered array ~M of unknown type.", [aarray])
      }
    Hash(_) =>
      gethash(
        if inds.truthy() {
          cons(ind1, inds)
        } else {
          ind1
        },
        aarray,
      )
    Nil | Sym(_) =>
      if symval(q_d_use_fast_arrays).truthy() {
        let tem = if boundp(aarray) { symval(aarray) } else { Nil }
        simplify(
          if arrayp(tem) {
            aref(tem, mlisp__int_indices(cons(ind1, inds)))
          } else if hash_table_p(tem) {
            gethash(
              if inds.truthy() {
                cons(ind1, inds)
              } else {
                ind1
              },
              tem,
            )
          } else if eq(aarray, q_mqapply) {
            marrayref(ind1, car(inds), cdr(inds))
          } else if mget(aarray, q_hashar).truthy() {
            harrfind(list_star([list2(aarray, q_array), ind1, inds]))
          } else if symbolp(tem) {
            list_star([list2(tem, q_array), ind1, inds])
          } else {
            raise LispError::SimpleError(
              "unknown type of array for use_fast_arrays. the value cell should have the array or hash table",
            )
          },
        )
      } else {
        // no fast arrays
        simplify(
          {
            let ap = get(aarray, q_array)
            if ap.truthy() {
              let val = aref(ap, mlisp__int_indices(cons(ind1, inds)))
              // Check for KLUDGING array function implementation.
              let et = acall__elt_type(ap)
              let unbound = if eq(et, q_flonum) {
                numberp(val) && num_eq(val, symval(q_flounbound))
              } else if eq(et, q_fixnum) {
                numberp(val) && num_eq(val, symval(q_fixunbound))
              } else if eq(et, t) {
                eq(val, symval(q_munbound))
              } else {
                merr(
                  "MARRAYREF: encountered array pointer ~S of unknown type.",
                  [ap],
                )
                |> ignore
                false
              }
              if unbound {
                arrfind(list_star([list2(aarray, q_array), ind1, inds]))
              } else {
                val
              }
            } else if mget(aarray, q_array).truthy() {
              arrfind(list_star([list2(aarray, q_array), ind1, inds]))
            } else if mget(aarray, q_hashar).truthy() {
              harrfind(list_star([list2(aarray, q_array), ind1, inds]))
            } else if eq(aarray, q_mqapply) {
              marrayref(ind1, car(inds), cdr(inds))
            } else {
              list_star([list2(aarray, q_array), ind1, inds])
            }
          },
        )
      }
    Cons(_) =>
      simplify(
        if eq(caar(aarray), q_mlist) || eq(caar(aarray), q_d_matrix) {
          list_ref(aarray, cons(ind1, inds))
        } else {
          list_star([list2(q_mqapply, q_array), aarray, ind1, inds])
        },
      )
    _ => merr("MARRAYREF: cannot retrieve an element of ~M", [aarray])
  }
}

///|
fn d_arrayapply(ar : Value, inds : Value) -> Value raise {
  if !d_listp(inds).truthy() {
    merr("arrayapply: second argument must be a list; found ~M", [inds])
    |> ignore
  }
  if cdr(inds) is Nil {
    raise LispError::SimpleError(
      "invalid number of arguments to MARRAYREF: 1",
    )
  }
  marrayref(ar, cadr(inds), cddr(inds))
}

///|
fn d_arraysetapply(ar : Value, inds : Value, val : Value) -> Value raise {
  if !d_listp(inds).truthy() {
    merr("arraysetapply: second argument must be a list; found ~M", [inds])
    |> ignore
  }
  marrayset(val, ar, cdr(inds))
}

///|
fn marrayset(val : Value, aarray : Value, all_inds : Value) -> Value raise {
  let ind1 = first(all_inds)
  let inds = rest(all_inds)
  let quoted = () => list_star([
    list2(aarray, q_array),
    mapcar(u => list2(list2(q_mquote, q_simp), u), all_inds),
  ])
  match aarray {
    Vec(_) | Str(_) =>
      if acall__elt_type(aarray).truthy() {
        aset(aarray, mlisp__int_indices(all_inds), val) |> ignore
      } else {
        merr("MARRAYSET: encountered array ~M of unknown type.", [aarray])
        |> ignore
      }
    Hash(_) =>
      sethash(
        if cdr(all_inds).truthy() {
          copy_list(all_inds)
        } else {
          car(all_inds)
        },
        aarray,
        val,
      )
      |> ignore
    Nil | Sym(_) => {
      let ap = get(aarray, q_array)
      if ap.truthy() {
        aset(ap, mlisp__int_indices(all_inds), val) |> ignore
      } else {
        let ap = mget(aarray, q_array)
        if ap.truthy() {
          // the macsyma ARRAY frob is NOT an array pointer, it is a GENSYM
          // with a lisp array property, don't ask me why.
          aset(get(ap, q_array), mlisp__int_indices(all_inds), val) |> ignore
        } else if mget(aarray, q_hashar).truthy() {
          arrstore(quoted(), val) |> ignore
        } else if eq(aarray, q_mqapply) {
          marrayset(val, ind1, inds) |> ignore
        } else {
          arrstore(quoted(), val) |> ignore
        }
      }
    }
    Cons(_) =>
      if eq(caar(aarray), q_mlist) || eq(caar(aarray), q_d_matrix) {
        list_ref(aarray, all_inds, set_flag=t, val~) |> ignore
      } else {
        merr("MARRAYSET: cannot assign to an element of ~M", [aarray]) |> ignore
      }
    _ => merr("MARRAYSET: ~M is not an array.", [aarray]) |> ignore
  }
  val
}

///|
/// Note that all these have HEADERS on the list. The CAR of a list I will
/// call element 0. So [1,2][1] => 1
fn list_ref(
  l : Value,
  indexl : Value,
  set_flag? : Value = Nil,
  val? : Value = Nil,
) -> Value raise {
  if atom(l) {
    merr("LIST-REF: argument must be a list; found ~M", [l])
  } else if cdr(indexl) is Nil {
    let n = car(indexl)
    if integerp(n) &&
      plusp(n) &&
      (eq(caar(l), q_mlist) || eq(caar(l), q_d_matrix)) {
      let mut j = 1L
      let mut ll = cdr(l)
      while !(ll is Nil || num_eq(Fix(j), n)) {
        j += 1L
        ll = cdr(ll)
      }
      let ret = if ll is Nil {
        merr("LIST-REF: invalid subscript: ~M", [n])
      } else if set_flag.truthy() {
        rplaca(ll, val)
      } else {
        car(ll)
      }
      if set_flag.truthy() {
        l
      } else {
        ret
      }
    } else {
      merr("LIST-REF: invalid subscript: ~M", [n])
    }
  } else if set_flag.truthy() {
    list_ref(list_ref(l, list1(car(indexl))), cdr(indexl), set_flag~, val~)
    |> ignore
    l
  } else {
    list_ref(list_ref(l, list1(car(indexl))), cdr(indexl))
  }
}

///|
/// GET-INTERNAL-RUN-TIME, in microseconds of CPU time.
fn acall__get_internal_run_time() -> Value {
  Fix((cpu_time() * 1000000.0).to_int64())
}

///|
fn display_for_tr(labelsp : Value, equationsp : Value, argl : Value) -> Value raise {
  let mut lablist : Value = Nil
  for ans0 in argl.iter() {
    let mut ans = ans0
    if equationsp.truthy() &&
      // ((MEQUAL) FOO BAR)
      !atom(caddr(ans)) &&
      eq(caar(caddr(ans)), q_mequal) {
      // if the ANS evaluats to something with an "=" already then of
      // course he really meant to use DISP, but we might as well do what he
      // means right?
      ans = caddr(ans)
    }
    if labelsp.truthy() {
      if !checklabel(symval(q_d_linechar)).truthy() {
        set(q_d_linenum, num_add(symval(q_d_linenum), Fix(1L))) |> ignore
      }
      makelabel(symval(q_d_linechar)) |> ignore
      // setqs the free variable *LINELABEL*
      lablist = cons(symval(q_ear_linelabel), lablist)
      if !symval(q_d_nolabels).truthy() {
        set(symval(q_ear_linelabel), ans) |> ignore
      }
    }
    let tim = acall__get_internal_run_time()
    with_special(q_ear_display_labels_p, lbool(lablist.truthy()), () => displa(
      list3(
        list1(q_mlabel),
        if labelsp.truthy() {
          symval(q_ear_linelabel)
        } else {
          Nil
        },
        ans,
      ),
    ))
    |> ignore
    mterpri() |> ignore
    timeorg(tim) |> ignore
  }
  if labelsp.truthy() {
    cons(list1(q_mlist), nreverse(lablist))
  } else {
    q_d_done
  }
}

///|
fn insure_array_props(
  fnname : Value,
  ignore_mode : Value,
  number_of_args : Value,
) -> Value raise {
  ignore(ignore_mode)
  // called during load or eval time by the defining forms for translated
  // array-functions. this duplicates code in JPG;MLISP.
  add2lnc(fnname, symval(q_d_arrays)) |> ignore
  let ary = mgetl(fnname, list2(q_hashar, q_array))
  if ary.truthy() {
    let n = if eq(car(ary), q_hashar) {
      aref1(get(cadr(ary), q_array), 2)
    } else {
      int(length(cdr(arraydims(cadr(ary)))))
    }
    if !num_eq(n, number_of_args) {
      merr(
        "INSURE-ARRAY-PROPS: array ~:@M already defined with different dimensions.",
        [fnname],
      )
    } else {
      Nil
    }
  } else {
    let a = gensym()
    mputprop(fnname, a, q_hashar) |> ignore
    putprop(a, make_array([7], initial=Nil), q_array) |> ignore
    let arr = get(a, q_array)
    aset1(arr, 0, Fix(4L)) |> ignore
    aset1(arr, 1, Fix(0L)) |> ignore
    aset1(arr, 2, number_of_args)
  }
}

///|
let acall__tr_apply_name : Value = sym("the first arg to a translated `apply'")

///|
/// An entry point to $APPLY for translated code.
fn mapply_tr(fun : Value, list_ : Value) -> Value raise {
  if !d_listp(list_).truthy() {
    merr("apply: second argument must be a list; found ~M", [list_]) |> ignore
  }
  mapply1(fun, cdr(list_), acall__tr_apply_name, list_)
}

///|
fn assign_check(var_ : Value, val : Value) -> Value raise {
  let a = get(var_, q_assign)
  if a.truthy() {
    funcall(a, [var_, val])
  } else {
    Nil
  }
}

///|
fn maplist_tr(fun : Value, l1 : Value, l : Value) -> Value raise {
  let l = cons(l1, copy_list(l))
  simplify(
    with_special(q_maplp, t, () => {
      let res = map1(cons(getopr(fun), l))
      if atom(res) {
        list2(list1(q_mlist), res)
      } else if eq(caar(res), q_mlist) {
        res
      } else {
        cons(list1(q_mlist), margs(res))
      }
    }),
  )
}

///|
fn acall__booleanp(x : Value) -> Bool {
  x is Nil || eq(x, t)
}

///|
/// Entry point into DB for translated code. The main point here is that
/// evaluation of a form takes place first, (using the lisp evaluator), and
/// then the trueness is checked.
fn boole_verify(form : Value, error_q : Value, d_unknown_q : Value) -> Value raise {
  if acall__booleanp(form) {
    form
  } else if error_q.truthy() {
    pre_err(form)
  } else if d_unknown_q.truthy() {
    q_d_unknown
  } else {
    form
  }
}

///|
fn boole_eval(form : Value, error_q : Value, d_unknown_q : Value) -> Value raise {
  if acall__booleanp(form) {
    form
  } else {
    let ans = mevalp_tr(form, error_q)
    if acall__booleanp(ans) || !d_unknown_q.truthy() {
      ans
    } else {
      q_d_unknown
    }
  }
}

///|
fn d_is_boole_verify(form : Value) -> Value raise {
  boole_verify(form, symval(q_d_prederror), t)
}

///|
fn d_is_boole_eval(form : Value) -> Value raise {
  boole_eval(form, symval(q_d_prederror), t)
}

///|
fn d_maybe_boole_verify(form : Value) -> Value raise {
  boole_verify(form, Nil, t)
}

///|
fn d_maybe_boole_eval(form : Value) -> Value raise {
  boole_eval(form, Nil, t)
}

///|
fn mcond_boole_verify(form : Value) -> Value raise {
  boole_verify(form, symval(q_d_prederror), Nil)
}

///|
fn mcond_boole_eval(form : Value) -> Value raise {
  boole_eval(form, symval(q_d_prederror), Nil)
}

///|
fn mevalp_tr(pat : Value, error_q : Value) -> Value raise {
  boole_verify(mevalp1_tr(pat, error_q), error_q, Nil)
}

///|
fn mevalp1_tr(pat : Value, error_q : Value) -> Value raise {
  if atom(pat) {
    pat
  } else if eq(caar(pat), q_mnot) || eq(caar(pat), q_mand) || eq(caar(pat), q_mor) {
    let pred_eval = lfunc("pred-eval", a => mevalp_tr(arg(a, 0), error_q))
    if eq(q_mnot, caar(pat)) {
      is_mnot(pred_eval, cadr(pat))
    } else if eq(q_mand, caar(pat)) {
      is_mand(pred_eval, cdr(pat))
    } else {
      is_mor(pred_eval, cdr(pat))
    }
  } else {
    let ans = mevalp2(pat, caar(pat), cadr(pat), caddr(pat))
    if acall__booleanp(ans) {
      ans
    } else {
      pat
    }
  }
}

///|
/// Some functions for even faster calling of arrays.
fn marrayref1_dol(aarray : Value, index : Value) -> Value raise {
  if arrayp(aarray) {
    if eq(acall__elt_type(aarray), q_flonum) {
      aref(aarray, [to_int(index)])
    } else {
      merr("MARRAYREF1$: array must be an array of floats; found ~M", [aarray])
    }
  } else {
    marrayref(aarray, index, Nil)
  }
}

///|
fn marrayset1_dol(value : Value, aarray : Value, index : Value) -> Value raise {
  if arrayp(aarray) {
    if eq(acall__elt_type(aarray), q_flonum) {
      aset(aarray, [to_int(index)], value)
    } else {
      merr("MARRAYSET1$: array must be an array of floats; found ~M", [aarray])
    }
  } else {
    marrayset(value, aarray, list1(index))
  }
}

///|
fn application_operator(form : Value, ign : Value) -> Value raise {
  ignore(ign)
  apply(caar(form), cdr(form))
}

///|
/// more efficient operators calls.
fn n_starmminus(x : Value) -> Value raise {
  if numberp(x) {
    num_neg(x)
  } else {
    simplify(list2(list1(q_mminus), x))
  }
}

///|
fn retlist_tr(args : Value) -> Value raise {
  let mut j = length(args) - 2
  let mut l : Value = Nil
  while j >= 0 {
    l = cons(list3(list2(q_mequal, q_simp), nth(j, args), nth(j + 1, args)), l)
    j -= 2
  }
  cons(list2(q_mlist, q_simp), l)
}

///|
fn init_acall() -> Unit raise {
  putprop(q_d_is, q_d_is_boole_verify, q_tr_boole_verify) |> ignore
  putprop(q_d_is, q_d_is_boole_eval, q_tr_boole_eval) |> ignore
  putprop(q_d_maybe, q_d_maybe_boole_verify, q_tr_boole_verify) |> ignore
  putprop(q_d_maybe, q_d_maybe_boole_eval, q_tr_boole_eval) |> ignore
  putprop(q_mcond, q_mcond_boole_verify, q_tr_boole_verify) |> ignore
  putprop(q_mcond, q_mcond_boole_eval, q_tr_boole_eval) |> ignore
}
