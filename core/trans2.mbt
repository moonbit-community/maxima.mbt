// Port of src/trans2.lisp: translation properties for list and array
// manipulation, and the run-time array access functions MASET1/MAREF1.

///|
/// DEF%TR $RANDOM
fn trans2__tr_random(form : Value) -> Value raise {
  let r = translate(cadr(form))
  let mode = car(r)
  let arg = cdr(r)
  let m = find(mode, list2(q_d_fixnum, q_d_float))
  cons(if m.truthy() { m } else { q_d_number }, list2(q_d_random, arg))
}

///|
/// DEF%TR MCALL
fn trans2__tr_mcall(form : Value) -> Value raise {
  let form = cdr(form)
  let mode = if symbolp(car(form)) { function_mode(car(form)) } else { q_d_any }
  let form = tr_args(form)
  let op = car(form)
  call_and_simp(mode, q_mcall, cons(op, cdr(form)))
}

///|
/// TR-MASET
fn tr_maset(ar : Value, val : Value, inds : Value) -> Value raise {
  // Top-level forms need to define the variable first.
  if symval(q_ear_macexpr_top_level_form_p).truthy() {
    list4(
      q_d_any,
      q_progn,
      list3(q_defvar, ar, transl__quote(ar)),
      cons(q_maset, cons(val, cons(ar, inds))),
    )
  } else {
    cons(q_d_any, cons(q_maset, cons(val, cons(ar, inds))))
  }
}

///|
/// MASET1
fn maset1(val : Value, ar : Value, inds : Value) -> Value raise {
  let n = length(inds)
  if arrayp(ar) && n == array_rank(ar) {
    aset(ar, list_to_array(inds).map(i => to_int(i)), val)
  } else if hash_table_p(ar) {
    sethash(if cdr(inds).truthy() { copy_list(inds) } else { car(inds) }, ar, val)
  } else if symbolp(ar) {
    raise LispError::SimpleError(
      "MASET1: first argument must not be a symbol; found: " +
      princ_to_string(ar),
    )
  } else if n == 1 && (d_listp(ar).truthy() || d_matrixp(ar).truthy()) {
    rplaca(nthcdr(to_int(car(inds)), ar), val) |> ignore
    val
  } else if d_matrixp(ar).truthy() && n == 2 {
    rplaca(nthcdr(to_int(cadr(inds)), nth(to_int(car(inds)), ar)), val)
    |> ignore
    val
  } else {
    raise LispError::SimpleError("MASET1: invalid array reference: " + princ_to_string(ar))
  }
}

///|
/// TR-MAREF
fn tr_maref(ar : Value, inds : Value) -> Value raise {
  cons(q_d_any, cons(q_maref, cons(ar, copy_list(inds))))
}

///|
/// MAREF1
fn maref1(ar : Value, inds : Value) -> Value raise {
  let n = length(inds)
  if arrayp(ar) && n == array_rank(ar) {
    aref(ar, list_to_array(inds).map(i => to_int(i)))
  } else if hash_table_p(ar) {
    gethash(if cdr(inds).truthy() { inds } else { car(inds) }, ar)
  } else if symbolp(ar) {
    if mget(ar, q_hashar).truthy() {
      harrfind(cons(list2(ar, q_array), copy_list(inds)))
    } else {
      cons(list2(ar, q_array), copy_list(inds))
    }
  } else if n == 1 && (d_listp(ar).truthy() || d_matrixp(ar).truthy()) {
    nth(to_int(car(inds)), ar)
  } else if d_matrixp(ar).truthy() && n == 2 {
    nth(to_int(cadr(inds)), nth(to_int(car(inds)), ar))
  } else {
    merr("Wrong number of array indices: ~M", [cons(list1(q_mlist), inds)])
  }
}

///|
/// TR-ARRAYCALL
fn tr_arraycall(form : Value) -> Value raise {
  if symval(q_d_translate_fast_arrays).truthy() {
    let all_inds = mapcar(x => dtranslate(x), cdr(form))
    // not apply changed 'tr-maref
    tr_maref(cdr(translate(caar(form))), all_inds)
  } else {
    translate(
      cons(
        list1(q_marrayref),
        cons(
          if symval(q_d_tr_array_as_ref).truthy() {
            caar(form)
          } else {
            list2(list1(q_mquote), caar(form))
          },
          cdr(form),
        ),
      ),
    )
  }
}

///|
/// TR-ARRAYSETQ: actually an array SETF, but it comes from A[X]:FOO which
/// is ((MSETQ) ... ...)
fn tr_arraysetq(array_ref : Value, value : Value) -> Value raise {
  if symval(q_d_translate_fast_arrays).truthy() {
    tr_maset(
      caar(array_ref),
      dtranslate(value),
      mapcar(x => dtranslate(x), copy_list(cdr(array_ref))),
    )
  } else {
    // oops. Hey, I switch around order of evaluation here. no need to
    // either man. gee.
    translate(
      cons(
        list1(q_marrayset),
        cons(
          value,
          cons(
            if symval(q_d_tr_array_as_ref).truthy() {
              caar(array_ref)
            } else {
              list2(list1(q_mquote), caar(array_ref))
            },
            cdr(array_ref),
          ),
        ),
      ),
    )
  }
}

///|
/// DEF%TR MARRAYREF
fn trans2__tr_marrayref(form : Value) -> Value raise {
  let form = cdr(form)
  let mut mode = if symbolp(car(form)) {
    get(car(form), q_array_mode)
  } else {
    Nil
  }
  if mode is Nil {
    mode = q_d_any
  }
  let form = tr_args(form)
  let op = car(form)
  cons(
    mode,
    cons(
      if length(form) == 2 && eq(mode, q_d_float) {
        q_marrayref1_dol
      } else {
        q_marrayref
      },
      cons(op, cdr(form)),
    ),
  )
}

///|
/// DEF%TR MARRAYSET
fn trans2__tr_marrayset(form : Value) -> Value raise {
  let form = cdr(form)
  let mut mode = if symbolp(cadr(form)) {
    get(cadr(form), q_array_mode)
  } else {
    Nil
  }
  if mode is Nil {
    mode = q_d_any
  }
  let form = tr_args(form)
  let val = car(form)
  let aarray = cadr(form)
  let inds = cddr(form)
  cons(
    mode,
    cons(
      if length(inds) == 1 && eq(mode, q_d_float) {
        q_marrayset1_dol
      } else {
        q_marrayset
      },
      cons(val, cons(aarray, inds)),
    ),
  )
}

///|
/// DEF%TR MLIST
fn trans2__tr_mlist(form : Value) -> Value raise {
  if cdr(form) is Nil {
    // []
    cons(q_d_any, transl__quote(list1(list1(q_mlist))))
  } else {
    cons(
      q_d_any,
      cons(q_list, cons(transl__quote(list1(q_mlist)), tr_args(cdr(form)))),
    )
  }
}

///|
/// DEF%TR $FIRST
fn trans2__tr_first(form : Value) -> Value raise {
  let form = translate(cadr(form))
  call_and_simp(
    q_d_any,
    if eq(q_d_list, car(form)) {
      q_cadr
    } else {
      q_d_first
    },
    list1(cdr(form)),
  )
}

///|
fn init_trans2() -> Unit raise {
  transl__deftr(q_d_random, trans2__tr_random)
  transl__deftr(q_mcall, trans2__tr_mcall)
  transl__deftr(q_marrayref, trans2__tr_marrayref)
  transl__deftr(q_marrayset, trans2__tr_marrayset)
  transl__deftr(q_mlist, trans2__tr_mlist)
  transl__deftr(q_d_first, trans2__tr_first)
}
