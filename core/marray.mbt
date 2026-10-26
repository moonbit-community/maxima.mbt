// Port of src/marray.lisp: Macsyma user array utilities.

///|
fn d_listarray(ary : Value) -> Value raise {
  let elems = if mget(ary, q_hashar).truthy() {
    mapcar(
      subs => d_arrayapply(ary, subs),
      cdddr(meval(list2(list1(q_d_arrayinfo), ary))),
    )
  } else if mget(ary, q_array).truthy() {
    listarray(mget(ary, q_array))
  } else if arrayp(ary) {
    if array_rank(ary) == 1 {
      vector_to_list(ary)
    } else {
      // (coerce (make-array (apply '* dims) :displaced-to ary) 'list)
      let a = as_array(ary)
      list(a.data[0:array_total_size(ary)].to_array())
    }
  } else if hash_table_p(ary) {
    let mut vals : Value = Nil
    maphash(
      (x, _) => if !eq(x, q_dim1) {
        vals = cons(gethash(x, ary), vals)
      },
      ary,
    )
    reverse(vals)
  } else if eq(marray_type(ary), q_d_functional) {
    // (mgenarray-content ary): slot 5 of the mgenarray structure (ar.lisp)
    cdr(d_listarray(struct_ref(ary, 5)))
  } else {
    merr("listarray: argument must be an array; found: ~M", [ary])
  }
  cons(list1(q_mlist), elems)
}

///|
fn d_fillarray(ary1 : Value, ary2 : Value) -> Value raise {
  let ary = {
    let m = mget(ary1, q_array)
    if m.truthy() {
      m
    } else if arrayp(ary1) {
      ary1
    } else {
      merr("fillarray: first argument must be a declared array; found: ~M", [
        ary1,
      ])
    }
  }
  let src = if d_listp(ary2).truthy() {
    cdr(ary2)
  } else {
    let g = get(mget(ary2, q_array), q_array)
    if g.truthy() {
      g
    } else if arrayp(ary2) {
      ary2
    } else {
      merr("fillarray: second argument must be an array or list; found: ~M", [
        ary2,
      ])
    }
  }
  fillarray(ary, src) |> ignore
  ary1
}

///|
fn getvalue(sym_ : Value) -> Value raise {
  if symbolp(sym_) && boundp(sym_) {
    symbol_value(sym_)
  } else {
    Nil
  }
}

///|
fn d_rearray(l : Value) -> Value raise {
  let l = cdr(l)
  let ar = car(l)
  let dims = mapcar(x => meval(x), cdr(l))
  if symval(q_d_use_fast_arrays).truthy() {
    set(ar, rearray_aux(ar, getvalue(ar), dims))
  } else {
    rearray_aux(ar, getvalue(ar), dims)
  }
}

///|
fn rearray_aux(ar : Value, val : Value, dims : Value) -> Value raise {
  if arrayp(val) {
    lispm_rearray(val, dims)
  } else if arrayp(get(ar, q_array)) {
    setf_get(ar, q_array, lispm_rearray(get(ar, q_array), dims))
  } else {
    let marray_sym = mget(ar, q_array)
    if marray_sym.truthy() {
      rearray_aux(marray_sym, Nil, dims) |> ignore
      ar
    } else {
      merr("rearray: argument is not an array: ~A", [ar])
    }
  }
}

///|
fn lispm_rearray(ar : Value, dims : Value) -> Value raise {
  if array_rank(ar) == length(dims) {
    adjust_array(ar, list_to_array(dims).map(d => to_int(d) + 1))
  } else {
    merr("rearray: arrays must have the same number of subscripts.", [])
  }
}
