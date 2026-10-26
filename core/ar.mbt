// Port of src/ar.lisp: Maxima array objects (Lisp arrays, hash tables and
// MGENARRAY structures).
//
// (defstruct mgenarray aref aset type null generator content) is a
// `make_struct("mgenarray", [...])` with slots 0..5 in that order:
// aref aset type null generator content.

///|
fn ar__make_mgenarray(
  type_ : Value,
  null_ : Value,
  generator : Value,
  content : Value,
) -> Value {
  make_struct("mgenarray", [Nil, Nil, type_, null_, generator, content])
}

///|
fn ar__mgenarray_type(x : Value) -> Value raise {
  struct_ref(x, 2)
}

///|
fn ar__mgenarray_null(x : Value) -> Value raise {
  struct_ref(x, 3)
}

///|
fn ar__mgenarray_generator(x : Value) -> Value raise {
  struct_ref(x, 4)
}

///|
fn ar__mgenarray_content(x : Value) -> Value raise {
  struct_ref(x, 5)
}

///|
/// (deftype marray () `(or cl:array hash-table mgenarray))
fn marrayp(x : Value) -> Value raise {
  lbool(arrayp(x) || hash_table_p(x) || struct_typep(x, "mgenarray"))
}

///|
fn marray_type(x : Value) -> Value raise {
  if arrayp(x) {
    q_array
  } else if hash_table_p(x) {
    q_hash_table
  } else if struct_typep(x, "mgenarray") {
    ar__mgenarray_type(x)
  } else {
    Nil
  }
}

///|
fn ar__dims(l : Value) -> Array[Int] raise {
  list_to_array(l).map(d => to_int(d))
}

///|
fn d_make_array(type_ : Value, diml : Value) -> Value raise {
  let ltype = if eq(type_, q_d_float) || eq(type_, q_d_flonum) {
    q_flonum
  } else if eq(type_, q_d_fixnum) {
    q_fixnum
  } else {
    Nil
  }
  // Check the dimensions. No check for number of dimensions. For a
  // functional array the list of dimensions starts at the third element.
  let to_check = if eq(type_, q_d_functional) { cddr(diml) } else { diml }
  if !every(u => fixnump(u), to_check) {
    merror(
      Str("make_array: dimensions must be integers; found ~M"),
      list1(cons(list1(q_mlist), diml)),
    )
    |> ignore
  }
  if ltype is Nil {
    if eq(type_, q_d_any) {
      make_array(ar__dims(diml), initial=Nil)
    } else if eq(type_, q_d_hashed) {
      make_equal_hash_table(cdr(diml))
    } else if eq(type_, q_d_functional) {
      // MAKE_ARRAY('FUNCTIONAL, LAMBDA(...), 'ARRAY_TYPE, ...)
      // This is a memoizing array.
      if !(length(diml) > 1) {
        merror(
          Str(
            "make_array: not enough arguments for functional array specification.",
          ),
          Nil,
        )
        |> ignore
      }
      let ar = d_make_array(cadr(diml), cddr(diml))
      let atype = cadr(diml)
      let the_null = if eq(atype, q_d_fixnum) {
        let n = symval(q_fixunbound)
        fillarray(ar, list1(n)) |> ignore
        n
      } else if eq(atype, q_d_flonum) || eq(atype, q_d_float) {
        let n = symval(q_flounbound)
        fillarray(ar, list1(n)) |> ignore
        n
      } else if eq(atype, q_d_any) {
        let n = symval(q_munbound)
        fillarray(ar, list1(n)) |> ignore
        n
      } else {
        // Nothing to do for hashed arrays.
        Nil
      }
      ar__make_mgenarray(q_d_functional, the_null, car(diml), ar)
    } else {
      merror(Str("make_array: array type ~M not recognized."), list1(type_))
    }
  } else {
    make_array(
      ar__dims(diml),
      initial=if eq(ltype, q_fixnum) { Fix(0L) } else { Flo(0.0) },
    )
  }
}

///|
fn dimension_array_object(form : Value, result : Value) -> Value raise {
  let mtype = marray_type(form)
  if eq(mtype, q_d_functional) {
    dimension_array_object(ar__mgenarray_content(form), result)
  } else {
    dimension_atom(format(Nil, "{Lisp Array: ~A}", [form]), result)
  }
}

///|
fn msize_array_object(x : Value, l : Value, r : Value) -> Value raise {
  let mtype = marray_type(x)
  if eq(mtype, q_d_functional) {
    msize_array_object(ar__mgenarray_content(x), l, r)
  } else {
    msize_atom(format(Nil, "{Lisp Array: ~A}", [x]), l, r)
  }
}

///|
fn marray_check(a : Value) -> Value raise {
  if marrayp(a).truthy() {
    let ty = marray_type(a)
    if eq(ty, q_d_fixnum) || eq(ty, q_d_float) {
      a
    } else if eq(ty, q_d_any) {
      ar__mgenarray_content(a)
    } else if eq(ty, q_d_hashed) || eq(ty, q_d_functional) {
      // BUG: It does have a number of dimensions! Gosh. -GJC
      merror(
        Str("MARRAY-CHECK: hashed array ~M has no dimension data."),
        list1(a),
      )
    } else {
      marray_type_unknown(a)
    }
  } else {
    merror(Str("MARRAY-CHECK: not an array: ~M"), list1(a))
  }
}

///|
fn d_array_dimension_n(n : Value, a : Value) -> Value raise {
  int(array_dimension(marray_check(a), to_int(n)))
}

///|
fn marray_type_unknown(x : Value) -> Value raise {
  merror(Str("MARRAY-TYPE-UNKNOWN: array type ~S not recognized."), list1(x))
}

///|
fn ar__check_indices(ind1 : Value, inds : Value) -> Array[Int] raise {
  if !(integerp(ind1) && every(x => integerp(x), inds)) {
    bad_index_error(cons(ind1, inds)) |> ignore
  }
  ar__dims(cons(ind1, inds))
}

///|
fn ar__hash_key(ind1 : Value, inds : Value) -> Value {
  if inds.truthy() {
    cons(ind1, inds)
  } else {
    ind1
  }
}

///|
fn marrayref_gensub(aarray : Value, ind1 : Value, inds : Value) -> Value raise {
  let ty = marray_type(aarray)
  if eq(ty, q_array) {
    aref(aarray, ar__check_indices(ind1, inds))
  } else if eq(ty, q_hash_table) {
    gethash(ar__hash_key(ind1, inds), aarray)
  } else if eq(ty, q_d_functional) {
    // special variable changes behavior of hashed-array referencing
    // functions in case of not finding an element.
    let value = with_special(q_evarrp, t, fn() raise {
      catch_tag(q_evarrp, fn() raise {
        marrayref_gensub(ar__mgenarray_content(aarray), ind1, inds)
      })
    })
    if equal(value, ar__mgenarray_null(aarray)) {
      marrayset_gensub(
        mfuncall(ar__mgenarray_generator(aarray), cons(ind1, inds)),
        ar__mgenarray_content(aarray),
        ind1,
        inds,
      )
    } else {
      value
    }
  } else {
    marray_type_unknown(aarray)
  }
}

///|
/// INDICES is a Lisp list, not a Maxima list.
fn bad_index_error(indices : Value) -> Value raise {
  let m_indices = cons(list1(q_mlist), indices)
  if every(x => specrepp(x).truthy() || integerp(x), indices) {
    merror(
      Str(
        "array: indices cannot be special expressions (CRE, Taylor or Poisson); found: ~M",
      ),
      list1(m_indices),
    )
  } else if every(x => d_mapatom(x).truthy() || integerp(x), indices) {
    merror(
      Str("array: indices cannot be plain or subscripted symbols; found: ~M"),
      list1(m_indices),
    )
  } else {
    merror(
      Str("array: indices must be literal integers; found: ~M"),
      list1(m_indices),
    )
  }
}

///|
fn marrayset_gensub(
  val : Value,
  aarray : Value,
  ind1 : Value,
  inds : Value,
) -> Value raise {
  let ty = marray_type(aarray)
  if eq(ty, q_array) {
    aset(aarray, ar__check_indices(ind1, inds), val)
  } else if eq(ty, q_hash_table) {
    sethash(ar__hash_key(ind1, inds), aarray, val)
  } else if eq(ty, q_d_functional) {
    marrayset_gensub(val, ar__mgenarray_content(aarray), ind1, inds)
  } else {
    marray_type_unknown(aarray)
  }
}

///|
/// Extensions to MEVAL.
fn meval1_extend(form : Value) -> Value raise {
  let l = mevalargs(cdr(form))
  marrayref_gensub(caar(form), car(l), cdr(l))
}

///|
fn arrstore_extend(a : Value, l : Value, r : Value) -> Value raise {
  marrayset_gensub(r, a, car(l), cdr(l))
}
