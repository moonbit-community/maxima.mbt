// Port of share/algebra/charsets/charsets_set.lisp: support for Maxima
// sets (Barton Willis), used by the charsets package.

///|
fn charsets_set__elem_eq(x : Value, y : Value) -> Bool raise {
  d_charsets_elem_equalp(x, y).truthy()
}

// Use the predicate canonlt to order the elements of a set. The default is
// $charsets_unorderedp. The predicate $charsets_unorderedp always returns
// true; when canonlt is its default value, sets are never sorted. Other
// choices for $charsets_canonlt include $ordergreatp and $orderlessp.

///|
fn d_charsets_unorderedp(_a : Value, _b : Value) -> Value raise {
  t
}

// When $charsets_set_elements_can_be_sets is true (the default), set
// elements that are lists are treated as sets; otherwise set elements that
// are lists are treated as lists.

///|
/// For non-lists x and y, equalp(x,y) returns is(ratsimp(x-y)=0). Signal an
/// error if either x or y is a list.
fn d_charsets_equalp(x : Value, y : Value) -> Value raise {
  if d_listp(x).truthy() || d_listp(y).truthy() {
    merr("Both arguments to `equalp' must be non-lists.", [])
  } else {
    d_charsets_xequalp(x, y)
  }
}

///|
/// If you are certain that x and y are not lists, you might call (at Maxima
/// level) ?xequalp instead of equalp.
fn d_charsets_xequalp(x : Value, y : Value) -> Value raise {
  like(Fix(0L), d_ratsimp(add_star(list2(x, n_starmminus(y))), Nil))
}

///|
/// If x and y are not lists, returns equalp(x,y). If x and y are both
/// lists, return setequality(x,y) if set_elements_can_be_sets; otherwise
/// return equalp(x[1],y[1]) and equalp(x[2],y[2]) and .... Finally, if
/// exactly one of x or y is a list, return false.
fn d_charsets_elem_equalp(x : Value, y : Value) -> Value raise {
  if d_listp(x).truthy() && d_listp(y).truthy() {
    if symval(q_d_charsets_set_elements_can_be_sets).truthy() {
      d_charsets_setequality(x, y)
    } else if d_charsets_emptyp(x).truthy() && d_charsets_emptyp(y).truthy() {
      t
    } else if num_eq(d_length(x), d_length(y)) &&
      d_charsets_elem_equalp(d_first(x), d_first(y)).truthy() {
      d_charsets_elem_equalp(d_rest(x), d_rest(y))
    } else {
      Nil
    }
  } else if d_listp(x).truthy() || d_listp(y).truthy() {
    Nil
  } else {
    d_charsets_xequalp(x, y)
  }
}

///|
/// Adjoin x to the Maxima list a; use equalp for the equality test.
fn d_charsets_adjoin2(x : Value, a : Value) -> Value raise {
  if d_listp(a).truthy() {
    let l = margs(a)
    cons(
      list1(q_mlist),
      if member_if_test(x, l, charsets_set__elem_eq) is Nil {
        cons(x, l)
      } else {
        l
      },
    )
  } else {
    merr("The second argument to `charsets_adjoin2' must be a list", [])
  }
}

///|
/// Setify removes duplicates from a Maxima list and sorts the list using
/// the partial ordering function canonlt.
fn d_charsets_setify(a : Value) -> Value raise {
  if d_listp(a).truthy() {
    charsets_mysort(
      cons(
        list1(q_mlist),
        remove_duplicates(margs(a), pred2=charsets_set__elem_eq),
      ),
    )
  } else {
    merr("The argument to `setify' must be a list.", [])
  }
}

///|
/// When $charsets_canonlt is $charsets_unorderedp, don't sort; otherwise
/// sort the list using the predicate $charsets_canonlt.
fn charsets_mysort(a : Value) -> Value raise {
  if eq(symval(q_d_charsets_canonlt), q_d_charsets_unorderedp) {
    a
  } else {
    d_sort(a, f=symval(q_d_charsets_canonlt))
  }
}

///|
/// union(a1,a2,...an) forms the union of the sets a1,a2,...an.
fn d_charsets_union(a : Value) -> Value raise {
  if memq(Nil, mapcar(x => d_listp(x), a)).truthy() {
    merr("Each argument to `union' must be a list.", [])
  } else {
    cons(
      list1(q_mlist),
      remove_duplicates(
        append_n(a.iter().map(x => cdr(x)).collect()),
        pred2=charsets_set__elem_eq,
      ),
    )
  }
}

///|
/// Remove elements of b from a.
fn d_charsets_setdifference(a : Value, b : Value) -> Value raise {
  if d_listp(a).truthy() && d_listp(b).truthy() {
    cons(
      list1(q_mlist),
      set_difference(margs(a), margs(b), pred2=charsets_set__elem_eq),
    )
  } else {
    merr("Both arguments to `setdifference' must be lists.", [])
  }
}

///|
/// Return the intersection of lists a and b.
fn d_charsets_intersection(a : Value) -> Value raise {
  let a = margs(a)
  if memq(Nil, mapcar(x => d_listp(x), a)).truthy() {
    merr("Each argument to `intersection' must be a list.", [])
  } else {
    let a = mapcar(x => margs(x), a)
    cons(
      list1(q_mlist),
      reduce((x, y) => intersection(x, y, pred2=charsets_set__elem_eq), a),
    )
  }
}

///|
/// Return true iff a is a subset of b.
fn d_charsets_subsetp(a : Value, b : Value) -> Value raise {
  if d_listp(a).truthy() && d_listp(b).truthy() {
    charsets_xsubsetp(margs(a), b)
  } else {
    merr("Both arguments to `subsetp' must be lists.", [])
  }
}

///|
/// True iff each element of the Lisp list a is a member of the Maxima list
/// b. The empty set is a subset of every set.
fn charsets_xsubsetp(a : Value, b : Value) -> Value raise {
  if a is Nil {
    t
  } else if d_charsets_elementp(car(a), b).truthy() {
    charsets_xsubsetp(cdr(a), b)
  } else {
    Nil
  }
}

///|
/// Return true iff a is a subset of b and b is a subset of a; return false
/// if a or b are not lists.
fn d_charsets_setequality(a : Value, b : Value) -> Value raise {
  if d_listp(a).truthy() && d_listp(b).truthy() {
    lbool(
      d_charsets_subsetp(a, b).truthy() && d_charsets_subsetp(b, a).truthy(),
    )
  } else {
    Nil
  }
}

///|
/// Return true iff x as an element of the list a.
fn d_charsets_elementp(x : Value, a : Value) -> Value raise {
  if d_listp(a).truthy() {
    if d_listp(x).truthy() {
      if symval(q_d_charsets_set_elements_can_be_sets).truthy() {
        lbool(
          member_if_test(x, margs(a), (u, v) => d_charsets_setequality(u, v).truthy()).truthy(),
        )
      } else {
        lbool(member_if_test(x, margs(a), charsets_set__elem_eq).truthy())
      }
    } else {
      lbool(member_if_test(x, margs(a), charsets_set__elem_eq).truthy())
    }
  } else {
    Nil
  }
}

///|
/// Return true if e is an empty Maxima list; otherwise, signal an error.
fn d_charsets_emptyp(e : Value) -> Value raise {
  if d_listp(e).truthy() {
    like(e, list1(list1(q_mlist)))
  } else {
    merr("Argument to `emptyp' must be a list.", [])
  }
}

///|
/// Return an n element Maxima list [e,e,e,...e].
fn d_charsets_dupe(e : Value, n : Value) -> Value raise {
  if integerp(n) && num_gt(n, Fix(-1L)) {
    let c = Collector::new()
    for _ in 0..<to_int(n) {
      c.add(e)
    }
    cons(list1(q_mlist), c.result())
  } else {
    merr("Second argument to `dupe' must be a nonnegative integer.", [])
  }
}

///|
/// Return true if and only if the lists a and b are disjoint.
fn d_charsets_disjointp(a : Value, b : Value) -> Value raise {
  if d_listp(a).truthy() && d_listp(b).truthy() {
    lbool(
      intersection(margs(a), margs(b), pred2=charsets_set__elem_eq) is Nil,
    )
  } else {
    merr("Both arguments to `disjointp' must be lists.", [])
  }
}

///|
/// Return the union of a - b and b - a.
fn d_charsets_symmdifference(a : Value, b : Value) -> Value raise {
  if d_listp(a).truthy() && d_listp(b).truthy() {
    mfuncall(
      q_d_charsets_union,
      list2(d_charsets_setdifference(a, b), d_charsets_setdifference(b, a)),
    )
  } else {
    merr("Both arguments to `symmdifference' must be lists.", [])
  }
}

///|
/// Return a list of the elements in b that are not in a.
fn d_charsets_complement(a : Value, b : Value) -> Value raise {
  if d_listp(a).truthy() && d_listp(b).truthy() {
    d_charsets_setdifference(b, a)
  } else {
    merr("Both arguments to `complement' must be lists.", [])
  }
}

///|
/// True iff the argument is a Maxima list without duplicate elements.
fn d_charsets_setp(a : Value) -> Value raise {
  if d_listp(a).truthy() {
    charsets_setp(margs(a))
  } else {
    Nil
  }
}

///|
fn charsets_setp(a : Value) -> Value raise {
  if a is Nil {
    t
  } else if charsets_setp(cdr(a)).truthy() {
    lbool(member_if_test(car(a), cdr(a), charsets_set__elem_eq) is Nil)
  } else {
    Nil
  }
}

///|
/// Return the set of all subsets of a.
fn d_charsets_powerset(a : Value) -> Value raise {
  if d_listp(a).truthy() {
    let a = d_charsets_setify(a)
    cons(
      list1(q_mlist),
      mapcar(x => cons(list1(q_mlist), x), charsets_powerset(margs(a))),
    )
  } else {
    merr("Argument to `charsets_powerset' must be a list.", [])
  }
}

///|
fn charsets_powerset(a : Value) -> Value raise {
  if a is Nil {
    list1(Nil)
  } else {
    let x = car(a)
    let b = charsets_powerset(cdr(a))
    append(b, mapcar(u => cons(x, u), b))
  }
}

///|
/// Return the set of all subsets of a that have exactly n elements.
fn d_charsets_subpowerset(a : Value, n : Value) -> Value raise {
  if d_listp(a).truthy() {
    let a = d_charsets_setify(a)
    if integerp(n) && num_gt(n, Fix(-1L)) {
      cons(
        list1(q_mlist),
        mapcar(x => cons(list1(q_mlist), x), charsets_subpowerset(margs(a), n)),
      )
    } else {
      merr("Second argument to SUBPOWERSET must\nbe a nonnegative integer.", [])
    }
  } else {
    merr("First argument to `charsets_subpowerset' must be a list.", [])
  }
}

///|
fn charsets_subpowerset(a : Value, n : Value) -> Value raise {
  if num_lt(n, Fix(1L)) || a is Nil {
    Nil
  } else if num_eq(n, Fix(1L)) {
    mapcar(x => list1(x), a)
  } else {
    let x = car(a)
    let b = charsets_subpowerset(cdr(a), num_sub(n, Fix(1L)))
    append(charsets_subpowerset(cdr(a), n), mapcar(u => cons(x, u), b))
  }
}
