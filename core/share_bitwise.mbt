// Port of share/contrib/bitwise/bitwise.lisp (Volker van Nek, 2008):
// Maxima bit functions bit_not, bit_and, bit_xor, bit_or, bit_lsh, bit_rsh,
// bit_length, bit_onep.
//
// Comments use the following abbreviations:
// i,j,k : literal integers
// x,y,z : any expression
// di,dj,dk : declared integer
// de, do : declared even resp. odd

///|
/// `(meval `(($is) ,form))` is t
fn share_bitwise__is(form : Value) -> Bool raise {
  equal(t, meval(list2(list1(q_d_is), form)))
}

///|
/// `(equal t (meval `(($is) (($equal) ((,head) ,a) ,b))))` with the
/// bit_not header `head`.
fn share_bitwise__is_not_equal(
  head : Value,
  a : Value,
  b : Value,
) -> Bool raise {
  share_bitwise__is(list3(list1(q_d_equal), list2(head, a), b))
}

///|
fn share_bitwise__sort(l : Value) -> Value raise {
  sort_list(l, (a, b) => d_orderlessp(a, b).truthy())
}

///|
/// ERROR if at least one arg to bit_function is a non-integer constant,
/// string or Maxima list
fn badargcheck(a : Value, f : Value, n : Value) -> Value raise {
  if (!integerp(a) && d_constantp(a).truthy()) ||
    stringp(a) ||
    d_listp(a).truthy() {
    let s = format(Nil, "bad ~@[~:r~] argument to `~a': ~a", [
      n,
      f,
      d_sconcat(list1(a)),
    ])
    merror(Str("~m"), list1(s))
  } else {
    Nil
  }
}

///|
/// bitwise NOT
fn simp_bit_not(a : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  oneargcheck(a) |> ignore
  let a = simplifya(cadr(a), z)
  badargcheck(a, Str("bit_not"), Nil) |> ignore
  if integerp(a) {
    // bit_not(i) --> bitwise NOT i
    lognot(a)
  } else if listp(a) && listp(car(a)) && equal(caar(a), q_d_bit_not) {
    // bit_not(bit_not(x)) --> x
    cadr(a)
  } else if maxima_integerp(a).truthy() {
    // bit_not(di) -->  - di - 1
    meval(list3(list1(q_mplus), list2(list1(q_mminus), a), Fix(-1L)))
  } else {
    list2(list2(q_d_bit_not, q_simp), a)
  }
}

///|
/// Simplify and check the arguments of bit_and/bit_xor/bit_or; returns
/// the simplified arguments in reverse order (as pushed).
fn share_bitwise__check_args(
  args : Value,
  name : String,
  z : Value,
) -> Value raise {
  let mut acc : Value = Nil
  let mut n = 1L
  for a in args.iter() {
    badargcheck(a, Str(name), Fix(n)) |> ignore
    n = n + 1L
    acc = cons(simplifya(a, z), acc)
  }
  acc
}

///|
/// Separate the leading literal integers of the sorted `args`: returns
/// (ints, rest), with ints in reverse order.
fn share_bitwise__split_ints(args : Value) -> (Value, Value) {
  let mut args = args
  let mut ints : Value = Nil
  let mut a = car(args)
  while !(args is Nil || !integerp(a)) {
    ints = cons(a, ints)
    args = cdr(args)
    a = car(args)
  }
  (ints, args)
}

///|
/// (apply #'logand ints) etc.
fn share_bitwise__fold(
  f : (Value, Value) -> Value raise,
  init : Value,
  l : Value,
) -> Value raise {
  let mut acc = init
  for x in l.iter() {
    acc = f(acc, x)
  }
  acc
}

///|
/// bitwise AND
fn simp_bit_and(args : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  let mut args = cdr(args)
  // trivial case                                     bit_and() --> -1
  if args is Nil {
    return Fix(-1L)
  }
  // check and simplify the arguments
  let mut acc = share_bitwise__check_args(args, "bit_and", z)
  // separate the arguments into a list of literal integers and the rest
  // and remove duplicates                            bit_and(x,x,y) --> bit_and(x,y)
  args = sorted_remove_duplicates(share_bitwise__sort(acc))
  let (ints0, rest) = share_bitwise__split_ints(args)
  let mut ints = ints0
  args = rest
  // apply logand to the list of literal integers and return if possible
  let n = share_bitwise__fold((x, y) => logand(x, y), Fix(-1L), ints)
  if args is Nil {
    return n
  }
  if zerop(n) {
    return Fix(0L)
  } else if num_eq(n, Fix(-1L)) {
    ints = Nil
  } else {
    ints = list1(n)
  }
  // if twos complement occurs                        bit_and(x,bit_not(x),y) --> 0
  acc = Nil
  let mut a = car(args)
  while cdr(args).truthy() {
    let a0 = a
    if cdr(args)
      .iter()
      .any(b => share_bitwise__is_not_equal(list2(q_d_bit_not, q_simp), a0, b)) {
      return Fix(0L)
    }
    acc = cons(a, acc)
    args = cdr(args)
    a = car(args)
  }
  acc = cons(a, acc)
  // even or odd declared objects                     bit_and(1,de,y) --> 0
  if num_eq(n, Fix(1L)) &&
    acc.iter().any(b => d_featurep(b, q_d_even).truthy()) {
    return Fix(0L)
  }
  //                                                  bit_and(1,do) --> 1
  if num_eq(n, Fix(1L)) && acc.iter().all(b => d_featurep(b, q_d_odd).truthy()) {
    return Fix(1L)
  }
  // if one arg remains                               bit_and(x) --> x
  args = append(ints, reverse(acc))
  if length(args) == 1 {
    return car(args)
  }
  cons(list2(q_d_bit_and, q_simp), args)
}

///|
/// helper for $bit_xor
fn sorted_remove_pairs(l : Value) -> Value raise {
  let mut l = l
  let mut acc : Value = Nil
  while !(l is Nil) {
    let a = car(l)
    if cdr(l).truthy() && like(a, cadr(l)).truthy() {
      l = cddr(l)
    } else {
      acc = cons(a, acc)
      l = cdr(l)
    }
  }
  reverse(acc)
}

///|
/// helper for $bit_xor
fn remove_twos_complement(n : Value, l : Value) -> Value raise {
  let mut l = l
  let mut acc : Value = Nil
  while !(l is Nil) {
    let a = car(l)
    if share_bitwise__is_not_equal(list1(q_d_bit_not), a, n) {
      return append(reverse(acc), cdr(l))
    } else {
      acc = cons(a, acc)
      l = cdr(l)
    }
  }
  reverse(acc)
}

///|
/// The even/odd step of bit_xor and bit_or: replace the first element of
/// `acc` declared `feature` by `meval(mk(elem))` and recurse with `head`.
fn share_bitwise__recurse_on_declared(
  acc : Value,
  feature : Value,
  mk_term : (Value) -> Value,
  head : Value,
) -> Value? raise {
  let mut acc = acc
  let mut bcc : Value = Nil
  while !(acc is Nil) {
    let a = car(acc)
    if d_featurep(a, feature).truthy() {
      acc = append(reverse(bcc), append(list1(meval(mk_term(a))), cdr(acc)))
      return Some(meval(cons(list2(head, q_simp), acc)))
    }
    bcc = cons(a, bcc)
    acc = cdr(acc)
  }
  None
}

///|
/// bitwise EXCLUSIVE OR
fn simp_bit_xor(args : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  let mut args = cdr(args)
  // trivial case                                     bit_xor() --> 0
  if args is Nil {
    return Fix(0L)
  }
  // check and simplify the arguments
  let mut acc = share_bitwise__check_args(args, "bit_xor", z)
  // separate the arguments into a list of literal integers and the rest
  // and remove pairs                                 bit_xor(x,x,y,z) --> bit_xor(y,z)
  args = sorted_remove_pairs(share_bitwise__sort(acc))
  let (ints0, rest) = share_bitwise__split_ints(args)
  let mut ints = ints0
  args = rest
  // apply logxor to the list of integers and return if possible
  let mut n = share_bitwise__fold((x, y) => logxor(x, y), Fix(0L), ints)
  if args is Nil {
    return n
  }
  ints = list1(n)
  // if twos complement occurs                        bit_xor(x,bit_not(x),y,z) --> bit_xor(-1,y,z)
  acc = Nil
  let mut a = car(args)
  while cdr(args).truthy() {
    let a0 = a
    if cdr(args)
      .iter()
      .any(b => share_bitwise__is_not_equal(list1(q_d_bit_not), a0, b)) {
      rplacd(args, remove_twos_complement(a, cdr(args))) |> ignore
      n = num_sub(num_neg(n), Fix(1L))
      ints = list1(n)
    } else {
      acc = cons(a, acc)
    }
    args = cdr(args)
    a = car(args)
  }
  if a.truthy() {
    acc = cons(a, acc)
  }
  acc = reverse(acc)
  // n might have been changed in previous step; 0 occurs
  if zerop(n) {
    ints = Nil
  }
  // if there is an even or odd declared object       bit_xor(1,de,y) --> bit_xor(de+1,y) --> recurse
  if num_eq(n, Fix(1L)) &&
    acc.iter().any(b => d_featurep(b, q_d_even).truthy()) {
    match
      share_bitwise__recurse_on_declared(
        acc,
        q_d_even,
        a => list3(list1(q_mplus), a, Fix(1L)),
        q_d_bit_xor,
      ) {
      Some(r) => return r
      None => ()
    }
  }
  //                                                  bit_xor(1,do,y) --> bit_xor(do-1,y) --> recurse
  if num_eq(n, Fix(1L)) && acc.iter().any(b => d_featurep(b, q_d_odd).truthy()) {
    match
      share_bitwise__recurse_on_declared(
        acc,
        q_d_odd,
        a => list3(list1(q_mplus), a, list2(list1(q_mminus), Fix(1L))),
        q_d_bit_xor,
      ) {
      Some(r) => return r
      None => ()
    }
  }
  // -1 occurs                                        bit_xor(-1,x,y) --> bit_xor(bit_not(x),y) --> recurse
  if acc.truthy() && num_eq(n, Fix(-1L)) {
    return meval(
      cons(
        list2(q_d_bit_xor, q_simp),
        cons(meval(list2(list2(q_d_bit_not, q_simp), car(acc))), cdr(acc)),
      ),
    )
  }
  // if one arg remains                               bit_xor(x) --> x
  args = append(ints, acc)
  if length(args) == 1 {
    return car(args)
  }
  cons(list2(q_d_bit_xor, q_simp), args)
}

///|
/// bitwise OR
fn simp_bit_or(args : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  let mut args = cdr(args)
  // trivial case                                     bit_or() --> 0
  if args is Nil {
    return Fix(0L)
  }
  // check and simplify the arguments
  let mut acc = share_bitwise__check_args(args, "bit_or", z)
  // separate the arguments into a list of literal integers and the rest
  // and remove duplicates                            bit_or(x,x,y) --> bit_or(x,y)
  args = sorted_remove_duplicates(share_bitwise__sort(acc))
  let (ints0, rest) = share_bitwise__split_ints(args)
  let mut ints = ints0
  args = rest
  // apply logior to the list of literal integers and return if possible
  let n = share_bitwise__fold((x, y) => logior(x, y), Fix(0L), ints)
  if args is Nil {
    return n
  }
  if num_eq(n, Fix(-1L)) {
    return Fix(-1L)
  } else if zerop(n) {
    ints = Nil
  } else {
    ints = list1(n)
  }
  // if twos complement occurs                        bit_or(x,bit_not(x),y) --> -1
  acc = Nil
  let mut a = car(args)
  while cdr(args).truthy() {
    let a0 = a
    if cdr(args)
      .iter()
      .any(b => share_bitwise__is_not_equal(list2(q_d_bit_not, q_simp), a0, b)) {
      return Fix(-1L)
    }
    acc = cons(a, acc)
    args = cdr(args)
    a = car(args)
  }
  acc = cons(a, acc)
  // if there is an even or odd declared obj          bit_or(1,de,y) --> bit_or(de+1,y) --> recurse
  if num_eq(n, Fix(1L)) &&
    acc.iter().any(b => d_featurep(b, q_d_even).truthy()) {
    match
      share_bitwise__recurse_on_declared(
        acc,
        q_d_even,
        a => list3(list1(q_mplus), a, Fix(1L)),
        q_d_bit_or,
      ) {
      Some(r) => return r
      None => ()
    }
  }
  //                                                  bit_or(1,do,y) --> bit_or(do,y)
  if num_eq(n, Fix(1L)) && acc.iter().any(b => d_featurep(b, q_d_odd).truthy()) {
    ints = Nil
  }
  // if one arg remains                               bit_or(x) --> x
  args = append(ints, reverse(acc))
  if length(args) == 1 {
    return car(args)
  }
  cons(list2(q_d_bit_or, q_simp), args)
}

///|
/// bitwise LEFT SHIFT
fn simp_bit_lsh(e : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  twoargcheck(e) |> ignore
  let a = simplifya(cadr(e), z)
  let count = simplifya(caddr(e), z)
  badargcheck(a, Str("bit_lsh"), Fix(1L)) |> ignore
  badargcheck(count, Str("bit_lsh"), Fix(2L)) |> ignore
  if integerp(a) && integerp(count) {
    // bit_lsh(i,k) --> bitwise LEFT SHIFT i,k
    ash(a, to_int(count))
  } else if maxima_integerp(count).truthy() &&
    share_bitwise__is(list3(list1(q_mgeqp), count, Fix(0L))) {
    // bit_lsh(x,dk) --> 2^dk*x, where dk>=0
    meval(list3(list1(q_mtimes), list3(list1(q_mexpt), Fix(2L), count), a))
  } else {
    list3(list2(q_d_bit_lsh, q_simp), a, count)
  }
}

///|
/// bitwise RIGHT SHIFT
fn simp_bit_rsh(e : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  twoargcheck(e) |> ignore
  let a = simplifya(cadr(e), z)
  let count = simplifya(caddr(e), z)
  badargcheck(a, Str("bit_rsh"), Fix(1L)) |> ignore
  badargcheck(count, Str("bit_rsh"), Fix(2L)) |> ignore
  // bit_rsh(x,y) --> bit_lsh(x,-y). The Lisp passes the form (- count) to
  // meval, which evaluates count and applies CL `-` to it.
  let c = meval(count)
  if !numberp(c) {
    raise LispError::SimpleError("The value " + prin1_to_string(c) + " is not of type NUMBER")
  }
  meval(list3(list1(q_d_bit_lsh), a, num_neg(c)))
}

///|
/// ONE-BIT TEST
fn simp_bit_onep(e : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  twoargcheck(e) |> ignore
  let a = simplifya(cadr(e), z)
  let index = simplifya(caddr(e), z)
  badargcheck(a, Str("bit_onep"), Fix(1L)) |> ignore
  badargcheck(index, Str("bit_onep"), Fix(2L)) |> ignore
  // additional check: error if index<0
  if share_bitwise__is(list3(list1(q_mlessp), index, Fix(0L))) {
    merror(Str("second argument to `bit_onep' must be non-negative."), Nil)
    |> ignore
  }
  if integerp(a) && integerp(index) {
    // bit_onep(i,k) --> ONE-BIT TEST i,k, k>=0
    lbool(logbitp(to_int(index), a))
  } else if eql(Fix(0L), index) {
    if d_featurep(a, q_d_even).truthy() {
      // bit_onep(de,0) --> false
      Nil
    } else if d_featurep(a, q_d_odd).truthy() {
      // bit_onep(do,0) --> true
      t
    } else {
      Nil
    }
  } else if maxima_integerp(index).truthy() &&
    share_bitwise__is(list3(list1(q_mgeqp), index, Fix(0L))) &&
    share_bitwise__is(list3(list1(q_mgeqp), a, Fix(0L))) &&
    share_bitwise__is(
      list3(list1(q_mlessp), a, list3(list1(q_mexpt), Fix(2L), index)),
    ) {
    // bit_onep(x,dk) where 0<=x<2^dk, dk>=0 --> false
    Nil
  } else if listp(a) &&
    listp(car(a)) &&
    equal(caar(a), q_mexpt) &&
    // check if  y = dj*log(di)/log(2) :
    maxima_integerp(cadr(a)).truthy() &&
    maxima_integerp(caddr(a)).truthy() &&
    share_bitwise__is(
      list3(
        list1(q_d_equal),
        index,
        list3(
          list1(q_mquotient),
          list3(
            list1(q_mtimes),
            caddr(a),
            list2(list1(q_p_log), list2(list1(q_d_factor), cadr(a))),
          ),
          list2(list1(q_p_log), Fix(2L)),
        ),
      ),
    ) {
    // bit_onep(di^dj,y) where di^dj = 2^y --> true
    t
  } else {
    list3(list2(q_d_bit_onep, q_simp), a, index)
  }
}

///|
/// BIT LENGTH
fn simp_bit_length(a : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  oneargcheck(a) |> ignore
  let a = simplifya(cadr(a), z)
  badargcheck(a, Str("bit_length"), Nil) |> ignore
  // additional check: error if a<0
  if share_bitwise__is(list3(list1(q_mlessp), a, Fix(0L))) {
    merror(Str("argument to `bit_length' must be non-negative."), Nil)
    |> ignore
  }
  if integerp(a) {
    // bit_length(i) --> BIT LENGTH i
    int(integer_length(a))
  } else if listp(a) &&
    listp(car(a)) &&
    equal(caar(a), q_mexpt) &&
    maxima_integerp(cadr(a)).truthy() &&
    maxima_integerp(caddr(a)).truthy() &&
    share_bitwise__is(list3(list1(q_mgeqp), caddr(a), Fix(0L))) {
    // bit_length(2^dk) --> dk+1, bit_length(4^dk) --> 2*dk+1, etc.
    // where dk>=0
    // (The Lisp's test of the factor list is discarded: its value is
    // unused and the clause always returns here.)
    let fl = get_factor_list(cadr(a))
    let e = cadar(fl)
    meval(
      list3(list1(q_mplus), list3(list1(q_mtimes), e, caddr(a)), Fix(1L)),
    )
  } else {
    list2(list2(q_d_bit_length, q_simp), a)
  }
}

///|
fn init_share_bitwise() -> Unit raise {
  setf_get(q_d_bit_not, q_integer_valued, t) |> ignore
  setf_get(q_d_bit_and, q_integer_valued, t) |> ignore
  setf_get(q_d_bit_xor, q_integer_valued, t) |> ignore
  setf_get(q_d_bit_or, q_integer_valued, t) |> ignore
  setf_get(q_d_bit_lsh, q_integer_valued, t) |> ignore
  setf_get(q_d_bit_rsh, q_integer_valued, t) |> ignore
  setf_get(q_d_bit_length, q_integer_valued, t) |> ignore
  putprop(q_d_bit_not, q_simp_bit_not, q_operators) |> ignore
  putprop(q_d_bit_and, q_simp_bit_and, q_operators) |> ignore
  putprop(q_d_bit_xor, q_simp_bit_xor, q_operators) |> ignore
  putprop(q_d_bit_or, q_simp_bit_or, q_operators) |> ignore
  putprop(q_d_bit_lsh, q_simp_bit_lsh, q_operators) |> ignore
  putprop(q_d_bit_rsh, q_simp_bit_rsh, q_operators) |> ignore
  putprop(q_d_bit_onep, q_simp_bit_onep, q_operators) |> ignore
  putprop(q_d_bit_length, q_simp_bit_length, q_operators) |> ignore
}
