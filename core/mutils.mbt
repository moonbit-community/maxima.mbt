// Port of src/mutils.lisp: general purpose Macsyma utilities.

///|
/// A MEMQ which works at all levels of a piece of list structure.
fn among(x : Value, l : Value) -> Value raise {
  match l {
    Nil => Nil
    Cons({ car: a, cdr: d }) => {
      let r = among(x, a)
      if r.truthy() {
        r
      } else {
        among(x, d)
      }
    }
    _ => lbool(eq(x, l))
  }
}

///|
/// Like ASSOC, but uses ALIKE1 as the comparison predicate rather
/// than EQUAL.
fn assol(item : Value, alist : Value) -> Value raise {
  if symbolp(item) {
    if alist.truthy() {
      assq(item, alist)
    } else {
      Nil
    }
  } else if integerp(item) {
    if alist.truthy() {
      assoc(item, alist)
    } else {
      Nil
    }
  } else {
    for pair in alist.iter() {
      if alike1(item, car(pair)).truthy() {
        return pair
      }
    }
    Nil
  }
}

///|
fn assolike(item : Value, alist : Value) -> Value raise {
  cdr(assol(item, alist))
}

///|
/// Searches for X in the list L, but uses ALIKE1 as the comparison predicate.
fn memalike(x : Value, l : Value) -> Value raise {
  if symbolp(x) {
    if l.truthy() {
      memq(x, l)
    } else {
      Nil
    }
  } else {
    let mut l = l
    while l is Cons({ car: a, cdr: d }) {
      if alike1(x, a).truthy() {
        return l
      }
      l = d
    }
    Nil
  }
}

///|
/// Return the first duplicate element of the list LIST, or NIL if there
/// are no duplicates present in LIST.
fn find_duplicate(list_ : Value, test_? : Value, key? : Value = Nil) -> Value raise {
  let mut seen : Value = Nil
  for e in list_.iter() {
    let i = if key.truthy() { funcall(key, [e]) } else { e }
    let found = match test_ {
      None => member(i, seen).truthy()
      Some(tst) => {
        let mut f = false
        for s in seen.iter() {
          if funcall(tst, [i, s]).truthy() {
            f = true
            break
          }
        }
        f
      }
    }
    if found {
      return e
    }
    seen = cons(i, seen)
  }
  Nil
}

///|
/// Does X or a subexpression match PREDICATE?
fn subexpression_matches_p(predicate : Value, x : Value) -> Value raise {
  let r = funcall(predicate, [x])
  if r.truthy() {
    return r
  }
  if x is Cons(_) {
    if specrepp(x).truthy() {
      subexpression_matches_p(predicate, specdisrep(x))
    } else {
      for arg in cdr(x).iter() {
        let r2 = subexpression_matches_p(predicate, arg)
        if r2.truthy() {
          return r2
        }
      }
      Nil
    }
  } else {
    Nil
  }
}

// ----------------------------------------------------------------------------
// Subscripted function utilities

///|
fn subfunmakes(fun : Value, subl : Value, argl : Value) -> Value raise {
  cons(list2(q_mqapply, q_simp), cons(cons(list3(fun, q_simp, q_array), subl), argl))
}

///|
fn subfunmake(fun : Value, subl : Value, argl : Value) -> Value raise {
  cons(list1(q_mqapply), cons(cons(list3(fun, q_simp, q_array), subl), argl))
}

///|
fn subfunname(expr : Value) -> Value raise {
  caaadr(expr)
}

///|
fn subfunsubs(expr : Value) -> Value raise {
  cdadr(expr)
}

///|
fn subfunargs(expr : Value) -> Value raise {
  cddr(expr)
}

// ----------------------------------------------------------------------------
// Modular arithmetic

///|
/// Normalizes the number N with respect to MODULUS,
/// returning a number in (-MODULUS/2, MODULUS/2].
fn normalized_modulus(n : Value) -> Value raise {
  let m = symval(q_modulus)
  let rem = num_mod(n, m)
  if num_le(num_mul(Fix(2L), rem), m) {
    rem
  } else {
    num_sub(rem, m)
  }
}

///|
fn cmod(n : Value) -> Value raise {
  if symval(q_modulus).truthy() {
    normalized_modulus(n)
  } else {
    n
  }
}

///|
fn cplus(a : Value, b : Value) -> Value raise {
  cmod(num_add(a, b))
}

///|
fn ctimes(a : Value, b : Value) -> Value raise {
  cmod(num_mul(a, b))
}

///|
fn cdifference(a : Value, b : Value) -> Value raise {
  cmod(num_sub(a, b))
}

// ----------------------------------------------------------------------------
// Matcher utilities

///|
fn matcherr() -> Value raise {
  throw_tag(q_match, Nil)
}

///|
fn kar(x : Value) -> Value raise {
  if atom(x) {
    matcherr()
  } else {
    car(x)
  }
}

///|
fn n_starkar(x : Value) -> Value raise {
  if !atom(x) {
    car(x)
  } else {
    Nil
  }
}

///|
fn kaar(x : Value) -> Value raise {
  kar(kar(x))
}

///|
fn kdr(x : Value) -> Value raise {
  if atom(x) {
    matcherr()
  } else {
    cdr(x)
  }
}

///|
fn nthkdr(x : Value, c : Value) -> Value raise {
  if zerop(c) {
    x
  } else {
    nthkdr(kdr(x), one_minus(c))
  }
}

// ----------------------------------------------------------------------------
// Widely used trivial predicates

///|
/// Determines if X is a Maxima rational form:  ((rat ...) a b)
fn ratnump(x : Value) -> Value raise {
  lbool(is_op(x, q_rat))
}

///|
/// Returns T if X is a Lisp number or if it is a Maxima rational
/// form or a bigfloat form, NIL otherwise
fn mnump(x : Value) -> Value raise {
  if numberp(x) {
    return t
  }
  match x {
    Cons({ car: Cons({ car: op, .. }), .. }) =>
      lbool(eq(op, q_rat) || eq(op, q_bigfloat))
    _ => Nil
  }
}

///|
/// Returns T if X, assumed to be a bigfloat, represents the value 1.
fn bigfloat_one_p(x : Value) -> Value raise {
  // Binary bigfloat ones are of the form '((BIGFLOAT [SIMP] <P>) 2^(<P>-1) 1).
  // Decimal bigfloat ones are of the form '((BIGFLOAT [SIMP] <P> DECIMAL) 1 0).
  let lastc = car(last(car(x)))
  if eq(q_decimal, lastc) {
    lbool(num_eq(Fix(1L), cadr(x)) && zerop(caddr(x)))
  } else {
    lbool(
      num_eq(Fix(1L), caddr(x)) &&
      num_eq(ash(Fix(1L), to_int(one_minus(lastc))), cadr(x)),
    )
  }
}

///|
/// Returns non-NIL if X is Lisp number or bfloat that is equal to 1.
fn onep1(x : Value) -> Value raise {
  if numberp(x) {
    lbool(num_eq(Fix(1L), x))
  } else if d_bfloatp(x).truthy() {
    bigfloat_one_p(x)
  } else {
    Nil
  }
}

///|
fn even(x : Value) -> Value raise {
  lbool(integerp(x) && !oddp(x))
}

///|
/// Is there a bfloat anywhere in X?
fn some_bfloatp(x : Value) -> Value raise {
  subexpression_matches_p(q_d_bfloatp, x)
}

///|
/// Is there a float anywhere in X?
fn some_floatp(x : Value) -> Value raise {
  subexpression_matches_p(q_floatp, x)
}

///|
fn mplusp(x : Value) -> Value raise {
  lbool(is_op(x, q_mplus))
}

///|
fn mtimesp(x : Value) -> Value raise {
  lbool(is_op(x, q_mtimes))
}

///|
fn mexptp(x : Value) -> Value raise {
  lbool(is_op(x, q_mexpt))
}

///|
fn mnctimesp(x : Value) -> Value raise {
  lbool(is_op(x, q_mnctimes))
}

///|
fn mncexptp(x : Value) -> Value raise {
  lbool(is_op(x, q_mncexpt))
}

///|
fn mlogp(x : Value) -> Value raise {
  lbool(is_op(x, q_p_log))
}

///|
fn mmminusp(x : Value) -> Value raise {
  lbool(is_op(x, q_mminus))
}

///|
/// Determines if X is negative if X is a Lisp number or a Maxima rat
/// form or bigfloat form
fn mnegp(x : Value) -> Value raise {
  if numberp(x) {
    lbool(minusp(x))
  } else if ratnump(x).truthy() || d_bfloatp(x).truthy() {
    lbool(minusp(cadr(x)))
  } else {
    Nil
  }
}

///|
fn mqapplyp(x : Value) -> Value raise {
  lbool(is_op(x, q_mqapply))
}

///|
fn mbagp(x : Value) -> Value raise {
  match x {
    Cons({ car: Cons({ car: op, .. }), .. }) =>
      lbool(eq(op, q_mequal) || eq(op, q_mlist) || eq(op, q_d_matrix))
    _ => Nil
  }
}

///|
fn mequalp(x : Value) -> Value raise {
  lbool(is_op(x, q_mequal))
}

///|
fn mxorlistp(x : Value) -> Value raise {
  match x {
    Cons({ car: Cons({ car: op, .. }), .. }) =>
      lbool(eq(op, q_mlist) || eq(op, q_d_matrix))
    _ => Nil
  }
}

///|
fn mxorlistp1(x : Value) -> Value raise {
  match x {
    Cons({ car: Cons({ car: op, .. }), .. }) =>
      if eq(op, q_d_matrix) {
        t
      } else if symval(q_d_listarith).truthy() {
        lbool(eq(op, q_mlist))
      } else {
        Nil
      }
    _ => Nil
  }
}

///|
fn sinp(e : Value) -> Value raise {
  lbool(is_op(e, q_p_sin))
}

///|
/// Return true iff the expression `e` is in general form and its operator
/// is `%cos`.
fn cosp(e : Value) -> Value raise {
  lbool(is_op(e, q_p_cos))
}
