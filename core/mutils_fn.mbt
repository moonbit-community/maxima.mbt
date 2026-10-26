// Port of src/mutils-fn.lisp: assoc, gensym and number predicates.

///|
/// Search for KEY in the left hand side of the elements of IELIST (each a
/// two-argument expression such as x=1, 2^3, [a,b]) and return the right hand
/// side of the first match, or DEFAULT.
fn d_assoc(key : Value, ielist : Value, default? : Value = Nil) -> Value raise {
  let elist = if listp(ielist) {
    margs(ielist)
  } else {
    merror(
      Str("assoc: second argument must be a nonatomic expression; found: ~:M"),
      list1(ielist),
    )
  }
  let mut found : Value = Nil
  for i in elist.iter() {
    if !(listp(i) && length(i) == 3) {
      merror(
        Str(
          "assoc: elements of the second argument must be an expression of two parts; found: ~:M",
        ),
        list1(i),
      )
      |> ignore
    }
    if alike1(key, second(i)).truthy() {
      found = i
      break
    }
  }
  if found.truthy() {
    third(found)
  } else {
    default
  }
}

///|
/// Return a Maxima gensym. Maxima gensyms are interned.
fn d_gensym(x? : Value = Nil) -> Value raise {
  match x {
    Nil => mutils_fn__intern_gensym("$g")
    Str(s) => mutils_fn__intern_gensym("$" + lstring(maybe_invert_string_case(Str(s))))
    Fix(n) if n >= 0L => {
      // (let ((*gensym-counter* x)) (gensym "$G"))
      sym("$g" + n.to_string())
    }
    Big(_) if !minusp(x) => sym("$g" + princ_to_string(x))
    _ =>
      merror(
        Str(
          "gensym: Argument must be a nonnegative integer or a string. Found: ~M",
        ),
        list1(x),
      )
  }
}

///|
/// `(intern (symbol-name (gensym prefix)))`
fn mutils_fn__intern_gensym(prefix : String) -> Value raise {
  sym(symbol_name(gensym(prefix~)))
}

///|
fn d_ratp(x : Value) -> Value raise {
  lbool(!atom(x) && consp(car(x)) && eq(caar(x), q_mrat))
}

///|
fn d_ratnump(x : Value) -> Value raise {
  if integerp(x) {
    return t
  }
  let r = ratnump(x)
  if r.truthy() {
    return r
  }
  lbool(
    d_ratp(x).truthy() &&
    member_eq(q_trunc, car(x)) is Nil &&
    integerp(cadr(x)) &&
    integerp(cddr(x)),
  )
}

///|
fn d_floatnump(x : Value) -> Value raise {
  if floatp(x) {
    return t
  }
  if d_ratp(x).truthy() && floatp(cadr(x)) {
    onep1(cddr(x))
  } else {
    Nil
  }
}

///|
/// Returns true if X is a Maxima rational, a float, or a bigfloat number
fn d_numberp(x : Value) -> Value raise {
  let r = d_ratnump(x)
  if r.truthy() {
    return r
  }
  let f = d_floatnump(x)
  if f.truthy() {
    return f
  }
  d_bfloatp(x)
}

///|
fn d_integerp(x : Value) -> Value raise {
  lbool(
    integerp(x) ||
    (
      d_ratp(x).truthy() &&
      member_eq(q_trunc, car(x)) is Nil &&
      integerp(cadr(x)) &&
      equal(cddr(x), Fix(1L))
    ),
  )
}

///|
/// The call to $INTEGERP checks for a CRE rational number with an integral
/// numerator and a unity denominator.
fn d_oddp(x : Value) -> Value raise {
  if integerp(x) {
    lbool(oddp(x))
  } else if atom(x) {
    Nil
  } else if d_integerp(x).truthy() {
    lbool(oddp(cadr(x)))
  } else {
    Nil
  }
}

///|
fn d_evenp(x : Value) -> Value raise {
  if integerp(x) {
    lbool(evenp(x))
  } else if atom(x) {
    Nil
  } else if d_integerp(x).truthy() {
    lbool(!oddp(cadr(x)))
  } else {
    Nil
  }
}

///|
fn d_taylorp(x : Value) -> Value raise {
  lbool(
    !atom(x) && eq(caar(x), q_mrat) && member_eq(q_trunc, cdar(x)).truthy(),
  )
}
