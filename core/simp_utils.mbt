// Port of src/simp-utils.lisp: common utilities needed by both simp.lisp
// and mutils.lisp (ALIKE1, LIKE, SPECREPCHECK, ...).

///|
fn delsimp(e : Value) -> Value raise {
  remove(q_simp, e)
}

///|
/// Returns true if X is a bigfloat.
fn d_bfloatp(x : Value) -> Value raise {
  match x {
    Cons({ car: Cons({ car: op, .. }), .. }) => lbool(eq(op, q_bigfloat))
    _ => Nil
  }
}

///|
/// Returns non-NIL if X is Lisp number or bfloat that is equal to 0.
fn zerop1(x : Value) -> Value raise {
  if numberp(x) {
    lbool(zerop(x))
  } else if d_bfloatp(x).truthy() {
    lbool(num_eq(Fix(0L), cadr(x)))
  } else {
    Nil
  }
}

///|
fn ratdisrep(e : Value) -> Value raise {
  simplifya(d_ratdisrep(e), Nil)
}

///|
fn specdisrep(e : Value) -> Value raise {
  if eq(caar(e), q_mrat) {
    ratdisrep(e)
  } else {
    d_outofpois(e)
  }
}

///|
fn specrepcheck(e : Value) -> Value raise {
  if specrepp(e).truthy() {
    specdisrep(e)
  } else {
    e
  }
}

///|
/// Compares two Macsyma expressions ignoring SIMP flags and all other
/// items in the header except for the ARRAY flag.
fn like(x : Value, y : Value) -> Value raise {
  alike1(specrepcheck(x), specrepcheck(y))
}

///|
/// macro MEMQARR: `(if (member-eq 'array l) t)`
fn memqarr(l : Value) -> Value raise {
  if member_eq(q_array, l).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn lisp_vector_alike1(x : Value, y : Value) -> Value raise {
  let lx = length(x)
  if lx == length(y) {
    lisp_array_elements_alike1(x, y, int(lx))
  } else {
    Nil
  }
}

///|
fn lisp_array_alike1(x : Value, y : Value) -> Value raise {
  if equal(array_dimensions(x), array_dimensions(y)) {
    lisp_array_elements_alike1(x, y, int(array_total_size(x)))
  } else {
    Nil
  }
}

///|
/// `(row-major-aref x i)`
fn simp_utils__row_major_aref(x : Value, i : Int) -> Value raise {
  match x {
    Vec(a) => a.data[i]
    Str(s) => Char(char_at(s, i))
    _ => raise LispError::SimpleError("row-major-aref: not an array")
  }
}

///|
fn lisp_array_elements_alike1(x : Value, y : Value, n : Value) -> Value raise {
  let n = to_int(n)
  for i in 0..<n {
    if !alike1(
        simp_utils__row_major_aref(x, i),
        simp_utils__row_major_aref(y, i),
      ).truthy() {
      return Nil
    }
  }
  t
}

///|
fn alike1(x : Value, y : Value) -> Value raise {
  // Clauses are ordered based on frequency of the case
  // cons, integer, and symbol are very common
  // everything else is rare
  if eq(x, y) {
    return t
  }
  match x {
    Cons({ car: car_x, cdr: cdr_x }) =>
      match (car_x, y) {
        (Cons({ car: op, cdr: cdar_x }), Cons({ car: Cons(_) as car_y, cdr: cdr_y })) if eq(op, car(car_y)) =>
          if eq(op, q_mrat) {
            like(x, y)
          } else if eq(op, q_mpois) {
            lbool(equal(cdr_x, cdr_y))
          } else if eq(op, q_bigfloat) {
            // Bigfloats need special treatment because their precision
            // and an optional DECIMAL flag are stored in the CAR,
            // which would otherwise be ignored.
            // ((BIGFLOAT [SIMP] <PRECISION> [DECIMAL]) <MANTISSA> <EXPONENT>)
            if num_eq(cadr(x), cadr(y)) && num_eq(caddr(x), caddr(y)) {
              if eq(car_x, car_y) {
                t
              } else {
                let rest_x = if eq(q_simp, cadar(x)) { cddar(x) } else { cdar(x) }
                let rest_y = if eq(q_simp, cadar(y)) { cddar(y) } else { cdar(y) }
                lbool(
                  num_eq(car(rest_x), car(rest_y)) &&
                  eq(cadr(rest_x), cadr(rest_y)),
                )
              }
            } else {
              Nil
            }
          } else if eq(car_x, car_y) ||
            eq(memqarr(cdar_x), memqarr(cdr(car_y))) {
            // General case: First check for CARs being EQ (see EQTEST).
            // If not, just check whether both have or don't have the ARRAY flag.
            alike(cdr_x, cdr_y)
          } else {
            Nil
          }
        // (foo) and (foo) test non-alike because the car's aren't standard
        _ => Nil
      }
    _ =>
      if y is Cons(_) {
        Nil
      } else if symbolp(x) || symbolp(y) {
        Nil
      } else if integerp(x) {
        lbool(integerp(y) && num_eq(x, y))
      } else if floatp(x) {
        // uncommon cases from here down
        lbool(floatp(y) && num_eq(x, y))
      } else if x is Str(sx) {
        lbool(y is Str(sy) && sx == sy)
      } else if vectorp(x) {
        lbool(vectorp(y) && lisp_vector_alike1(x, y).truthy())
      } else if arrayp(x) {
        lbool(arrayp(y) && lisp_array_alike1(x, y).truthy())
      } else {
        Nil
      }
  }
}

///|
/// Maps ALIKE1 down two lists.
fn alike(x : Value, y : Value) -> Value raise {
  let mut x = x
  let mut y = y
  while true {
    match x {
      Cons({ car: xa, cdr: xd }) => {
        match y {
          Cons({ car: ya, cdr: yd }) => {
            if !alike1(xa, ya).truthy() {
              return Nil
            }
            x = xd
            y = yd
          }
          _ => return Nil
        }
      }
      _ => return lbool(equal(x, y))
    }
  }
  Nil
}

///|
/// Check if EXP is a multiple of VAR.
fn multiplep(exp_ : Value, var_ : Value) -> Value raise {
  if zerop1(exp_).truthy() {
    return Nil
  }
  let c = coeff(exp_, var_, Fix(1L))
  if zerop1(c).truthy() {
    return Nil
  }
  zerop1(sub(exp_, mul2(var_, c)))
}

///|
fn margs(form : Value) -> Value raise {
  if eq(caar(form), q_mqapply) {
    cddr(form)
  } else {
    cdr(form)
  }
}

///|
fn atomchk(e : Value, fun : Value, n2ndp : Value) -> Value raise {
  if atom(e) || eq(caar(e), q_bigfloat) {
    merr(
      "~:M: ~Margument must be a non-atomic expression; found ~M",
      [fun, if n2ndp.truthy() { Str("2nd ") } else { Str("") }, e],
    )
  } else {
    Nil
  }
}

///|
fn d_member(x : Value, e : Value) -> Value raise {
  atomchk(e, q_d_member, t) |> ignore
  let x = specrepcheck(x)
  for i in margs(e).iter() {
    if alike1(x, specrepcheck(i)).truthy() {
      return t
    }
  }
  Nil
}
