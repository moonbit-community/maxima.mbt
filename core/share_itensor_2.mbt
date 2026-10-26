// Port of share/tensor/itensor.lisp, part 2: ISHOW, the redefined DERIV
// and SDIFF (indexed objects acquire derivative indices; differentiation of
// tensors with respect to tensors), and the indicial derivative IDIFF.

///|
fn d_ishow(f : Value) -> Value raise {
  makelabel(symval(q_d_linechar)) |> ignore
  if symval(q_d_dispflag).truthy() {
    displa(
      list3(
        list1(q_mlabel),
        symval(q_ear_linelabel),
        ishow(specrepcheck(derat(f))),
      ),
    )
    |> ignore
  }
  set(symval(q_ear_linelabel), f)
}

///|
/// Displays P([L1],[L2],I1,I2,...) by making the elements of L2 into a
/// single atom which serves as the exponent and the elements of L1 and
/// I1,I2,... into a single atom with a comma in between which serves as the
/// subscript.
fn ishow(f : Value) -> Value raise {
  // FOOBAR (special) initialized to NIL
  let b = bind(q_foobar, Nil)
  defer unbind(b)
  if atom(f) {
    f
  } else if rpobj(f).truthy() {
    // If an indexed object ...
    set(
      q_foobar,
      if covi(f).truthy() || cdddr(f).truthy() {
        // If covariant or derivative indices
        cons(
          list2(caar(f), q_array),
          list1(maknam(cons(q_d_, splice(covi(f), cdddr(f))))),
        )
      } else {
        caar(f)
      },
    )
    |> ignore
    if conti(f).truthy() {
      // If contravariant indices
      list3(
        list2(q_mexpt, q_simp),
        symval(q_foobar),
        maknam(cons(q_d_, splice(conti(f), Nil))),
      )
    } else {
      symval(q_foobar)
    }
  } else {
    // Map onto subparts of F
    cons(car(f), mapcar(x => ishow(x), cdr(f)))
  }
}

///|
fn splice(l1 : Value, l2 : Value) -> Value raise {
  if l2.truthy() {
    let mut l2 = cons(q_op_cm, splice1(l2))
    if l1.truthy() {
      l2 = nconc(splice1(l1), l2)
    }
    l2
  } else {
    splice1(l1)
  }
}

///|
fn splice1(l : Value) -> Value raise {
  if cdr(l) is Nil {
    splice2(car(l))
  } else {
    nconc(splice2(car(l)), cons(q_op_sp, splice1(cdr(l))))
  }
}

///|
fn splice2(x : Value) -> Value raise {
  if fixnump(x) {
    explode(x)
  } else {
    cdr(explodec(x))
  }
}

///|
/// The itensor redefinition of DERIV (comm.lisp): numeric differentiation
/// indices are mapped to coordinates through $VECT_COORDS.
fn share_itensor__deriv(e : Value) -> Value raise {
  let mut e = e
  if cdr(e) is Nil {
    return stotaldiff(car(e))
  } else if cddr(e) is Nil {
    nconc(e, list1(Fix(1L))) |> ignore
  }
  let mut exp = car(e)
  e = append(e, Nil)
  let mut z = e
  let mut count : Value = Nil
  let mut v : Value = Nil
  // states: 0 loop, 1 loop2, 2 doit, 3 loop1, 4 noun
  let mut state = 0
  while true {
    match state {
      0 => {
        // DERIVLIST is set by $EV
        let dl = symval(q_derivlist)
        if dl is Nil || member_equal(cadr(z), dl).truthy() {
          state = 2
        } else {
          z = cdr(z)
          state = 1
        }
      }
      1 =>
        if cdr(z).truthy() {
          state = 0
        } else if cdr(e) is Nil {
          return exp
        } else {
          state = 4
        }
      2 => {
        if cddr(z) is Nil {
          merr("Wrong number of args to DERIVATIVE", []) |> ignore
        }
        count = caddr(z)
        if !fixnump(count) {
          state = 4
        } else {
          if num_lt(count, Fix(0L)) {
            merr("Improper count to DIFF: ~M", [count]) |> ignore
          }
          state = 3
        }
      }
      3 => {
        v = cadr(z)
        let vc = symval(q_d_vect_coords)
        if fixnump(v) &&
          vc.truthy() &&
          num_gt(v, Fix(0L)) &&
          !num_gt(v, symval(q_d_dim)) {
          v = if atom(vc) {
            meval1(list2(list3(vc, q_simp, q_array), v)).0
          } else if eq(caar(vc), q_mlist) {
            if !num_lt(v, int(length(vc))) {
              merr("Coordinate list too short for derivative index", [])
            } else {
              nth(to_int(v), vc)
            }
          } else {
            v
          }
        }
        if zerop(count) {
          rplacd(z, cdddr(z)) |> ignore
          state = 1
        } else {
          exp = sdiff(exp, v)
          if zerop1(exp).truthy() {
            return Fix(0L)
          }
          count = num_sub(count, Fix(1L))
        }
      }
      _ => return diff_pctderiv(cons(exp, cdr(e)))
    }
  }
  Nil
}

///|
fn chainrule1(e : Value, x : Value) -> Value raise {
  if atom(e) {
    let y = car(mget(e, q_depends))
    if eq(y, cadr(symval(q_d_coord))) {
      return subst(x, y, chainrule(e, y))
    }
  }
  chainrule(e, x)
}

///|
/// RETURN: n*v^n*rename(v'/v) where e=v^n
fn diffexpt1(e : Value, x : Value) -> Value raise {
  list4(
    list1(q_mtimes),
    caddr(e),
    e,
    d_rename(
      list1(
        list3(
          list1(q_mtimes),
          list3(list1(q_mexpt), cadr(e), Fix(-1L)),
          sdiff(cadr(e), x),
        ),
      ),
    ),
  )
}

///|
/// Helpers with new index notation: -j is represented as
/// ((MTIMES [SIMP]) -1 $J)
fn sdiff_negindexp(i : Value) -> Value raise {
  lbool(
    consp(i) &&
    eq(caar(i), q_mtimes) &&
    eql(cadr(i), Fix(-1L)) &&
    consp(cddr(i)) &&
    cdddr(i) is Nil,
  )
}

///|
fn sdiff_negindex_base(i : Value) -> Value raise {
  caddr(i)
}

///|
/// Differentiation of the metric (and its derivatives) with respect to the
/// metric: the special cases of the tensor/tensor branch of SDIFF. Returns
/// None when no case applies.
fn share_itensor__sdiff_metric(e : Value, x : Value) -> Value? raise {
  if !boundp(q_d_imetric) {
    return None
  }
  let g = symval(q_d_imetric)
  if !(eq(caar(e), g) && eq(caar(x), g)) {
    return None
  }
  let ecov = length(cdadr(e))
  let econ = length(cdaddr(e))
  let eder = length(cdddr(e))
  let xcov = length(cdadr(x))
  let xcon = length(cdaddr(x))
  let xder = length(cdddr(x))
  let mt = () => list2(q_mtimes, q_simp)
  let em = () => share_itensor__empty_ml()
  let gl = (a : Value, b : Value) => share_itensor__metric(
    share_itensor__msl([a, b]),
    em(),
    [],
  )
  let e0 = nth(0, cdadr(e))
  let e1 = nth(1, cdadr(e))
  if ecov == 2 && econ == 0 && eder == 0 && xcov == 0 && xcon == 2 && xder == 0 {
    // dg([a,b],[])/dg([],[m,n])
    return Some(
      list4(
        mt(),
        Fix(-1L),
        gl(e0, nth(0, cdaddr(x))),
        gl(e1, nth(1, cdaddr(x))),
      ),
    )
  }
  if ecov == 0 && econ == 2 && eder == 0 && xcov == 2 && xcon == 0 && xder == 0 {
    // dg([],[a,b])/dg([m,n],[])
    return Some(
      list4(
        mt(),
        Fix(-1L),
        share_itensor__metric(
          em(),
          share_itensor__msl([nth(0, cdaddr(e)), nth(0, cdadr(x))]),
          [],
        ),
        share_itensor__metric(
          em(),
          share_itensor__msl([nth(1, cdaddr(e)), nth(1, cdadr(x))]),
          [],
        ),
      ),
    )
  }
  let x0 = nth(0, cdaddr(x))
  let x1 = nth(1, cdaddr(x))
  if ecov == 2 && econ == 0 && eder == 1 && xcov == 0 && xcon == 2 && xder == 0 {
    // dg([a,b],[],y)/dg([],[m,n])
    let d1 = d_idummy()
    let d2 = d_idummy()
    return Some(
      list3(
        mt(),
        share_itensor__metric(em(), share_itensor__msl([d1, d2]), [cadddr(e)]),
        list3(
          list2(q_mplus, q_simp),
          list4(mt(), gl(e0, x0), gl(d1, x1), gl(e1, d2)),
          list4(mt(), gl(e0, d1), gl(e1, x0), gl(d2, x1)),
        ),
      ),
    )
  }
  if ecov == 2 && econ == 0 && eder == 1 && xcov == 0 && xcon == 2 && xder == 1 {
    // dg([a,b],[],y)/dg([],[m,n],k)
    return Some(
      list([
        mt(),
        Fix(-1L),
        gl(e0, x0),
        gl(e1, x1),
        share_itensor__kd1(cadddr(e), cadddr(x)),
      ]),
    )
  }
  if ecov == 2 && econ == 0 && eder == 2 && xcov == 0 && xcon == 2 && xder == 0 {
    // dg([a,b],[],y,d)/dg([],[m,n])
    let d1 = d_idummy()
    let d2 = d_idummy()
    return Some(
      list3(
        mt(),
        share_itensor__metric(em(), share_itensor__msl([d1, d2]), [
          nth(0, cdddr(e)),
          nth(1, cdddr(e)),
        ]),
        list3(
          list2(q_mplus, q_simp),
          list4(mt(), gl(e0, x0), gl(d1, x1), gl(e1, d2)),
          list4(mt(), gl(e0, d1), gl(e1, x0), gl(d2, x1)),
        ),
      ),
    )
  }
  if ecov == 2 && econ == 0 && eder == 2 && xcov == 0 && xcon == 2 && xder == 1 {
    // dg([a,b],[],y,d)/dg([],[m,n],k)
    let d1 = d_idummy()
    let d2 = d_idummy()
    let d3 = d_idummy()
    let d4 = d_idummy()
    return Some(
      list3(
        mt(),
        list3(
          list2(q_mplus, q_simp),
          list4(mt(), gl(e0, d3), gl(d2, d4), gl(e1, d1)),
          list4(mt(), gl(e0, d2), gl(e1, d3), gl(d1, d4)),
        ),
        list3(
          list2(q_mplus, q_simp),
          list([
            mt(),
            share_itensor__kd1(x0, d3),
            share_itensor__kd1(x1, d4),
            share_itensor__kd1(nth(1, cdddr(e)), nth(0, cdddr(x))),
            share_itensor__metric(em(), share_itensor__msl([d2, d1]), [
              nth(0, cdddr(e)),
            ]),
          ]),
          list([
            mt(),
            share_itensor__kd1(x0, d2),
            share_itensor__kd1(x1, d1),
            share_itensor__kd1(nth(0, cdddr(e)), nth(0, cdddr(x))),
            share_itensor__metric(em(), share_itensor__msl([d3, d4]), [
              nth(1, cdddr(e)),
            ]),
          ]),
        ),
      ),
    )
  }
  if ecov == 2 && econ == 0 && eder == 2 && xcov == 0 && xcon == 2 && xder == 2 {
    // dg([a,b],[],y,d)/dg([],[m,n],k,l)
    return Some(
      list([
        mt(),
        Fix(-1L),
        gl(e0, x0),
        gl(e1, x1),
        share_itensor__kd1(cadddr(e), cadddr(x)),
        share_itensor__kd1(nth(1, cdddr(e)), nth(1, cdddr(x))),
      ]),
    )
  }
  None
}

///|
/// Differentiation of tensors with respect to tensors.
fn share_itensor__sdiff_tensor(e : Value, x : Value) -> Value raise {
  match share_itensor__sdiff_metric(e, x) {
    Some(r) => return r
    None => ()
  }
  if eq(caar(e), caar(x)) &&
    length(cdadr(e)) == length(cdadr(x)) &&
    length(cdaddr(e)) == length(cdaddr(x)) &&
    length(cdddr(e)) == length(cdddr(x)) &&
    // New: signs in the covariant lists must agree slot by slot
    share_itensor__every2(
      (u, v) => sdiff_negindexp(u).truthy() == sdiff_negindexp(v).truthy(),
      cdadr(e),
      cdadr(x),
    ) {
    return cons(
      list1(q_mtimes),
      cons(
        Fix(1L),
        append_n([
          mapcar2(
            (x, y) => if sdiff_negindexp(x).truthy() {
              // -j in e, -b in x: dT^j/dT^b = kdelta([b],[j])
              share_itensor__kd1(sdiff_negindex_base(y), sdiff_negindex_base(x))
            } else {
              share_itensor__kd1(x, y)
            },
            cdadr(e),
            cdadr(x),
          ),
          mapcar2((x, y) => share_itensor__kd1(x, y), cdaddr(x), cdaddr(e)),
          mapcar2((x, y) => share_itensor__kd1(x, y), cdddr(e), cdddr(x)),
        ]),
      ),
    )
  }
  let bound = boundp(q_d_imetric)
  let g = symval(q_d_imetric)
  if (
      // catchall symbols constructed from the metric tensor
      bound &&
      eq(caar(x), g) &&
      memq(
        caar(e),
        cons(q_d_icurvature, cons(q_p_icurvature, symval(q_christoffels))),
      ).truthy()
    ) ||
    (
      // d(some covi)/d(cov metric)
      bound &&
      !eq(caar(e), g) &&
      eq(caar(x), g) &&
      length(cdadr(x)) == 2 &&
      length(cdaddr(x)) == 0 &&
      length(cdddr(x)) == 0 &&
      length(cdadr(e)) + length(cdddr(e)) > 0
    ) ||
    (
      // d(some conti)/d(cont metric)
      bound &&
      !eq(caar(e), g) &&
      eq(caar(x), g) &&
      length(cdadr(x)) == 0 &&
      length(cdaddr(x)) == 2 &&
      length(cdddr(x)) == 0 &&
      length(cdaddr(e)) > 0
    ) ||
    (
      // da([a,b],y)/da([m,n],k) with a+b=m+n, y=k
      depends(caar(e), caar(x)).truthy() &&
      length(cdadr(e)) + length(cdaddr(e)) ==
      length(cdadr(x)) + length(cdaddr(x)) &&
      length(cdddr(e)) == length(cdddr(x))
    ) {
    list3(list1(q_p_derivative), e, x)
  } else {
    Fix(0L)
  }
}

///|
/// `(every f l1 l2)`: stops at the end of the shorter list.
fn share_itensor__every2(
  f : (Value, Value) -> Bool raise,
  l1 : Value,
  l2 : Value,
) -> Bool raise {
  let mut a = l1
  let mut b = l2
  while a is Cons(_) && b is Cons(_) {
    if !f(car(a), car(b)) {
      return false
    }
    a = cdr(a)
    b = cdr(b)
  }
  true
}

///|
/// The itensor redefinition of SDIFF (comm.lisp): the derivative of any
/// indexed object appends on the coordinate index in sorted order unless
/// the indexed object was declared constant in which case 0 is returned.
fn share_itensor__sdiff(e : Value, x : Value) -> Value raise {
  let r : Value = if mnump(e).truthy() {
    Fix(0L)
  } else if alike1(e, x).truthy() &&
    !(rpobj(e).truthy() && rpobj(x).truthy()) {
    Fix(1L)
  } else if atom(e) || memq(q_array, cdar(e)).truthy() {
    chainrule1(e, x)
  } else if kindp(caar(e), q_d_constant).truthy() {
    // New line added
    Fix(0L)
  } else if eq(caar(e), q_mrat) {
    ratdx(e, x)
  } else if eq(caar(e), q_mplus) {
    simplus(cons(list1(q_mplus), sdiffmap(cdr(e), x)), Fix(1L), t)
  } else if eq(caar(e), q_mequal) {
    let a = sdiff(cadr(e), x)
    list3(car(e), a, sdiff(caddr(e), x))
  } else if mbagp(e).truthy() {
    cons(car(e), sdiffmap(cdr(e), x))
  } else if eq(caar(e), q_d_matrix) {
    cons(car(e), mapcar(y => cons(car(y), sdiffmap(cdr(y), x)), cdr(e)))
  } else if eq(caar(e), q_mtimes) {
    addn(sdifftimes(cdr(e), x), t)
  } else if eq(caar(e), q_mexpt) {
    diffexpt(e, x)
  } else if boundp(q_d_imetric) &&
    rpobj(x).truthy() &&
    eq(caar(e), q_p_determinant) &&
    eq(cadr(e), symval(q_d_imetric)) {
    let g = symval(q_d_imetric)
    if eq(caar(x), g) &&
      length(cdadr(x)) == 0 &&
      length(cdaddr(x)) == 2 &&
      length(cdddr(x)) == 0 {
      list4(
        list2(q_mtimes, q_simp),
        Fix(-1L),
        list2(list2(q_p_determinant, q_simp), g),
        share_itensor__metric(
          share_itensor__msl([nth(0, cdaddr(x)), nth(1, cdaddr(x))]),
          share_itensor__empty_ml(),
          [],
        ),
      )
    } else if eq(caar(x), g) &&
      length(cdadr(x)) == 2 &&
      length(cdaddr(x)) == 0 &&
      length(cdddr(x)) == 0 {
      list3(
        list2(q_mtimes, q_simp),
        list2(list2(q_p_determinant, q_simp), g),
        share_itensor__metric(
          share_itensor__empty_ml(),
          share_itensor__msl([nth(0, cdadr(x)), nth(1, cdadr(x))]),
          [],
        ),
      )
    } else {
      Fix(0L)
    }
  } else if rpobj(e).truthy() && rpobj(x).truthy() {
    share_itensor__sdiff_tensor(e, x)
  } else if depends(e, x) is Nil {
    if fixnump(x) {
      list3(list1(q_p_derivative), e, x)
    } else if atom(x) {
      Fix(0L)
    } else {
      list3(list1(q_p_derivative), e, x)
    }
  } else if eq(caar(e), q_mnctimes) {
    // This line moved down
    simplus(
      list3(
        list1(q_mplus),
        list3(list1(q_mnctimes), sdiff(cadr(e), x), caddr(e)),
        list3(list1(q_mnctimes), cadr(e), sdiff(caddr(e), x)),
      ),
      Fix(1L),
      Nil,
    )
  } else if eq(caar(e), q_mncexpt) {
    diffncexpt(e, x)
  } else if eq(caar(e), q_p_integrate) {
    diffint(e, x)
  } else if eq(caar(e), q_p_derivative) {
    if atom(cadr(e)) || memq(q_array, cdaadr(e)).truthy() {
      chainrule1(e, x)
    } else if freel(cdr(e), x).truthy() {
      Fix(0L)
    } else {
      diff_pctderiv(list3(e, x, Fix(1L)))
    }
  } else if eq(caar(e), q_p_sum) || eq(caar(e), q_p_product) {
    diffsumprod(e, x)
  } else {
    sdiffgrad(e, x)
  }
  simplifya(r, t)
}

// VTT: several of these functions have been copied verbatim from comm.lisp
// and comm2.lisp, in order to implement indicial differentiation as
// distinct from differentiation with respect to an external variable.

///|
fn idiffmap(e : Value, x : Value) -> Value raise {
  mapcar(term => idiff(term, x), e)
}

///|
fn idifftimes(l : Value, x : Value) -> Value raise {
  let mut l = l
  let mut left : Value = Nil
  let mut out : Value = Nil
  while true {
    let term = car(l)
    l = cdr(l)
    out = cons(muln(cons(idiff(term, x), append(left, l)), t), out)
    if l is Nil {
      return out
    }
    left = cons(term, left)
  }
  out
}

///|
/// RETURN: n*v^n*(v'/v) where e=v^n
fn idiffexpt1(e : Value, x : Value) -> Value raise {
  list4(
    list1(q_mtimes),
    caddr(e),
    e,
    list3(
      list1(q_mtimes),
      list3(list1(q_mexpt), cadr(e), Fix(-1L)),
      idiff(cadr(e), x),
    ),
  )
}

///|
fn idiffexpt(e : Value, x : Value) -> Value raise {
  if mnump(caddr(e)).truthy() {
    mul3(
      caddr(e),
      power(cadr(e), addk(caddr(e), Fix(-1L))),
      idiff(cadr(e), x),
    )
  } else {
    mul2(
      e,
      add2(
        mul3(power(cadr(e), Fix(-1L)), caddr(e), idiff(cadr(e), x)),
        mul2(
          simplifya(list2(list1(q_p_log), cadr(e)), t),
          idiff(caddr(e), x),
        ),
      ),
    )
  }
}

///|
fn idiffint(e : Value, x : Value) -> Value raise {
  if cdddr(e) is Nil {
    if alike1(x, caddr(e)).truthy() {
      cadr(e)
    } else if !atom(caddr(e)) && atom(x) && free(caddr(e), x) is Nil {
      mul2(cadr(e), idiff(caddr(e), x))
    } else {
      let a = idiff(cadr(e), x)
      if d_constantp(a).truthy() || (atom(caddr(e)) && free(a, caddr(e)).truthy()) {
        mul2(a, caddr(e))
      } else {
        simplifya(list3(list1(q_p_integrate), a, caddr(e)), t)
      }
    }
  } else if alike1(x, caddr(e)).truthy() {
    addn(idiffint1(cdr(e), x, x), t)
  } else {
    let a = idiff(cadr(e), x)
    addn(
      cons(
        if equal(a, Fix(0L)) {
          Fix(0L)
        } else {
          simplifya(
            list([list1(q_p_integrate), a, caddr(e), cadddr(e), car(cddddr(e))]),
            t,
          )
        },
        idiffint1(cdr(e), x, caddr(e)),
      ),
      t,
    )
  }
}

///|
fn idiffint1(e : Value, x : Value, y : Value) -> Value raise {
  let u = idiff(cadddr(e), x)
  let v = idiff(caddr(e), x)
  list2(
    if pzerop(u).truthy() {
      Fix(0L)
    } else {
      mul2(u, maxima_substitute(cadddr(e), y, car(e)))
    },
    if pzerop(v).truthy() {
      Fix(0L)
    } else {
      mul3(v, maxima_substitute(caddr(e), y, car(e)), Fix(-1L))
    },
  )
}

///|
fn idiff_pctderiv(e : Value) -> Value raise {
  with_special(q_derivflag, Nil, () => simplifya(cons(list1(q_p_idiff), e), t))
}

///|
fn ideriv(e : Value) -> Value raise {
  let mut e = e
  if e is Nil {
    wna_err(q_d_idiff) |> ignore
  } else if cdr(e) is Nil {
    return stotaldiff(car(e))
  } else if cddr(e) is Nil {
    nconc(e, list1(Fix(1L))) |> ignore
  }
  let mut exp = car(e)
  e = copy_list(e)
  let mut z = e
  let mut count : Value = Nil
  // states: 0 loop, 1 loop2, 2 doit, 3 loop1, 4 noun
  let mut state = 0
  while true {
    match state {
      0 => {
        // DERIVLIST is set by $EV
        let dl = symval(q_derivlist)
        if dl is Nil || member_equal(cadr(z), dl).truthy() {
          state = 2
        } else {
          z = cdr(z)
          state = 1
        }
      }
      1 =>
        if cdr(z).truthy() {
          state = 0
        } else if cdr(e) is Nil {
          return exp
        } else {
          state = 4
        }
      2 => {
        state = 3
        if nonvarcheck(cadr(z), q_d_idiff).truthy() {
          ()
        } else if cddr(z) is Nil {
          wna_err(q_d_idiff) |> ignore
        } else if !fixnump(caddr(z)) {
          state = 4
        } else {
          count = caddr(z)
          if minusp(count) {
            merr("Improper count to IDIFF:~%~M", [count]) |> ignore
          }
        }
      }
      3 =>
        if zerop(count) {
          rplacd(z, cdddr(z)) |> ignore
          state = 1
        } else {
          exp = idiff(exp, cadr(z))
          if equal(exp, Fix(0L)) {
            return Fix(0L)
          }
          count = num_sub(count, Fix(1L))
        }
      _ => return idiff_pctderiv(cons(exp, cdr(e)))
    }
  }
  Nil
}

///|
fn idiffncexpt(e : Value, x : Value) -> Value raise {
  let base_star = cadr(e)
  let pow = caddr(e)
  if mnump(pow).truthy() && (!fixnump(pow) || num_lt(pow, Fix(0L))) {
    // POW cannot be 0
    idiff_pctderiv(list3(e, x, Fix(1L)))
  } else if atom(base_star) && eq(base_star, x) && free(pow, base_star).truthy() {
    mul2_star(pow, list3(list1(q_mncexpt), base_star, add2(pow, Fix(-1L))))
  } else if fixnump(pow) {
    let deriv = idiff(base_star, x)
    let mut ans : Value = Nil
    let n = to_int(pow)
    for i in 0..<n {
      ans = cons(
        list3(
          list1(q_mnctimes),
          list3(list1(q_mncexpt), base_star, int(i)),
          list3(
            list1(q_mnctimes),
            deriv,
            list3(list1(q_mncexpt), base_star, int(n - 1 - i)),
          ),
        ),
        ans,
      )
    }
    addn(ans, Nil)
  } else if depends(pow, x) is Nil &&
    (atom(pow) || (atom(base_star) && free(pow, base_star).truthy())) {
    let deriv = idiff(base_star, x)
    let index = gensumindex()
    simplifya(
      list([
        list1(q_p_sum),
        list3(
          list1(q_mnctimes),
          list3(list1(q_mncexpt), base_star, index),
          list3(
            list1(q_mnctimes),
            deriv,
            list3(
              list1(q_mncexpt),
              base_star,
              list4(
                list1(q_mplus),
                pow,
                Fix(-1L),
                list3(list1(q_mtimes), Fix(-1L), index),
              ),
            ),
          ),
        ),
        index,
        Fix(0L),
        list3(list1(q_mplus), pow, Fix(-1L)),
      ]),
      Nil,
    )
  } else {
    idiff_pctderiv(list3(e, x, Fix(1L)))
  }
}

///|
fn idiffsumprod(e : Value, x : Value) -> Value raise {
  if !atom(x) ||
    free(cadddr(e), x) is Nil ||
    free(car(cddddr(e)), x) is Nil {
    idiff_pctderiv(list3(e, x, Fix(1L)))
  } else if eq(caddr(e), x) {
    Fix(0L)
  } else {
    let mut u = idiff(cadr(e), x)
    u = simplifya(
      list([
        list1(q_p_sum),
        if eq(caar(e), q_p_sum) {
          u
        } else {
          div(u, cadr(e))
        },
        caddr(e),
        cadddr(e),
        car(cddddr(e)),
      ]),
      t,
    )
    if eq(caar(e), q_p_sum) {
      u
    } else {
      mul2(e, u)
    }
  }
}

///|
fn idiffgrad(e : Value, x : Value) -> Value raise {
  let fun = caar(e)
  if eq(fun, q_mqapply) && zl_get(caaadr(e), q_grad).truthy() {
    return idiffgrad(
      cons(cons(caaadr(e), Nil), append(cdadr(e), cddr(e))),
      x,
    )
  }
  let grad : Value = if eq(fun, q_mqapply) { Nil } else { zl_get(fun, q_grad) }
  if eq(fun, q_mqapply) || grad is Nil {
    if depends(e, x) is Nil {
      Fix(0L)
    } else {
      idiff_pctderiv(list3(e, x, Fix(1L)))
    }
  } else if length(cdr(e)) != length(car(grad)) {
    merr("Wrong number of arguments for ~:M", [fun])
  } else {
    let args = idiffmap(cdr(e), x)
    let mut l1 = cdr(grad)
    let mut a = args
    let mut l2 : Value = Nil
    while l1.truthy() {
      l2 = cons(
        if equal(car(a), Fix(0L)) {
          Fix(0L)
        } else {
          car(l1)
        },
        l2,
      )
      l1 = cdr(l1)
      a = cdr(a)
    }
    addn(
      mapcar2(
        (p, q) => mul2(p, q),
        cdr(substitutel(cdr(e), car(grad), cons(list1(q_mlist), nreverse(l2)))),
        args,
      ),
      t,
    )
  }
}

///|
fn idiff(e : Value, x : Value) -> Value raise {
  if d_constantp(e).truthy() {
    Fix(0L)
  } else if alike1(e, x).truthy() {
    Fix(1L)
  } else if atom(e) || memq(q_array, cdar(e)).truthy() {
    Fix(0L)
  } else if kindp(caar(e), q_d_constant).truthy() {
    // New line added
    Fix(0L)
  } else if eq(caar(e), q_mrat) {
    ratdx(e, x)
  } else if eq(caar(e), q_mplus) {
    simplus(cons(list1(q_mplus), idiffmap(cdr(e), x)), Fix(1L), t)
  } else if eq(caar(e), q_mequal) {
    let a = d_idiff(list2(cadr(e), x))
    list3(car(e), a, d_idiff(list2(caddr(e), x)))
  } else if eq(caar(e), q_d_matrix) {
    cons(car(e), mapcar(y => cons(car(y), idiffmap(cdr(y), x)), cdr(e)))
  } else if eq(caar(e), q_mtimes) {
    addn(idifftimes(cdr(e), x), t)
  } else if eq(caar(e), q_mexpt) {
    idiffexpt1(e, x)
  } else if rpobj(e).truthy() {
    diffrpobj(e, x)
  } else if boundp(q_d_imetric) &&
    eq(caar(e), q_p_determinant) &&
    eq(cadr(e), symval(q_d_imetric)) {
    let mut dummy = d_idummy()
    if eq(dummy, x) {
      dummy = d_idummy()
    }
    list4(
      list2(q_mtimes, q_simp),
      Fix(2L),
      e,
      list3(
        diffop(),
        share_itensor__ml(list2(dummy, x)),
        share_itensor__ml(list1(dummy)),
      ),
    )
  } else if eq(caar(e), q_mnctimes) {
    simplus(
      list3(
        list1(q_mplus),
        list3(list1(q_mnctimes), d_idiff(list2(cadr(e), x)), caddr(e)),
        list3(list1(q_mnctimes), cadr(e), d_idiff(list2(caddr(e), x))),
      ),
      Fix(1L),
      Nil,
    )
  } else if eq(caar(e), q_mncexpt) {
    idiffncexpt(e, x)
  } else if eq(caar(e), q_p_integrate) {
    idiffint(e, x)
  } else if eq(caar(e), q_p_derivative) {
    if atom(cadr(e)) || memq(q_array, cdaadr(e)).truthy() {
      Fix(0L)
    } else {
      idiff_pctderiv(list3(e, x, Fix(1L)))
    }
  } else if eq(caar(e), q_p_sum) || eq(caar(e), q_p_product) {
    idiffsumprod(e, x)
  } else {
    idiffgrad(e, x)
  }
}

///|
/// Derivative of an indexed object
fn diffrpobj(e : Value, x : Value) -> Value raise {
  if memq(caar(e), symval(q_d_coord)).truthy() &&
    cdadr(e) is Nil &&
    length(cdaddr(e)) == 1 &&
    cdddr(e) is Nil {
    // Special case: functions declared with coord()
    delta(list1(x), cdaddr(e))
  } else {
    // Everything else
    nconc(
      list3(car(e), cadr(e), caddr(e)),
      if cdddr(e) is Nil {
        list1(x)
      } else if symval(q_d_iframe_flag).truthy() ||
        symval(q_d_itorsion_flag).truthy() {
        // Derivative indices do not commute when frames are used
        append(cdddr(e), list1(x))
      } else {
        itensor_sort(append(cdddr(e), list1(x)))
      },
    )
  }
}
