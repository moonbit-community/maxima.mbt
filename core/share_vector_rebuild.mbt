// Port of share/vector/vector_rebuild.lisp (Volker van Nek): utilities for
// working with vectors.
//
// Functions at Maxima level: vector_rebuild(x), vector_rebuild(x,
// [param_list]), vector_simp(x) and vector_factor(x) (evfun properties),
// extract_equations(x). Operators: |x| vector length, x~y cross product
// (lbp=134, rbp=133). Option variable: vector_factor_minus.

// mtimesq
//
// In combination with setting listarith & friends to false mtimesq allows
// to suppress automatic arithmetics and to bypass the displa function
// dim-mquotient. mtimesq display symbol is "*" and is settable by
// stardisp. One evaluation steps from mtimesq to mtimes and vice versa.

///|
fn simp_mtimesq(a : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  list3(
    list2(q_mtimesq, q_simp),
    simplifya(cadr(a), z),
    simplifya(caddr(a), z),
  )
}

///|
fn mtimesq(a : Value, b : Value) -> Value raise {
  list3(list2(q_mtimes, q_simp), a, b)
}

///|
/// extend stardisp in displa.lisp
fn stardisp1(symbol : Value, val : Value) -> Value raise {
  ignore(symbol)
  putprop(
    q_mtimes,
    if val.truthy() {
      list1(Char('*'))
    } else {
      list1(Char(' '))
    },
    q_dissym,
  )
  |> ignore
  putprop(q_mtimesq, get(q_mtimes, q_dissym), q_dissym)
}

///|
fn mtimesqp(expr : Value) -> Value raise {
  lbool(!atom(expr) && eq(q_mtimesq, caar(expr)))
}

///|
/// TeX-support
fn tex_mtimesq(x : Value, l : Value, r : Value) -> Value raise {
  append_n([
    l,
    tex(cadr(x), Nil, Nil, q_mparen, q_mparen),
    list1(Str("\\,")),
    tex(caddr(x), Nil, Nil, q_mparen, q_mparen),
    r,
  ])
}

///|
/// mtimesq needs an extra evaluation here
fn d_vector_simp(expre_dol_dolion : Value) -> Value raise {
  with_specials([(q_d_listarith, t), (q_d_doallmxops, t)], () => d_expand(
    meval(list3(list1(q_d_ev), expre_dol_dolion, q_d_infeval)),
  ))
}

///|
fn d_vector_rebuild(expr : Value, params? : Value) -> Value raise {
  let params = match params {
    Some(p) => p
    None => list1(list1(q_mlist))
  }
  if d_listp(params) is Nil ||
    some(
      p => d_constantp(p).truthy() ||
        !(d_symbolp(p).truthy() || d_subvarp(p).truthy()),
      cdr(params),
    ) {
    merror(
      Str(
        "The optional second argument to `vector_rebuild'\nmust be a list of symbols or subscripted variables.",
      ),
      Nil,
    )
    |> ignore
  }
  if atom(expr) || d_scalarp(expr).truthy() {
    return expr
  }
  let op = mop(expr)
  let args = margs(expr)
  if car(args) is Nil {
    // noarg-op
    return expr
  }
  if eq(op, q_mequal) {
    cons(
      list2(q_mequal, q_simp),
      mapcar(arg => d_vector_rebuild(arg, params~), args),
    )
  } else if eq(op, q_mdefine) {
    meval(
      list3(
        list2(q_mdefine, q_simp),
        cadr(expr),
        d_vector_rebuild(caddr(expr), params~),
      ),
    )
  } else {
    vector_rebuild(expr, cdr(params))
  }
}

///|
fn vector_rebuild(expr : Value, params : Value) -> Value raise {
  let mut coef_matrix : Value = Nil
  let mut col_flag = false
  let mut res = list2(list1(q_mplus), Fix(0L))
  let mut n = 0
  let vec = d_vector_simp(expr)
  if vector_p(vec) is Nil {
    return expr
  }
  if zero_vector_p(vec).truthy() {
    return vec
  }
  if column_vector_p(vec).truthy() {
    col_flag = true
  }
  for a in cdr(vec).iter() {
    let a = if col_flag { cadr(a) } else { a }
    coef_matrix = append(coef_matrix, list1(coef_list(a, params)))
  }
  let params = append(params, list1(Fix(1L)))
  for p in params.iter() {
    let col = mapcar(row => nth(n, row), coef_matrix)
    n = n + 1
    if some(e => zerop1(e) is Nil, col) {
      let mut tmp_vec = cons(list2(q_mlist, q_simp), col)
      if col_flag {
        tmp_vec = row_to_column(tmp_vec)
      }
      res = append(res, list1(list3(list1(q_mtimes), p, tmp_vec)))
    }
  }
  meval(res)
}

///|
/// e.g. expr=4-2*t+3*s, params=(s t) --> (3 -2 4)
fn coef_list(expr : Value, params : Value) -> Value raise {
  let mut expr = expr
  let mut res : Value = Nil
  for p in params.iter() {
    let c = meval(list3(list1(q_d_coeff), expr, p))
    res = cons(c, res)
    expr = meval(
      list3(
        list1(q_mplus),
        expr,
        list3(list1(q_mtimes), list2(list1(q_mminus), c), p),
      ),
    )
  }
  reverse(cons(expr, res))
}

///|
fn d_extract_equations(equation : Value) -> Value raise {
  let err_msg : Value = Str("Argument to `extract_equations' is not a vector equation.")
  if !atom(equation) && !eq(mop(equation), q_mequal) {
    merror(err_msg, Nil) |> ignore
  }
  if atom(equation) && equation.truthy() {
    // (cdr equation) on a non-list atom
    raise type_error(equation, "LIST")
  }
  let args = cdr(equation)
  let mut left = d_vector_simp(car(args))
  let mut right = d_vector_simp(cadr(args))
  if vector_p(left).truthy() && vector_p(right).truthy() {
    // OK
    ()
  } else if eql(Fix(0L), left) && vector_p(right).truthy() {
    // due to a bug in Maxima allow left or right to be zero
    left = cons(
      list2(q_mlist, q_simp),
      list(Array::make(to_int(vector_dim(right)), Fix(0L))),
    )
  } else if eql(Fix(0L), right) && vector_p(left).truthy() {
    right = cons(
      list2(q_mlist, q_simp),
      list(Array::make(to_int(vector_dim(left)), Fix(0L))),
    )
  } else {
    merror(err_msg, Nil) |> ignore
  }
  if d_listp(left) is Nil {
    left = column_to_row(left)
  }
  if d_listp(right) is Nil {
    right = column_to_row(right)
  }
  meval(list4(list1(q_d_map), Str("="), left, right))
}

///|
fn d_vector_factor(expr : Value) -> Value raise {
  if atom(expr) {
    return expr
  }
  let op = mop(expr)
  if eq(op, q_mequal) {
    cons(list2(q_mequal, q_simp), mapcar(e => d_vector_factor(e), cdr(expr)))
  } else if eq(op, q_mdefine) {
    meval(
      list3(
        list2(q_mdefine, q_simp),
        cadr(expr),
        d_vector_factor(caddr(expr)),
      ),
    )
  } else if eq(op, q_mplus) || eq(op, q_mnctimes) || eq(op, q_crossq) {
    cons(list2(op, q_simp), mapcar(e => d_vector_factor(e), cdr(expr)))
  } else {
    // incl. op=mtimes,mminus
    vector_extract_gcd(expr)
  }
}

///|
fn vector_extract_gcd(expr : Value) -> Value raise {
  with_special(q_d_ratprint, Nil, () => {
    let mut vec = d_vector_simp(expr)
    if zero_vector_p(vec).truthy() || zero__dolmatrix_p(vec).truthy() {
      vec
    } else if d_listp(vec).truthy() || d_matrixp(vec).truthy() {
      let args = if d_listp(vec).truthy() {
        cdr(vec)
      } else {
        append_n(cdr(vec).iter().map(r => cdr(r)).collect())
      }
      let mut fac = car(args)
      for a in args.iter() {
        fac = d_gcd(fac, a, Nil)
      }
      vec = meval(
        list3(
          list1(q_d_fullmapl),
          list3(
            list1(q_lambda),
            list2(list1(q_mlist), q_e),
            list2(list1(q_d_ratsimp), list3(list1(q_mquotient), q_e, fac)),
          ),
          vec,
        ),
      )
      let mut minus_flag = false
      if symval(q_d_vector_factor_minus).truthy() &&
        every(
          a => eq(
            t,
            meval(list2(list1(q_d_is), list3(list1(q_mlessp), a, Fix(0L)))),
          ),
          args,
        ) {
        minus_flag = true
        vec = meval(
          list3(
            list1(q_d_fullmapl),
            list3(
              list1(q_lambda),
              list2(list1(q_mlist), q_e),
              list2(list1(q_mminus), q_e),
            ),
            vec,
          ),
        )
      }
      if minus_flag {
        if eql(Fix(1L), fac) {
          list2(list1(q_mminus), vec)
        } else {
          list2(list1(q_mminus), list3(list1(q_mtimesq), fac, vec))
        }
      } else if eql(Fix(1L), fac) {
        vec
      } else {
        list3(list1(q_mtimesq), fac, vec)
      }
    } else {
      expr
    }
  })
}

///|
/// vector length
fn simp_vector_length(a : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  ignore(z)
  oneargcheck(a) |> ignore
  let a = d_vector_simp(cadr(a))
  if d_scalarp(a).truthy() {
    meval(list2(list2(q_mabs, q_simp), a))
  } else if vector_p(a).truthy() {
    let args = if d_listp(a).truthy() {
      cdr(a)
    } else {
      mapcar(x => cadr(x), cdr(a))
    }
    let args = mapcar(x => meval(list3(list1(q_mexpt), x, Fix(2L))), args)
    meval(
      list2(list2(q_d_sqrt, q_simp), cons(list2(q_mplus, q_simp), args)),
    )
  } else {
    list2(list1(q_d_op_bar), a)
  }
}

///|
/// `((mplus simp) ((mtimes simp) a b) ((mminus) ((mtimes simp) c d)))`
/// evaluated
fn vector_rebuild__det2(a : Value, b : Value, c : Value, d : Value) -> Value raise {
  meval(
    list3(
      list2(q_mplus, q_simp),
      list3(list2(q_mtimes, q_simp), a, b),
      list2(list1(q_mminus), list3(list2(q_mtimes, q_simp), c, d)),
    ),
  )
}

///|
/// cross product
fn simp_vector_cross(a : Value, tmp : Value, z : Value) -> Value raise {
  ignore(tmp)
  ignore(z)
  twoargcheck(a) |> ignore
  let mut v = d_vector_simp(cadr(a))
  let mut w = d_vector_simp(caddr(a))
  let mut col_flag = false
  if vector_p(v).truthy() && vector_p(w).truthy() {
    if column_vector_p(v).truthy() {
      v = column_to_row(v)
      col_flag = true
    }
    if column_vector_p(w).truthy() {
      w = column_to_row(w)
      col_flag = true
    }
    let dim_v = length(v) - 1
    let dim_w = length(w) - 1
    if dim_v == 2 && dim_w == 2 {
      // v[1]*w[2]-v[2]*w[1]
      vector_rebuild__det2(cadr(v), caddr(w), caddr(v), cadr(w))
    } else if dim_v == 3 && dim_w == 3 {
      let cross = list4(
        list2(q_mlist, q_simp),
        vector_rebuild__det2(caddr(v), cadddr(w), cadddr(v), caddr(w)),
        vector_rebuild__det2(cadddr(v), cadr(w), cadr(v), cadddr(w)),
        vector_rebuild__det2(cadr(v), caddr(w), caddr(v), cadr(w)),
      )
      if col_flag {
        row_to_column(cross)
      } else {
        cross
      }
    } else {
      list3(list1(q_d_op_tl), v, w)
    }
  } else {
    list3(list1(q_d_op_tl), v, w)
  }
}

// some small helpers

///|
/// assume col to be a column vector (a $matrix)
fn column_to_row(col : Value) -> Value raise {
  cons(list2(q_mlist, q_simp), mapcar(x => cadr(x), cdr(col)))
}

///|
/// assume row to be a row vector (a mlist)
fn row_to_column(row : Value) -> Value raise {
  cons(
    list2(q_d_matrix, q_simp),
    mapcar(e => list2(list2(q_mlist, q_simp), e), cdr(row)),
  )
}

///|
/// assume vec to be a row or column vector
fn vector_dim(vec : Value) -> Value raise {
  int(length(cdr(vec)))
}

///|
fn column_vector_p(obj : Value) -> Value raise {
  lbool(d_matrixp(obj).truthy() && length(cadr(obj)) == 2)
}

///|
fn vector_p(obj : Value) -> Value raise {
  let l = d_listp(obj)
  if l.truthy() {
    l
  } else {
    column_vector_p(obj)
  }
}

///|
fn zero_vector_p(obj : Value) -> Value raise {
  let z = zero_mlist_p(obj)
  if z.truthy() {
    z
  } else {
    lbool(zero__dolmatrix_p(obj).truthy() && length(cadr(obj)) == 2)
  }
}

///|
fn zero_mlist_p(obj : Value) -> Value raise {
  lbool(d_listp(obj).truthy() && every(x => zerop1(x).truthy(), cdr(obj)))
}

///|
fn zero__dolmatrix_p(obj : Value) -> Value raise {
  lbool(
    d_matrixp(obj).truthy() && every(x => zero_mlist_p(x).truthy(), cdr(obj)),
  )
}

///|
/// Top-level forms of vector_rebuild.lisp.
fn init_share_vector_rebuild() -> Unit raise {
  meval(list4(list1(q_d_infix), q_mtimesq, Fix(120L), Fix(119L))) |> ignore
  putprop(q_mtimesq, q_simp_mtimesq, q_operators) |> ignore
  putprop(q_mtimesq, get(q_mtimes, q_dissym), q_dissym) |> ignore
  putprop(q_d_stardisp, q_stardisp1, q_assign) |> ignore
  putprop(q_mtimesq, q_tex_mtimesq, q_tex) |> ignore
  putprop(q_d_vector_simp, t, q_evfun) |> ignore
  putprop(q_d_vector_factor, t, q_evfun) |> ignore
  meval(list3(list1(q_d_matchfix), q_d_op_bar, q_d_op_bar)) |> ignore
  putprop(q_d_op_bar, q_simp_vector_length, q_operators) |> ignore
  // lbp and rbp copied from vect.mac
  meval(list4(list1(q_d_infix), q_d_op_tl, Fix(134L), Fix(133L))) |> ignore
  putprop(q_d_op_tl, q_simp_vector_cross, q_operators) |> ignore
}
