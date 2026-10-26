// Port of src/linnew.lisp: a matrix package which uses minors.
//
// TMLINSOLVE(LIST-OF-EQUATIONS,LIST-OF-VARIABLES,LIST-OF-VARIABLES-TO-BE-
// OBTAINED) solves the linear equations. LIST-OF-VARIABLES-TO-BE-OBTAINED can
// be omitted, in which case all variables are obtained. TMNEWDET(MATRIX,
// DIMENSION) computes the determinant. DIMENSION can be omitted. The default
// is DIMENSION=(declared dimension of MATRIX). TMINVERSE(MATRIX) computes the
// inverse of matrix.
//
// The program uses hash arrays to remember the minors if N > threshold. If
// $WISE is set to T, the program knocks out unnecessary elements. But also it
// kills necessary ones in the case of zero elements! The $WISE flag should
// not be set to T for inverse. The default of $WISE is NIL.

///|
let linnew__q_lhs : Value = sym("$lhs")

///|
let linnew__q_rhs : Value = sym("$rhs")

///|
fn linnew__n() -> Int raise {
  to_int(symval(q_ear_n))
}

///|
fn linnew__threshold() -> Int raise {
  to_int(symval(q_ear_threshold))
}

///|
fn linnew__zero_rat() -> Value {
  cons(Fix(0L), Fix(1L))
}

///|
/// 2-D aref with Lisp integer indices.
fn linnew__aref2(a : Value, i : Value, j : Value) -> Value raise {
  aref(a, [to_int(i), to_int(j)])
}

///|
fn linnew__aset2(a : Value, i : Value, j : Value, v : Value) -> Unit raise {
  aset(a, [to_int(i), to_int(j)], v) |> ignore
}

///|
fn tminitialflag() -> Value raise {
  if !boundp(q_d_wise) {
    set(q_d_wise, Nil) |> ignore
  }
  if !boundp(q_d_fool) {
    set(q_d_fool, Nil)
  } else {
    Nil
  }
}

///|
/// TMDET returns the determinant of N*N matrix A2 which is in an globally
/// declared array A2.
fn tmdet(a4 : Value, ear_n : Value) -> Value raise {
  with_specials([(q_ear_n, ear_n), (q_ix, Nil)], () => {
    tminitialflag() |> ignore
    set(q_ix, Fix(0L)) |> ignore
    set(q_nx, Fix(0L)) |> ignore
    let mut index : Value = Nil
    for i in 1..=to_int(ear_n) {
      index = cons(int(i), index)
    }
    index = nreverse(index)
    tminor(a4, ear_n, Fix(1L), index, Fix(0L))
  })
}

///|
/// TMLIN SOLVES M SETS OF LINEAR EQUATIONS WITH N UNKNOWN VARIABLES. IT
/// SOLVES ONLY FOR THE FIRST NX UNKNOWNS OUT OF N. THE EQUATIONS ARE
/// EXPRESSED IN MATRIX FORM WHICH IS IN N*(N+M) ARRAY A2. THE RESULT OF TMLIN
/// IS ((DET) (U1 U2) (V1 V2) (W1 W2)) WHERE DET IS THE DETERMINANT OF THE
/// COEFFICIENT MATRIX AND X1=U1/DET, X2=U2/DET, Y1=V1/DET, ETC.
fn tmlin(a4 : Value, ear_n : Value, m : Value, nx : Value) -> Value raise {
  with_specials([(q_ear_n, ear_n), (q_nx, nx)], () => {
    let mut index : Value = Nil
    tmdefarray(ear_n) |> ignore
    tminitialflag() |> ignore
    for i in 1..=to_int(ear_n) {
      index = cons(int(i), index)
    }
    index = reverse(index)
    let r = with_special(q_ix, Fix(0L), () => {
      let mut result : Value = Nil
      while !num_gt(symval(q_ix), symval(q_nx)) {
        let ix = to_int(symval(q_ix))
        let mut res : Value = Nil
        let lim = if ix == 0 { 1 } else { to_int(m) }
        for i in 1..=lim {
          if !symval(q_d_wise).truthy() {
            tmkillarray(int(ix)) |> ignore
          }
          res = cons(tminor(a4, ear_n, Fix(1L), index, int(i)), res)
        }
        result = cons(reverse(res), result)
        if ix == 0 && equal(car(result), linnew__zero_rat()) {
          merr("tmlin: coefficient matrix is singular.", []) |> ignore
        }
        set(q_ix, int(ix + 1)) |> ignore
      }
      reverse(result)
    })
    tmrearray(ear_n) |> ignore
    r
  })
}

///|
/// TMINOR ACTUALLY COMPUTES THE MINOR DETERMINANT OF A SUBMATRIX OF A2, WHICH
/// IS CONSTRUCTED BY EXTRACTING ROWS (K,K+1,K+2,...,N) AND COLUMNS SPECIFIED
/// BY INDEX. N IS THE DIMENSION OF THE ORIGINAL MATRIX A2. WHEN TMINOR IS
/// USED FOR LINEAR EQUATION PROGRAM, JRIGHT SPECIFIES A COLUMN OF THE
/// CONSTANT MATRIX WHICH IS PLUGGED INTO AN IX-TH COLUMN OF THE COEFFICIENT
/// MATRIX FOR OBTAINING IX-TH UNKNOWN.
fn tminor(
  a4 : Value,
  ear_n : Value,
  k : Value,
  index : Value,
  jright : Value,
) -> Value raise {
  with_special(q_ear_n, ear_n, () => {
    let a4 = get_array_pointer(a4)
    let n = to_int(ear_n)
    let kk = to_int(k)
    if kk == n {
      if num_eq(k, symval(q_ix)) {
        linnew__aref2(a4, car(index), num_add(jright, ear_n))
      } else {
        linnew__aref2(a4, car(index), k)
      }
    } else {
      let mut sum = linnew__zero_rat()
      let mut j = 1
      while j <= 1 + (n - kk) {
        let l0 = extract(index, int(j))
        let subindx = cadr(l0)
        let l = car(l0)
        let aorb = if num_eq(k, symval(q_ix)) {
          linnew__aref2(a4, l, num_add(jright, ear_n))
        } else {
          linnew__aref2(a4, l, k)
        }
        if !equal(aorb, linnew__zero_rat()) {
          let name = tmaccess(subindx)
          let k1 = one_plus(k)
          let minor = if symval(q_d_fool).truthy() {
            tminor(a4, ear_n, k1, subindx, jright)
          } else if tmeval(name).truthy() {
            tmeval(name)
          } else if tmnomoreuse(int(j), l, k).truthy() {
            tmstore(name, Nil) |> ignore
            tminor(a4, ear_n, k1, subindx, jright)
          } else {
            tmstore(name, tminor(a4, ear_n, k1, subindx, jright))
          }
          let prod = rattimes(aorb, minor, t)
          sum = if j % 2 == 1 {
            ratplus(sum, prod)
          } else {
            ratdifference(sum, prod)
          }
        }
        if symval(q_d_wise).truthy() {
          if tmnomoreuse(int(j), l, k).truthy() {
            tmkill(subindx, k) |> ignore
          }
        }
        j = j + 1
      }
      sum
    }
  })
}

///|
fn extract(index : Value, j : Value) -> Value raise {
  let mut ind = index
  let mut count = 1
  let mut subindx : Value = Nil
  let j = to_int(j)
  while ind.truthy() {
    if count == j {
      return list2(car(ind), nconc(subindx, cdr(ind)))
    } else {
      subindx = nconc(subindx, list1(car(ind)))
    }
    ind = cdr(ind)
    count = count + 1
  }
  Nil
}

///|
/// MAREF1 of trans2.lisp (the translator's array reference), for the cases
/// that arise here.
fn linnew__maref1(ar : Value, inds : Array[Value]) -> Value raise {
  if arrayp(ar) && inds.length() == array_rank(ar) {
    aref(ar, inds.map(i => to_int(i)))
  } else if hash_table_p(ar) {
    gethash(if inds.length() > 1 { list(inds) } else { inds[0] }, ar)
  } else if symbolp(ar) {
    if mget(ar, q_hashar).truthy() {
      harrfind(cons(list2(ar, q_array), list(inds)))
    } else {
      cons(list2(ar, q_array), list(inds))
    }
  } else if inds.length() == 1 &&
    (d_listp(ar).truthy() || d_matrixp(ar).truthy()) {
    nth(to_int(inds[0]), ar)
  } else if d_matrixp(ar).truthy() && inds.length() == 2 {
    nth(to_int(inds[1]), nth(to_int(inds[0]), ar))
  } else {
    merr("Wrong number of array indices: ~M", [cons(list1(q_mlist), list(inds))])
  }
}

///|
fn tmratconv(bbb : Value, ear_n : Value, m : Value) -> Value raise {
  with_specials([(q_ear_n, ear_n), (q_ccc, Nil)], () => {
    set(q_ccc, bbb) |> ignore
    let n = to_int(ear_n)
    let m = to_int(m)
    let a2 = symval(q_ear_a2)
    for k in 1..=n {
      for j in 1..=m {
        let v = linnew__maref1(symval(q_ccc), [int(k), int(j)])
        aset(a2, [k, j], v) |> ignore
        newvar1(v) |> ignore
      }
    }
    newvar(cons(list1(q_mtimes), symval(q_vlist))) |> ignore
    for k in 1..=n {
      for j in 1..=m {
        aset(a2, [k, j], cdr(ratrep_star(aref(a2, [k, j])))) |> ignore
      }
    }
    Nil
  })
}

///|
fn d_tmnewdet(mat : Value, dim? : Value) -> Value raise {
  with_specials([(q_ear_aa, Nil), (q_vlist, Nil), (q_ear_n, Nil)], () => {
    match dim {
      Some(d) => {
        if !integerp(d) {
          merr("tmnewdet: second argument must be an integer; found: ~M", [d])
          |> ignore
        }
        set(q_ear_n, d) |> ignore
      }
      None =>
        if d_matrixp(mat).truthy() {
          set(q_ear_n, int(length(cdr(mat)))) |> ignore
        } else {
          merr("tmnewdet: first argument must be a matrix; found: ~M", [mat])
          |> ignore
        }
    }
    set(q_ear_aa, mat) |> ignore
    let n = linnew__n()
    set(q_ear_a2, make_array([1 + n, 1 + n], initial=Nil)) |> ignore
    tmdefarray(symval(q_ear_n)) |> ignore
    tmratconv(symval(q_ear_aa), symval(q_ear_n), symval(q_ear_n)) |> ignore
    let r = cons(
      list([q_mrat, q_simp, symval(q_varlist), symval(q_genvar)]),
      tmdet(q_ear_a2, symval(q_ear_n)),
    )
    tmrearray(symval(q_ear_n)) |> ignore
    r
  })
}

///|
fn d_tmlinsolve(arglist : Value) -> Value raise {
  with_special(q_ear_aa, Nil, () => {
    let equations = cdar(arglist)
    let mut vars = cdadr(arglist)
    let outvars = if cddr(arglist) is Nil { vars } else { cdaddr(arglist) }
    vars = tmerge(vars, outvars)
    set(q_nx, int(length(outvars))) |> ignore
    set(q_ear_n, int(length(vars))) |> ignore
    if linnew__n() != length(equations) {
      return print(q_too_few_or_much_equations)
    }
    let rows = mapcar(
      exp0 => {
        let mut exp_ = exp0
        let coefs = mapcar(
          v => {
            exp_ = d_bothcoef(exp_, v)
            let r = cadr(exp_)
            exp_ = meval(caddr(exp_))
            r
          },
          vars,
        )
        append_n([
          list1(list1(q_mlist)),
          coefs,
          list1(list2(list1(q_mminus), exp_)),
        ])
      },
      mapcar(
        e => meval(
          list3(
            list1(q_mplus),
            funcall(linnew__q_lhs, [e]),
            list2(list1(q_mminus), funcall(linnew__q_rhs, [e])),
          ),
        ),
        equations,
      ),
    )
    set(q_ear_aa, cons(list2(q_d_matrix, q_simp), rows)) |> ignore
    let mut result = cdr(
      d_tmlin(symval(q_ear_aa), symval(q_ear_n), Fix(1L), symval(q_nx)),
    )
    let mut vars = cons(Nil, outvars)
    let mut labels : Value = Nil
    let mut dlabel : Value = Nil
    while vars.truthy() {
      let name = makelabel(symval(q_d_linechar))
      set(q_d_linenum, num_add(symval(q_d_linenum), Fix(1L))) |> ignore
      set(
        name,
        if car(vars) is Nil {
          dlabel = name
          cadar(result)
        } else {
          list3(
            list1(q_mequal),
            car(vars),
            list3(
              list2(q_mtimes, q_simp),
              cadar(result),
              list3(list2(q_mexpt, q_simp), dlabel, Fix(-1L)),
            ),
          )
        },
      )
      |> ignore
      labels = cons(name, labels)
      result = cdr(result)
      if symval(q_d_dispflag).truthy() {
        mtell_open(
          Str("~M"),
          list1(list3(list1(q_mlabel), name, symbol_value(name))),
        )
        |> ignore
      }
      vars = cdr(vars)
    }
    cons(list1(q_mlist), cdr(reverse(labels)))
  })
}

///|
fn tmerge(vars : Value, outvars : Value) -> Value raise {
  let mut l : Value = Nil
  for v in vars.iter() {
    if !member(v, outvars).truthy() {
      l = cons(v, l)
    }
  }
  append(outvars, reverse(l))
}

///|
/// The SHOW debugging macro of commac.lisp.
fn linnew__show_a2() -> Unit raise {
  format(t, "~%The value of ~A is ~A", [Str("*A2*"), symval(q_ear_a2)])
  |> ignore
}

///|
fn d_tmlin(ear_aa : Value, ear_n : Value, m : Value, nx : Value) -> Value raise {
  with_specials(
    [(q_ear_aa, ear_aa), (q_ear_n, ear_n), (q_nx, nx), (q_vlist, Nil)],
    () => {
      let n = to_int(ear_n)
      set(q_ear_a2, make_array([1 + n, 1 + to_int(m) + n], initial=Nil))
      |> ignore
      linnew__show_a2()
      tmratconv(ear_aa, ear_n, num_add(m, ear_n)) |> ignore
      let r = cons(
        list1(q_mlist),
        mapcar(
          res => cons(
            list1(q_mlist),
            mapcar(
              result => cons(
                list([q_mrat, q_simp, symval(q_varlist), symval(q_genvar)]),
                result,
              ),
              res,
            ),
          ),
          tmlin(q_ear_a2, ear_n, m, nx),
        ),
      )
      linnew__show_a2()
      r
    },
  )
}

///|
fn tmkill(ear_indx : Value, k : Value) -> Value raise {
  with_special(q_ear_indx, ear_indx, () => {
    if ear_indx is Nil {
      return Nil
    }
    let name = tmaccess(ear_indx)
    if tmeval(name).truthy() {
      tmstore(name, Nil) |> ignore
    } else {
      let mut ind = ear_indx
      let mut count = 1
      while ind.truthy() {
        let l = extract(ear_indx, int(count))
        let j = car(l)
        let subindx = cadr(l)
        if num_eq(j, int(count)) {
          tmkill(subindx, one_plus(k)) |> ignore
        }
        ind = cdr(ind)
        count = count + 1
      }
    }
    Nil
  })
}

///|
fn tmnomoreuse(j : Value, l : Value, k : Value) -> Value raise {
  if num_eq(j, l) &&
    (num_gt(k, symval(q_nx)) || num_lt(k, one_plus(symval(q_ix)))) {
    t
  } else {
    Nil
  }
}

///|
fn tmdefarray(ear_n : Value) -> Value raise {
  with_special(q_ear_n, ear_n, () => {
    set(q_ear_tmarrays, get_array_pointer(symval(q_ear_tmarrays))) |> ignore
    if symval(q_ear_tmarrays).truthy() {
      let d = cadr(arraydims(symval(q_ear_tmarrays)))
      tmrearray(one_minus(if d.truthy() { d } else { Fix(1L) })) |> ignore
    }
    let n = to_int(ear_n)
    set(q_ear_tmarrays, make_array([1 + n], initial=Nil)) |> ignore
    for i in 1..=n {
      let name = if i == 1 { make_symbol("M") } else { gensym() }
      if n < linnew__threshold() {
        set(
          name,
          make_array([1 + to_int(tmcombi(ear_n, int(i)))], initial=Nil),
        )
        |> ignore
        aset1(symval(q_ear_tmarrays), i, get_array_pointer(name)) |> ignore
      } else {
        aset1(symval(q_ear_tmarrays), i, list3(name, q_simp, q_array)) |> ignore
      }
    }
    gensym(prefix="G")
  })
}

///|
/// TMREARRAY kills the TMARRAYS which holds pointers to minors. If
/// (TMARRAYS I) is an atom, it is declared array. Otherwise it is hashed
/// array.
fn tmrearray(ear_n : Value) -> Value raise {
  for i in 1..=to_int(ear_n) {
    let a = aref1(symval(q_ear_tmarrays), i)
    if !atom(a) {
      tm_dolkill(car(a)) |> ignore
    }
  }
  Nil
}

///|
fn tmaccess(index : Value) -> Value raise {
  if symval(q_d_fool).truthy() {
    return Nil
  }
  let l = length(index)
  let n = linnew__n()
  if n < linnew__threshold() {
    let mut sum : Value = Fix(0L)
    let mut x = 0
    let mut y = index
    for i in 1..=l {
      let mut j = x + 1
      while j != to_int(car(y)) {
        sum = num_add(sum, tmcombi(int(n - j), int(l - i)))
        j = j + 1
      }
      x = to_int(car(y))
      y = cdr(y)
    }
    list3(q_aref, aref1(symval(q_ear_tmarrays), l), one_plus(sum))
  } else {
    cons(q_aref, cons(aref1(symval(q_ear_tmarrays), l), index))
  }
}

///|
fn tmcombi(ear_n : Value, i : Value) -> Value raise {
  let d = num_sub(ear_n, i)
  if num_gt(d, i) {
    num_div(tmfactorial(ear_n, d), tmfactorial(i, Fix(0L)))
  } else {
    num_div(tmfactorial(ear_n, i), tmfactorial(d, Fix(0L)))
  }
}

///|
fn tmfactorial(i : Value, j : Value) -> Value raise {
  if num_eq(i, j) {
    Fix(1L)
  } else {
    num_mul(i, tmfactorial(one_minus(i), j))
  }
}

///|
/// `(eval '(aref <array> <index>))` for the access forms built by TMACCESS
/// below the threshold.
fn linnew__eval_access(e : Value) -> Value raise {
  if e is Nil {
    Nil
  } else {
    aref1(cadr(e), to_int(caddr(e)))
  }
}

///|
fn tmstore(name : Value, x : Value) -> Value raise {
  if linnew__n() < linnew__threshold() {
    // (eval `(setf ,name ',x))
    aset1(cadr(name), to_int(caddr(name)), x)
  } else {
    mset(name, list2(list2(q_mquote, q_simp), x)) |> ignore
    x
  }
}

///|
/// TMKILLARRAY kills all (N-IX+1)*(N-IX+1) minors which are not necessary
/// for the computation of IX-TH variable in the linear equation. Otherwise,
/// they will do harm.
fn tmkillarray(ix : Value) -> Value raise {
  with_special(q_ix, ix, () => {
    let n = linnew__n()
    for i in (1 + (n - to_int(ix)))..=n {
      if n < linnew__threshold() {
        fillarray(aref1(symval(q_ear_tmarrays), i), list1(Nil)) |> ignore
      } else {
        tm_dolkill(car(aref1(symval(q_ear_tmarrays), i))) |> ignore
      }
    }
    Nil
  })
}

///|
fn tmeval(e : Value) -> Value raise {
  if linnew__n() < linnew__threshold() {
    linnew__eval_access(e)
  } else {
    let result = meval(e)
    if equal(result, e) {
      Nil
    } else {
      cadr(result)
    }
  }
}

///|
fn tm_dolkill(e : Value) -> Value raise {
  kill1(e)
}

///|
fn d_tminverse(ear_aa : Value) -> Value raise {
  with_specials(
    [(q_ear_aa, ear_aa), (q_vlist, Nil), (q_ear_n, Nil), (q_nx, Nil)],
    () => {
      let n = length(cdr(ear_aa))
      set(q_ear_n, int(n)) |> ignore
      let m = n
      set(q_nx, int(n)) |> ignore
      set(q_ear_a2, make_array([1 + n, 1 + m + n], initial=Nil)) |> ignore
      tmratconv(ear_aa, int(n), int(n)) |> ignore
      let one = cons(Fix(1L), Fix(1L))
      let zero = linnew__zero_rat()
      for i in 1..=n {
        for j in 1..=m {
          aset(symval(q_ear_a2), [i, n + j], if i == j { one } else { zero })
          |> ignore
        }
      }
      let r = mapcar(
        res => cons(
          list1(q_mlist),
          mapcar(
            result => d_ratdisrep(
              cons(
                list([q_mrat, q_simp, symval(q_varlist), symval(q_genvar)]),
                result,
              ),
            ),
            res,
          ),
        ),
        tmlin(q_ear_a2, int(n), int(m), symval(q_nx)),
      )
      list3(
        list2(q_mtimes, q_simp),
        list3(list2(q_mexpt, q_simp), cadar(r), Fix(-1L)),
        cons(list2(q_d_matrix, q_simp), cdr(r)),
      )
    },
  )
}

// TMPIVOT-ISOLATE CARRIES OUT PIVOTING SO THAT THE ALL DIAGONAL ELEMENTS ARE
// NONZERO. THIS GUARANTEES WE HAVE MAXIMUM NUMBER OF BLOCKS ISOLATED.

///|
fn linnew__rc(s : Value, i : Value) -> Value raise {
  aref1(symval(s), to_int(i))
}

///|
/// `(aref *b* (aref *row* i) (aref *col* j))`
fn linnew__b(i : Value, j : Value) -> Value raise {
  linnew__aref2(symval(q_ear_b), linnew__rc(q_ear_row, i), linnew__rc(q_ear_col, j))
}

///|
fn linnew__set_b(i : Value, j : Value, v : Value) -> Unit raise {
  linnew__aset2(
    symval(q_ear_b),
    linnew__rc(q_ear_row, i),
    linnew__rc(q_ear_col, j),
    v,
  )
}

///|
fn tmpivot_isolate(k : Value) -> Value raise {
  let n = linnew__n()
  if to_int(k) > n {
    t
  } else {
    for i in to_int(k)..=n {
      if linnew__b(int(i), k).truthy() {
        tmexchange(q_ear_row, k, int(i)) |> ignore
        if tmpivot_isolate(one_plus(k)).truthy() {
          return t
        } else {
          tmexchange(q_ear_row, k, int(i)) |> ignore
        }
      }
    }
    Nil
  }
}

///|
fn tmexchange(rowcol : Value, i : Value, j : Value) -> Value raise {
  let rowcol = get_array_pointer(rowcol)
  let i = to_int(i)
  let j = to_int(j)
  let dummy = aref1(rowcol, i)
  aset1(rowcol, i, aref1(rowcol, j)) |> ignore
  aset1(rowcol, j, dummy) |> ignore
  Nil
}

///|
/// TMPERMUTE PERMUTES THE ROWS OR COLUMNS OF THE N*M MATRIX AX ACCORDING TO
/// THE SPECIFICATION OF INDEXLIST. THE FLAG MUST BE SET 'ROW IF ROW
/// PERMUTATION IS DESIRED, OR 'COL OTHERWISE. THE RESULT IS IN AX. NM IS THE
/// DIMENSION OF INDEXLIST.
fn tmpermute(
  ax : Value,
  ear_n : Value,
  m : Value,
  rbias : Value,
  cbias : Value,
  indexlist : Value,
  nm : Value,
  flag : Value,
) -> Value raise {
  let ax = get_array_pointer(ax)
  let indexlist = get_array_pointer(indexlist)
  let nm = to_int(nm)
  // (setf (symbol-array *indx*) (make-array (1+ nm) :initial-element nil))
  setf_get(symbol_value(q_ear_indx), q_array, make_array([1 + nm], initial=Nil))
  |> ignore
  for i in 1..=nm {
    aset1(symbol_value(q_ear_indx), i, aref1(indexlist, i)) |> ignore
  }
  for i in 1..=nm {
    if to_int(aref1(symval(q_ear_indx), i)) != i {
      tmmove(ax, ear_n, m, rbias, cbias, int(i), Fix(0L), flag) |> ignore
      let mut l = i
      while true {
        let k = to_int(aref1(symval(q_ear_indx), l))
        aset1(symval(q_ear_indx), l, int(l)) |> ignore
        if k == i {
          tmmove(ax, ear_n, m, rbias, cbias, Fix(0L), int(l), flag) |> ignore
          break
        } else {
          tmmove(ax, ear_n, m, rbias, cbias, int(k), int(l), flag) |> ignore
          l = k
        }
      }
    }
  }
  Nil
}

///|
fn tmmove(
  ax : Value,
  ear_n : Value,
  m : Value,
  rbias : Value,
  cbias : Value,
  i : Value,
  j : Value,
  flag : Value,
) -> Value raise {
  let ax = get_array_pointer(ax)
  let rb = to_int(rbias)
  let cb = to_int(cbias)
  let i = to_int(i)
  let j = to_int(j)
  let ll = if eq(flag, q_ear_row) {
    to_int(m) - cb
  } else {
    to_int(ear_n) - rb
  }
  for k in 1..=ll {
    if eq(flag, q_ear_row) {
      aset(ax, [rb + j, cb + k], aref(ax, [rb + i, cb + k])) |> ignore
    } else {
      aset(ax, [rb + k, cb + j], aref(ax, [rb + k, cb + i])) |> ignore
    }
  }
  Nil
}

///|
/// TMSYMETRICP CHECKS THE SYMMETRY OF THE MATRIX.
fn tmsymetricp(a3 : Value, ear_n : Value) -> Value raise {
  let a3 = get_array_pointer(a3)
  let n = to_int(ear_n)
  for i in 1..=n {
    for j in (i + 1)..=n {
      if !equal(aref(a3, [i, j]), aref(a3, [j, i])) {
        return Nil
      }
    }
  }
  t
}

///|
/// TMLATTICE CHECKS THE "LATTICE" STRUCTURE OF THE MATRIX A. IT RETURNS NIL
/// IF THE MATRIX IS "OBVIOUSLY" SINGULAR. OTHERWISE IT RETURNS A LIST
/// (L1 L2 ... LM) WHERE M IS THE NUMBER OF BLOCKS (STRONGLY CONNECTED
/// SUBGRAPHS), AND L1 L2 ... ARE LIST OF ROW AND COLUMN NUMBERS WHICH BELONG
/// TO EACH BLOCKS. THE LIST LOOKS LIKE ((R1 C1) (R2 C2) ...).
fn tmlattice(a3 : Value, xrow : Value, xcol : Value, ear_n : Value) -> Value raise {
  with_special(q_ear_n, ear_n, () => {
    let a3 = get_array_pointer(a3)
    let xrow = get_array_pointer(xrow)
    let xcol = get_array_pointer(xcol)
    let n = to_int(ear_n)
    set(q_ear_b, make_array([1 + n, 1 + n], initial=Nil)) |> ignore
    set(q_ear_row, make_array([1 + n], initial=Nil)) |> ignore
    set(q_ear_col, make_array([1 + n], initial=Nil)) |> ignore
    for i in 1..=n {
      for j in 1..=n {
        aset(
          symval(q_ear_b),
          [i, j],
          lbool(!equal(aref(a3, [i, j]), linnew__zero_rat())),
        )
        |> ignore
      }
    }
    for i in 0..=n {
      aset1(symval(q_ear_row), i, int(i)) |> ignore
      aset1(symval(q_ear_col), i, int(i)) |> ignore
    }
    if tmpivot_isolate(Fix(1L)) is Nil {
      return Nil
    }
    for i in 1..=n {
      linnew__set_b(int(i), int(i), int(i))
      linnew__set_b(int(i), Fix(0L), t)
    }
    tmlattice1(Fix(1L)) |> ignore
    tmsort_lattice(xrow, xcol)
  })
}

///|
fn tmlattice1(k : Value) -> Value raise {
  if to_int(k) == linnew__n() {
    Nil
  } else {
    tmlattice1(one_plus(k)) |> ignore
    while true {
      let looppath = tmpathp(k, k)
      if looppath.truthy() {
        tmunify_loop(k, cdr(looppath)) |> ignore
      } else {
        return Nil
      }
    }
    Nil
  }
}

///|
fn tmpathp(j : Value, k : Value) -> Value raise {
  if equal(linnew__b(j, k), t) {
    list2(j, k)
  } else {
    for jj in to_int(k)..=linnew__n() {
      if equal(linnew__b(j, int(jj)), t) {
        let path = tmpathp(int(jj), k)
        if path.truthy() {
          return cons(j, path)
        }
      }
    }
    Nil
  }
}

///|
fn tmunify_loop(k : Value, chain : Value) -> Value raise {
  let l = car(chain)
  if num_eq(l, k) {
    return Nil
  }
  let dummyk = linnew__b(k, k)
  let dummyl = linnew__b(l, l)
  linnew__set_b(k, k, Nil)
  linnew__set_b(l, l, Nil)
  for i in 1..=linnew__n() {
    let iv = int(i)
    let a = linnew__b(k, iv)
    linnew__set_b(k, iv, if a.truthy() { a } else { linnew__b(l, iv) })
    let b = linnew__b(iv, k)
    linnew__set_b(iv, k, if b.truthy() { b } else { linnew__b(iv, l) })
    linnew__set_b(l, iv, Nil)
    linnew__set_b(iv, l, Nil)
  }
  linnew__set_b(k, k, dummyl)
  linnew__set_b(l, l, dummyk)
  linnew__set_b(k, Fix(0L), t)
  linnew__set_b(l, Fix(0L), Nil)
  tmunify_loop(k, cdr(chain))
}

///|
fn tmsort_lattice(xrow : Value, xcol : Value) -> Value raise {
  let nodelist = tmsort1()
  let mut result : Value = Nil
  for x in nodelist.iter() {
    let mut next = linnew__b(x, x)
    let mut res : Value = Nil
    while !num_eq(next, x) {
      res = cons(
        list2(linnew__rc(q_ear_row, next), linnew__rc(q_ear_col, next)),
        res,
      )
      next = linnew__b(next, next)
    }
    res = cons(
      list2(linnew__rc(q_ear_row, next), linnew__rc(q_ear_col, next)),
      res,
    )
    result = cons(res, result)
  }
  let mut i = 1
  for l1 in result.iter() {
    for l2 in l1.iter() {
      aset1(xrow, i, car(l2)) |> ignore
      aset1(xcol, i, cadr(l2)) |> ignore
      i = i + 1
    }
  }
  result
}

///|
fn tmsort1() -> Value raise {
  let mut result : Value = Nil
  let mut i = 1
  while i <= linnew__n() {
    if linnew__b(int(i), Fix(0L)).truthy() && tmmaxp(int(i)).truthy() {
      for j in 1..=linnew__n() {
        if j != i {
          linnew__set_b(int(i), int(j), Nil)
        }
      }
      linnew__set_b(int(i), Fix(0L), Nil)
      result = cons(int(i), result)
      i = 0
    }
    i = i + 1
  }
  result
}

///|
fn tmmaxp(i : Value) -> Value raise {
  for j in 1..=linnew__n() {
    if to_int(i) != j && linnew__b(int(j), i).truthy() {
      return Nil
    }
  }
  t
}

///|
/// UNPIVOT IS USED IN PAUL WANG'S PROGRAM TO RECOVER THE PIVOTING. GIVEN A
/// MATRIX A3, INDEX ROW AND COL, WHICH CORRESPOND TO Y, U AND V, IT COMPUTES
/// V*Y*U AND RETURNS IT TO THE SAME ARGUMENT A.
fn tmunpivot(
  a3 : Value,
  ear_row : Value,
  ear_col : Value,
  ear_n : Value,
  m : Value,
) -> Value raise {
  with_specials(
    [(q_ear_row, ear_row), (q_ear_col, ear_col), (q_ear_n, ear_n)],
    () => {
      set(q_ear_col, get_array_pointer(symval(q_ear_col))) |> ignore
      set(q_ear_row, get_array_pointer(symval(q_ear_row))) |> ignore
      let n = to_int(ear_n)
      set(q_ear_rowinv, make_array([1 + n], initial=Nil)) |> ignore
      set(q_ear_colinv, make_array([1 + n], initial=Nil)) |> ignore
      for i in 1..=n {
        aset1(
          symval(q_ear_rowinv),
          to_int(aref1(symval(q_ear_row), i)),
          int(i),
        )
        |> ignore
      }
      for i in 1..=n {
        aset1(
          symval(q_ear_colinv),
          to_int(aref1(symval(q_ear_col), i)),
          int(i),
        )
        |> ignore
      }
      tmpermute(a3, ear_n, m, Fix(0L), ear_n, q_ear_colinv, ear_n, q_ear_row)
      |> ignore
      tmpermute(a3, ear_n, m, Fix(0L), ear_n, q_ear_rowinv, ear_n, q_ear_col)
      |> ignore
      Nil
    },
  )
}
