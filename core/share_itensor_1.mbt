// Port of share/tensor/itensor.lisp (indicial tensor manipulation), part 1:
// indexed objects (RPOBJs), contraction properties, metric and Christoffel
// symbols, covariant and Lie derivatives, CONTRACT and the Kronecker delta.
//
// The Lisp file keeps a few variables in closures shared by two functions
// ((let (temp x d) (defmfun $covdiff ..) (defun covdiff ..)) and
// (let (dumx) (defun itensor-cleanup ..) (defun cleanup1 ..))); those are
// file-private refs here.

///|
/// The value of the special SMLIST, `(mlist simp)`.
fn share_itensor__sm() -> Value {
  symval(q_smlist)
}

///|
/// `(cons smlist l)`
fn share_itensor__ml(l : Value) -> Value {
  cons(symval(q_smlist), l)
}

///|
/// A fresh `((mlist simp))`.
fn share_itensor__empty_ml() -> Value {
  list1(list2(q_mlist, q_simp))
}

///|
/// `(list '(mlist simp) items...)`
fn share_itensor__msl(items : Array[Value]) -> Value {
  cons(list2(q_mlist, q_simp), list(items))
}

///|
/// `(list '(mlist) items...)`
fn share_itensor__mlist(items : Array[Value]) -> Value {
  cons(list1(q_mlist), list(items))
}

///|
/// `(list '(mtimes simp) -1 x)`: the new-style lowered index -x.
fn share_itensor__neg_index(x : Value) -> Value {
  list3(list2(q_mtimes, q_simp), Fix(-1L), x)
}

///|
/// `(cons $imetric '(simp))`: the header of a metric tensor.
fn share_itensor__metric_head() -> Value {
  list2(symval(q_d_imetric), q_simp)
}

///|
/// `(list (cons $imetric '(simp)) cov con derivs...)`
fn share_itensor__metric(cov : Value, con : Value, derivs : Array[Value]) -> Value {
  list_star([share_itensor__metric_head(), cov, con, list(derivs)])
}

///|
/// `(list '(%kdelta simp) (list '(mlist simp) a) (list '(mlist simp) b))`
fn share_itensor__kd1(a : Value, b : Value) -> Value {
  list3(
    list2(q_p_kdelta, q_simp),
    share_itensor__msl([a]),
    share_itensor__msl([b]),
  )
}

///|
/// `(numberp x)` and `(< x 0)`
fn share_itensor__negnump(x : Value) -> Bool raise {
  numberp(x) && num_lt(x, Fix(0L))
}

///|
/// The Lisp `less` as a sort predicate.
fn share_itensor__less_p(x : Value, y : Value) -> Bool raise {
  less(x, y).truthy()
}

///|
/// `(position item seq)` on a list or a vector with a fill pointer.
fn share_itensor__seq_position(item : Value, s : Value) -> Value raise {
  match s {
    Vec(_) => {
      let n = fill_pointer(s)
      for i in 0..<n {
        if eql(item, aref1(s, i)) {
          return int(i)
        }
      }
      Nil
    }
    _ => {
      let p = position(item, s)
      if p < 0 {
        Nil
      } else {
        int(p)
      }
    }
  }
}

///|
/// `($canform e)` through the function cell (symtry is autoloaded).
fn share_itensor__canform(e : Value) -> Value raise {
  funcall(q_d_canform, [e])
}

///|
/// macro (ifnot &rest clause) = `(or ,@clause)`
fn ifnot(clause : Value) -> Value raise {
  for c in clause.iter() {
    if c.truthy() {
      return c
    }
  }
  Nil
}

///|
/// Sets arguments to dummy indices
fn d_idummy() -> Value raise {
  set(q_d_icounter, one_plus(symval(q_d_icounter))) |> ignore
  sym(
    format_to_string("~a~d", [symval(q_d_idummyx), symval(q_d_icounter)]),
  )
}

///|
fn isprod(x : Value) -> Value raise {
  lbool(
    equal(x, list1(q_mtimes)) ||
    equal(x, list2(q_mtimes, q_simp)) ||
    equal(x, list3(q_mtimes, q_simp, q_ratsimp)),
  )
}

///|
/// Remove occurrences of ratsimp from elements of x
fn derat(x : Value) -> Value raise {
  if x is Nil {
    Nil
  } else if atom(x) {
    x
  } else if eq(car(x), q_ratsimp) {
    derat(cdr(x))
  } else {
    cons(derat(car(x)), derat(cdr(x)))
  }
}

///|
fn plusi(l : Value) -> Value raise {
  if l is Nil {
    l
  } else if share_itensor__negnump(car(l)) {
    plusi(cdr(l))
  } else if atom(car(l)) {
    cons(car(l), plusi(cdr(l)))
  } else if isprod(caar(l)).truthy() && eql(cadar(l), Fix(-1L)) {
    plusi(cdr(l))
  } else {
    cons(car(l), plusi(cdr(l)))
  }
}

///|
fn minusi(l : Value) -> Value raise {
  if l is Nil {
    l
  } else if share_itensor__negnump(car(l)) {
    cons(neg(car(l)), plusi(cdr(l)))
  } else if atom(car(l)) {
    minusi(cdr(l))
  } else if isprod(caar(l)).truthy() && eql(cadar(l), Fix(-1L)) {
    cons(caddar(l), minusi(cdr(l)))
  } else {
    minusi(cdr(l))
  }
}

///|
fn covi(rp : Value) -> Value raise {
  plusi(cdadr(rp))
}

///|
fn conti(rp : Value) -> Value raise {
  append(minusi(cdadr(rp)), cdaddr(rp))
}

///|
fn deri(rp : Value) -> Value raise {
  cdddr(rp)
}

///|
fn name(rp : Value) -> Value raise {
  caar(rp)
}

///|
fn d_covi(rp : Value) -> Value raise {
  if rpobj(rp).truthy() {
    share_itensor__ml(covi(rp))
  } else {
    merr("Not an RPOBJ", [])
  }
}

///|
fn d_conti(rp : Value) -> Value raise {
  if rpobj(rp).truthy() {
    share_itensor__ml(conti(rp))
  } else {
    merr("Not an RPOBJ", [])
  }
}

///|
fn d_deri(rp : Value) -> Value raise {
  if rpobj(rp).truthy() {
    share_itensor__ml(deri(rp))
  } else {
    merr("Not an RPOBJ", [])
  }
}

///|
fn d_name(rp : Value) -> Value raise {
  if rpobj(rp).truthy() {
    caar(rp)
  } else {
    merr("Not an RPOBJ", [])
  }
}

///|
/// Defines contractions: A contracts with B to form C
fn d_defcon(n : Value) -> Value raise {
  let nargs = length(n)
  let a = nth(0, n)
  add2lnc(a, symval(q_d_contractions)) |> ignore
  let c = if nargs == 1 {
    cons(q_op_sp, q_op_sp)
  } else if nargs == 3 {
    cons(nth(1, n), nth(2, n))
  } else {
    merr("DEFCON takes 1 or 3 arguments", [])
  }
  putprop(a, cons(c, zl_get(a, q_contractions)), q_contractions) |> ignore
  q_d_done
}

///|
/// Displays contraction definitions
fn d_dispcon(a : Value) -> Value raise {
  let mut a = cdr(a)
  if eq(car(a), q_d_all) {
    a = cdr(symval(q_d_contractions))
  }
  share_itensor__ml(
    mapcar(
      e => {
        let tmp = zl_get(e, q_contractions)
        if tmp.truthy() {
          share_itensor__ml(
            mapcar(
              z => if eq(car(z), q_op_sp) {
                list2(share_itensor__sm(), e)
              } else {
                list4(share_itensor__sm(), e, car(z), cdr(z))
              },
              tmp,
            ),
          )
        } else {
          share_itensor__empty_ml()
        }
      },
      a,
    ),
  )
}

///|
/// Removes contraction definitions
fn d_remcon(a : Value) -> Value raise {
  let mut a = cdr(a)
  if eq(car(a), q_d_all) {
    a = cdr(symval(q_d_contractions))
  }
  share_itensor__ml(
    mapc(
      e => {
        zl_remprop(e, q_contractions) |> ignore
        set(q_d_contractions, delete(e, symval(q_d_contractions))) |> ignore
      },
      a,
    ),
  )
}

///|
/// Helper to obtain contractions on both the noun and verb form of E
fn getcon(e : Value) -> Value raise {
  if symbolp(e) && eql(get_first_char(e), Char('%')) {
    zl_get(d_verbify(e), q_contractions)
  } else {
    zl_get(e, q_contractions)
  }
}

///|
/// "True" if an indexed object and not a matrix. In the case of no
/// contravariant components, it tacks a null list on (F([...]) becomes
/// F([...],[])).
fn rpobj(e : Value) -> Value raise {
  if !atom(e) && eq(caar(e), q_mqapply) {
    rpobj(cdr(e))
  } else if !atom(e) && !eq(caar(e), q_d_matrix) && d_listp(cadr(e)).truthy() {
    if cddr(e).truthy() {
      d_listp(caddr(e))
    } else {
      nconc(e, list1(share_itensor__empty_ml())) |> ignore
      t
    }
  } else {
    Nil
  }
}

///|
fn d_imetric(v : Value) -> Value raise {
  set(q_d_imetric, v) |> ignore
  d_defcon(list1(v)) |> ignore
  d_defcon(list3(v, v, q_d_kdelta))
}

///|
/// To reuse subparts of old expression
fn mysubst0(new_ : Value, old : Value) -> Value raise {
  if alike1(new_, old).truthy() {
    old
  } else {
    new_
  }
}

///|
/// COV gives covariant form of metric
fn cov(a : Value, b : Value) -> Value raise {
  if boundp(q_d_imetric) {
    meval(
      list3(
        list1(symval(q_d_imetric)),
        share_itensor__ml(list2(a, b)),
        share_itensor__empty_ml(),
      ),
    )
  } else {
    merr("Name of metric must be specified", [])
  }
}

///|
/// contr gives contravariant form of metric
fn contr(a : Value, b : Value) -> Value raise {
  if boundp(q_d_imetric) {
    meval(
      list3(
        list1(symval(q_d_imetric)),
        share_itensor__empty_ml(),
        share_itensor__ml(list2(a, b)),
      ),
    )
  } else {
    merr("Name of metric must be specified", [])
  }
}

///|
fn diffcov(a : Value, b : Value, d : Value) -> Value raise {
  if boundp(q_d_imetric) {
    meval(
      list4(
        list1(symval(q_d_imetric)),
        share_itensor__ml(list2(a, b)),
        share_itensor__empty_ml(),
        d,
      ),
    )
  } else {
    merr("Name of metric must be specified", [])
  }
}

///|
/// `(apply #'append (mapcar #'(lambda (e) (list e 1)) l))`
fn share_itensor__deriv_pairs(l : Value) -> Value {
  let c = Collector::new()
  for e in l.iter() {
    c.add(e)
    c.add(Fix(1L))
  }
  c.result()
}

///|
/// Christoffel-symbol of the first kind
fn d_ichr1(nargs : Value) -> Value raise {
  let n = length(nargs)
  if n > 2 {
    // Derivative indices present; use idiff() to resolve
    return meval(
      cons(
        q_d_idiff,
        cons(
          d_ichr1(list2(nth(0, nargs), nth(1, nargs))),
          share_itensor__deriv_pairs(cddr(nargs)),
        ),
      ),
    )
  }
  if n > 1 {
    if length(nth(1, nargs)) == 1 {
      return d_ichr1(list1(nth(0, nargs)))
    }
    return merr("ichr1 cannot have contravariant indices", [])
  }
  // G_abc = 1/2*(g_ba,c+g_ca,b-g_bc,a)
  let a1 = nth(0, nargs)
  let a = cadddr(a1)
  let b = cadr(a1)
  let c = caddr(a1)
  list3(
    list1(q_mtimes),
    list3(list2(q_rat, q_simp), Fix(1L), Fix(2L)),
    list4(
      list1(q_mplus),
      diffcov(b, a, c),
      diffcov(c, a, b),
      list3(list1(q_mtimes), Fix(-1L), diffcov(b, c, a)),
    ),
  )
}

///|
/// Christoffel-symbol of the second kind
fn d_ichr2(nargs : Value) -> Value raise {
  let n = length(nargs)
  if n > 2 {
    // Derivative indices present; use idiff() to resolve
    return meval(
      cons(
        q_d_idiff,
        cons(
          d_ichr2(list2(nth(0, nargs), nth(1, nargs))),
          share_itensor__deriv_pairs(cddr(nargs)),
        ),
      ),
    )
  }
  // G_ab^c=g^cd*G_abd
  let a1 = nth(0, nargs)
  let a2 = nth(1, nargs)
  let a = cadr(a1)
  let b = caddr(a1)
  let c = cadr(a2)
  let l = append(cdr(a1), cdr(a2))
  let mut d : Value = Nil
  let mut flag = false
  while !flag {
    d = d_idummy()
    if member(d, l) is Nil {
      flag = true
    }
  }
  list3(
    list1(q_mtimes),
    contr(c, d),
    d_ichr1(list1(share_itensor__ml(list3(a, b, d)))),
  )
}

///|
fn d_icurvature(l1 : Value, l2 : Value) -> Value raise {
  let r = d_idummy()
  let i = cadr(l1)
  let k = caddr(l1)
  let h = cadddr(l1)
  let j = cadr(l2)
  list([
    list1(q_mplus),
    idiff(list3(diffop(), share_itensor__ml(list2(i, k)), l2), h),
    list3(
      list1(q_mtimes),
      Fix(-1L),
      idiff(
        list3(
          diffop(),
          share_itensor__ml(list2(i, h)),
          share_itensor__ml(list1(j)),
        ),
        k,
      ),
    ),
    list3(
      list1(q_mtimes),
      list3(
        diffop(),
        share_itensor__ml(list2(i, k)),
        share_itensor__ml(list1(r)),
      ),
      list3(diffop(), share_itensor__ml(list2(r, h)), l2),
    ),
    list4(
      list1(q_mtimes),
      Fix(-1L),
      list3(
        diffop(),
        share_itensor__ml(list2(i, h)),
        share_itensor__ml(list1(r)),
      ),
      list3(diffop(), share_itensor__ml(list2(r, k)), l2),
    ),
    if symval(q_d_iframe_flag).truthy() {
      list4(
        list1(q_mtimes),
        Fix(-1L),
        list3(
          list1(q_d_ifb),
          share_itensor__ml(list2(k, h)),
          share_itensor__ml(list1(r)),
        ),
        list3(
          list1(q_d_icc2),
          share_itensor__ml(list2(r, i)),
          share_itensor__ml(list1(j)),
        ),
      )
    } else {
      Fix(0L)
    },
  ])
}

///|
/// Substitutes X for Y in the covariant part of RP
fn covsubst(x : Value, y : Value, rp : Value) -> Value raise {
  cons(car(rp), cons(subst(x, y, d_covi(rp)), cons(d_conti(rp), cdddr(rp))))
}

///|
/// Substitutes X for Y in the contravariant part of RP
fn consubst(x : Value, y : Value, rp : Value) -> Value raise {
  cons(car(rp), cons(d_covi(rp), cons(subst(x, y, d_conti(rp)), cdddr(rp))))
}

///|
/// Substitutes X for Y in the derivative indices of RP
fn dersubst(x : Value, y : Value, rp : Value) -> Value raise {
  nconc(list3(car(rp), cadr(rp), caddr(rp)), subst(x, y, cdddr(rp)))
}

///|
/// ichr2 or icc2 depending on iframe_flag
fn diffop() -> Value raise {
  if symval(q_d_iframe_flag).truthy() ||
    symval(q_d_itorsion_flag).truthy() ||
    symval(q_d_inonmet_flag).truthy() {
    list2(q_d_icc2, q_simp)
  } else {
    list2(q_d_ichr2, q_simp)
  }
}

///|
fn d_idiff(args : Value) -> Value raise {
  with_special(q_derivlist, Nil, () => ideriv(args))
}

// COVARIANT DIFFERENTIATION
// COVDIFF takes into account the value of iframe_flag. If true, COVDIFF
// uses the coefficients icc2 in place of the Christoffel-symbols ichr2.

///|
/// The closure variables TEMP, X and D shared by $COVDIFF and COVDIFF.
let share_itensor__cd_temp : Ref[Value] = Ref(Nil)

///|
let share_itensor__cd_x : Ref[Value] = Ref(Nil)

///|
let share_itensor__cd_d : Ref[Value] = Ref(Nil)

///|
fn d_covdiff(nargs : Value) -> Value raise {
  let n = length(nargs)
  if n < 2 {
    merr("COVDIFF must have at least 2 args", []) |> ignore
  }
  share_itensor__cd_temp.val = Nil
  share_itensor__cd_d.val = Nil
  let mut i = 2
  let mut e = nth(0, nargs)
  while true {
    share_itensor__cd_x.val = nth(i - 1, nargs)
    e = covdiff(e)
    i = i + 1
    if i > n {
      return e
    }
  }
  e
}

///|
/// The covariant derivative...
fn covdiff(e : Value) -> Value raise {
  share_itensor__cd_d.val = d_idummy()
  if atom(e) || eq(caar(e), q_rat) {
    // is the partial derivative for scalars
    idiff(e, share_itensor__cd_x.val)
  } else if rpobj(e).truthy() {
    share_itensor__cd_temp.val = mapcar(
      v => list3(
        list1(q_mtimes),
        list3(
          diffop(),
          share_itensor__ml(
            list2(share_itensor__cd_d.val, share_itensor__cd_x.val),
          ),
          share_itensor__ml(list1(v)),
        ),
        consubst(share_itensor__cd_d.val, v, e),
      ),
      conti(e),
    )
    let first = idiff(e, share_itensor__cd_x.val)
    let rest = if covi(e).truthy() || cdddr(e).truthy() {
      let l1 = mapcar(
        v => list3(
          list1(q_mtimes),
          list3(
            diffop(),
            share_itensor__ml(list2(v, share_itensor__cd_x.val)),
            share_itensor__ml(list1(share_itensor__cd_d.val)),
          ),
          covsubst(share_itensor__cd_d.val, v, e),
        ),
        covi(e),
      )
      let l2 = mapcar(
        v => list3(
          list1(q_mtimes),
          list3(
            diffop(),
            share_itensor__ml(list2(v, share_itensor__cd_x.val)),
            share_itensor__ml(list1(share_itensor__cd_d.val)),
          ),
          dersubst(share_itensor__cd_d.val, v, e),
        ),
        cdddr(e),
      )
      cons(
        list3(list1(q_mtimes), Fix(-1L), cons(list1(q_mplus), nconc(l1, l2))),
        share_itensor__cd_temp.val,
      )
    } else {
      share_itensor__cd_temp.val
    }
    simplus(cons(list1(q_mplus), cons(first, rest)), Fix(1L), t)
  } else if eq(caar(e), q_mtimes) {
    // (a*b)'
    simplus(covdifftimes(cdr(e), share_itensor__cd_x.val), Fix(1L), t)
  } else if eq(caar(e), q_mplus) {
    // (a+b)'=a'+b'
    simplifya(cons(list1(q_mplus), mapcar(v => covdiff(v), cdr(e))), Nil)
  } else if eq(caar(e), q_mexpt) {
    // (a^b)'=b*a^(b-1)*a'
    simptimes(
      list4(
        list1(q_mtimes),
        caddr(e),
        list3(
          list1(q_mexpt),
          cadr(e),
          list3(list1(q_mplus), Fix(-1L), caddr(e)),
        ),
        d_covdiff(list2(cadr(e), share_itensor__cd_x.val)),
      ),
      Fix(1L),
      Nil,
    )
  } else if eq(caar(e), q_mequal) {
    let a = covdiff(cadr(e))
    list3(car(e), a, covdiff(caddr(e)))
  } else if eq(caar(e), q_p_determinant) && eq(cadr(e), symval(q_d_imetric)) {
    if symval(q_d_iframe_flag).truthy() ||
      symval(q_d_itorsion_flag).truthy() ||
      symval(q_d_inonmet_flag).truthy() {
      let d1 = d_idummy()
      let d2 = d_idummy()
      let x = share_itensor__cd_x.val
      let g = list3(
        share_itensor__metric_head(),
        share_itensor__msl([d1, d2]),
        share_itensor__empty_ml(),
      )
      simptimes(
        list4(
          list1(q_mtimes),
          e,
          list3(
            share_itensor__metric_head(),
            share_itensor__empty_ml(),
            share_itensor__msl([d1, d2]),
          ),
          if share_itensor__seq_position(
              q_d_extdiff,
              symval(q_ear_mlambda_call_stack),
            ).truthy() {
            // Special case, we're in extdiff()
            d_idiff(list2(g, x))
          } else {
            d_covdiff(list2(g, x))
          },
        ),
        Fix(1L),
        t,
      )
    } else {
      Fix(0L)
    }
  } else {
    merr("Not acceptable to COVDIFF: ~M", [ishow(e)])
  }
}

///|
fn covdifftimes(l : Value, x : Value) -> Value raise {
  let mut l = l
  let mut left : Value = Nil
  let out = list1(list1(q_mplus))
  while true {
    let sp = car(l)
    l = cdr(l)
    nconc(
      out,
      list1(
        simptimes(
          cons(
            list1(q_mtimes),
            cons(d_covdiff(list2(sp, x)), append(left, l)),
          ),
          Fix(1L),
          t,
        ),
      ),
    )
    |> ignore
    if l is Nil {
      return out
    }
    left = nconc(left, list1(sp))
  }
  out
}

///|
/// Add frame bracket contribution when iframe_flag:true
fn vecdiff(v : Value, i : Value, j : Value, d : Value) -> Value raise {
  if symval(q_d_iframe_flag).truthy() {
    cons(
      list2(q_mplus, q_simp),
      list2(
        list4(list1(v), list1(list1(q_mlist)), share_itensor__mlist([i]), j),
        list3(
          list2(q_mtimes, q_simp),
          list3(list1(v), list1(list1(q_mlist)), share_itensor__mlist([d])),
          list3(
            list2(q_mtimes, q_simp),
            Fix(-1L),
            list3(
              list1(q_p_ifb),
              share_itensor__mlist([d, j]),
              share_itensor__mlist([i]),
            ),
          ),
        ),
      ),
    )
  } else {
    list4(list1(v), list1(list1(q_mlist)), share_itensor__mlist([i]), j)
  }
}

///|
/// The first (length l) - (length s) elements of l, i.e. those before the
/// tail s: `(subseq l 0 (- (length l) (length s)))`.
fn share_itensor__before(l : Value, s : Value) -> Value raise {
  subseq(l, 0, end=length(l) - length(s))
}

///|
fn liediff(v : Value, e : Value, n : Value) -> Value raise {
  if !symbolp(v) {
    merr("~M is not a symbol", [v])
  } else if atom(e) || eq(caar(e), q_rat) {
    // Scalar field: v([],[%1])*idiff(e,%1)
    let dummy = implode(nconc(exploden(symval(q_d_idummyx)), exploden(n)))
    list3(
      list1(q_mtimes),
      list3(list1(v), list1(list1(q_mlist)), share_itensor__mlist([dummy])),
      d_idiff(list2(e, dummy)),
    )
  } else if rpobj(e).truthy() {
    // Tensor field
    let dummy = d_idummy()
    let dummy2 = if symval(q_d_iframe_flag).truthy() { d_idummy() } else { Nil }
    let part1 = list3(
      list1(q_mplus),
      Fix(0L),
      list3(
        list1(q_mtimes),
        // e([...],[...],%1)*v([],[%1])
        list3(list1(v), list1(list1(q_mlist)), share_itensor__mlist([dummy])),
        d_idiff(list2(e, dummy)),
      ),
    )
    let part2 = maplist(
      s => {
        // e([..%1..],[...])*v([],[%1],k)
        let s_atom = atom(car(s))
        list4(
          list1(q_mtimes),
          if s_atom {
            Fix(1L)
          } else {
            Fix(-1L)
          },
          append(
            list3(
              car(e),
              cons(
                list1(q_mlist),
                append(
                  share_itensor__before(cdadr(e), s),
                  cons(
                    if s_atom {
                      dummy
                    } else {
                      list3(list2(q_mtimes, q_simp), Fix(-1L), dummy)
                    },
                    cdr(s),
                  ),
                ),
              ),
              caddr(e),
            ),
            cdddr(e),
          ),
          vecdiff(
            v,
            if s_atom {
              dummy
            } else {
              caddr(car(s))
            },
            if s_atom {
              car(s)
            } else {
              dummy
            },
            dummy2,
          ),
        )
      },
      cdadr(e),
    )
    let part3 = maplist(
      s => {
        // +e([...],[...],..%1..)*v([],[%1],k)
        list3(
          list1(q_mtimes),
          append_n([
            list3(car(e), cadr(e), caddr(e)),
            share_itensor__before(cdddr(e), s),
            cons(dummy, cdr(s)),
          ]),
          vecdiff(v, dummy, car(s), dummy2),
        )
      },
      cdddr(e),
    )
    let part4 = maplist(
      s => {
        // -e([...],[..%1..])*v([],[k],%1)
        list4(
          list1(q_mtimes),
          Fix(-1L),
          append(
            list3(
              car(e),
              cadr(e),
              cons(
                list1(q_mlist),
                append(share_itensor__before(cdaddr(e), s), cons(dummy, cdr(s))),
              ),
            ),
            cdddr(e),
          ),
          vecdiff(v, car(s), dummy, dummy2),
        )
      },
      cdaddr(e),
    )
    append_n([part1, part2, part3, part4])
  } else if eq(caar(e), q_mtimes) {
    // Leibniz rule: Lv(cadr e)*(cddr e)+(cadr e)*Lv(cddr e)
    let a = cons(list1(q_mtimes), cons(liediff(v, cadr(e), n), cddr(e)))
    let b = cons(
      list1(q_mtimes),
      list2(
        cadr(e),
        liediff(
          v,
          if cdddr(e).truthy() {
            cons(list1(q_mtimes), cddr(e))
          } else {
            caddr(e)
          },
          n,
        ),
      ),
    )
    list3(list1(q_mplus), a, b)
  } else if eq(caar(e), q_mplus) {
    // Linearity
    cons(list1(q_mplus), mapcar(u => liediff(v, u, n), cdr(e)))
  } else {
    merr("~M is not a tensorial expression liediff can handle", [e])
  }
}

///|
fn d_liediff(v : Value, e : Value) -> Value raise {
  liediff(v, e, Fix(1L))
}

///|
fn d_rediff(x : Value) -> Value raise {
  meval(list3(list1(q_d_ev), x, q_d_idiff))
}

///|
fn d_undiff(x : Value) -> Value raise {
  if atom(x) {
    x
  } else if rpobj(x).truthy() {
    if cdddr(x).truthy() {
      nconc(
        list2(list1(q_p_idiff), list3(car(x), cadr(x), caddr(x))),
        putinones(cdddr(x)),
      )
    } else {
      x
    }
  } else {
    mysubst0(
      simplifya(cons(list1(caar(x)), mapcar(y => d_undiff(y), cdr(x))), t),
      x,
    )
  }
}

///|
fn d_evundiff(x : Value) -> Value raise {
  meval(list3(list1(q_d_ev), d_undiff(x), q_d_nouns))
}

///|
fn putinones(e : Value) -> Value raise {
  if cdr(e).truthy() {
    cons(car(e), cons(Fix(1L), putinones(cdr(e))))
  } else {
    list2(car(e), Fix(1L))
  }
}

///|
fn d_lorentz_gauge(n : Value) -> Value raise {
  let nargs = length(n)
  if nargs == 0 {
    merr("LORENTZ_GAUGE requires at least one argument", [])
  } else if nargs == 1 {
    lorentz(nth(0, n), Nil)
  } else {
    let l = cdr(n)
    let ok = every(v => symbolp(v), l)
    lorentz(
      nth(0, n),
      if ok {
        l
      } else {
        merr("Invalid tensor name(s) in argument to LORENTZ_GAUGE", [])
      },
    )
  }
}

///|
/// Lorentz contraction of E: indexed objects with a derivative index
/// matching a contravariant index become 0. If L is NIL then do this for
/// all indexed objects otherwise do this only for those indexed objects
/// whose names are members of L.
fn lorentz(e : Value, l : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() {
    if (l is Nil || memq(caar(e), l).truthy()) &&
      intersect(cdaddr(e), cdddr(e)).truthy() {
      Fix(0L)
    } else {
      e
    }
  } else {
    mysubst0(
      simplifya(cons(list1(caar(e)), mapcar(q => lorentz(q, l), cdr(e))), t),
      e,
    )
  }
}

///|
/// alphanumeric compare
fn less(x : Value, y : Value) -> Value raise {
  if numberp(x) {
    if numberp(y) {
      lbool(num_lt(x, y))
    } else {
      alphalessp(ascii(x), y)
    }
  } else if numberp(y) {
    alphalessp(x, ascii(y))
  } else {
    alphalessp(x, y)
  }
}

///|
/// Main contraction function
fn d_contract(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() {
    contract5(e)
  } else if eq(caar(e), q_mtimes) {
    mysubst0(simplifya(cons(list1(q_mtimes), contract4a(e)), Nil), e)
  } else if eq(caar(e), q_mplus) {
    mysubst0(
      simplus(
        cons(list1(q_mplus), mapcar(x => d_contract(x), cdr(e))),
        Fix(1L),
        t,
      ),
      e,
    )
  } else {
    mysubst0(simplifya(cons(car(e), mapcar(x => d_contract(x), cdr(e))), Nil), e)
  }
}

///|
fn contract4a(e : Value) -> Value raise {
  let mut l1 : Value = Nil
  let mut l2 : Value = Nil
  for o in cdr(e).iter() {
    if atom(o) || atom(car(o)) {
      l1 = cons(o, l1)
    } else if eq(caar(o), q_mexpt) && eql(caddr(o), Fix(-1L)) {
      l2 = cons(cadr(o), l2)
    } else {
      l1 = cons(o, l1)
    }
  }
  if l1.truthy() {
    l1 = contract4(cons(list1(q_mtimes), l1))
  }
  if l2.truthy() {
    l1 = cons(
      list3(
        list1(q_mexpt),
        cons(list1(q_mtimes), contract4(cons(list1(q_mtimes), l2))),
        Fix(-1L),
      ),
      l1,
    )
  }
  l1
}

///|
/// Contract a single tensor with itself
fn contract5(e : Value) -> Value raise {
  // See if e contracts with itself, find contraction symbol
  let c0 = if rpobj(e).truthy() { getcon(caar(e)) } else { Nil }
  if c0 is Nil {
    return e
  }
  let symbol = {
    let mut c = getcon(caar(e))
    while !(eq(caar(c), caar(e)) || c is Nil) {
      c = cdr(c)
    }
    if c.truthy() {
      cdar(c)
    } else {
      Nil
    }
  }
  if symbol is Nil || memq(caar(e), symval(q_christoffels)).truthy() {
    return e
  }
  let sgn : Value = if rpobj(share_itensor__canform(e)).truthy() {
    Fix(1L)
  } else {
    Fix(-1L)
  }
  let mut cov = contractinside(derat(cadr(e)))
  let mut con = derat(caddr(e))
  let mut f = !equal(cov, derat(cadr(e)))
  // Calling contract2 here won't do the trick as it messes up the order of
  // indices. So we remove indices that appear both in cov and in con the
  // hard way, with a do loop.
  let mut i = cov
  while i is Cons(_) {
    if !atom(car(i)) {
      ()
    } else if member(car(i), con).truthy() {
      f = true
      con = delete(car(i), con)
      cov = delete(car(i), cov)
    }
    i = cdr(i)
  }
  let c = nconc(
    list3(
      if f {
        list1(symbol)
      } else {
        car(e)
      },
      cov,
      con,
    ),
    cdddr(e),
  )
  if f && eql(sgn, Fix(-1L)) {
    list3(list1(q_mtimes), sgn, c)
  } else {
    c
  }
}

///|
fn head(x : Value) -> Value raise {
  if atom(x) {
    Nil
  } else {
    cons(car(x), Nil)
  }
}

///|
fn firstintersect(l1 : Value, l2 : Value) -> Value raise {
  head(intersect(l1, l2))
}

///|
/// Remove like members. Return (cons l1 l2) or nil if no like members found.
fn contract2(l1 : Value, l2 : Value) -> Value raise {
  let i = firstintersect(l1, l2)
  if i.truthy() {
    cons(setdiff(l1, i), setdiff(l2, i))
  } else {
    Nil
  }
}

///|
/// Return a list with those members of s1 that are not in s2
fn setdiff(s1 : Value, s2 : Value) -> Value raise {
  let mut a : Value = Nil
  for x in s1.iter() {
    if !(!numberp(x) && memq(x, s2).truthy()) {
      a = cons(x, a)
    }
  }
  reverse(a)
}

///|
/// Tries to contract IT with some element of LST. If none occurs then
/// return NIL otherwise return a list whose first member is the result of
/// contraction and whose cdr is a top-level copy of LST with the element
/// which contracted removed.
fn contract3(it : Value, lst : Value) -> Value raise {
  let mut lst = lst
  let mut rest : Value = Nil
  while true {
    let frst = car(lst)
    lst = cdr(lst)
    let r = contract1(it, frst)
    if r.truthy() {
      return cons(r, nconc(nreverse(rest), lst))
    }
    // Try contraction in reverse order since the operation is commutative.
    if getcon(caar(frst)).truthy() {
      let r = contract1(frst, it)
      if r.truthy() {
        return cons(r, nconc(nreverse(rest), lst))
      }
    }
    if lst is Nil {
      return Nil
    }
    rest = cons(frst, rest)
  }
  Nil
}

///|
/// Is x of the form `((mtimes [simp]) -1 ...)` (tested with EQUAL)?
fn share_itensor__negprodp(x : Value) -> Bool {
  (equal(car(x), list1(q_mtimes)) || equal(car(x), list2(q_mtimes, q_simp))) &&
  eql(cadr(x), Fix(-1L))
}

///|
/// contracts products
fn contract4(l : Value) -> Value raise {
  let mut l1 : Value = Nil
  let mut l2 : Value = Nil
  let mut l3 : Value = Nil
  let mut f : Value = Nil
  let mut sf : Value = Nil
  // The first loop sets up 3 lists from the factors on L: L1 - atoms or the
  // contraction of non indexed objects (the contraction is to handle
  // sub-expressions in case E is not fully expanded as in A*B*(C*D+E*F). ),
  // L2 - indexed objects in L with contraction property, L3 - indexed
  // objects in L without contraction property
  let mut cl = cdr(l)
  while true {
    f = car(cl)
    cl = cdr(cl)
    if atom(f) {
      l1 = cons(f, l1)
    } else if rpobj(f).truthy() {
      // contract5 may return a negative result. (The Lisp tests the header
      // with EQ against quoted lists, which never succeeds.)
      f = contract5(f)
      if getcon(caar(f)).truthy() {
        l2 = cons(f, l2)
      } else {
        l3 = cons(f, l3)
      }
    } else {
      l1 = cons(d_contract(f), l1)
    }
    if cl is Nil {
      break
    }
  }
  if l2 is Nil {
    return nconc(l1, l3)
  }
  // If L2 is empty then no more contractions are needed. If L2 has only 1
  // member then just contract it with L3 otherwise contract the members of
  // L2 with themselves. The following loop goes down L2 trying to contract
  // members with other members according to the following method: moving
  // from front to end take current member (F) and see if it contracts with
  // any elements in the rest of the list (this is done by CONTRACT3). If it
  // doesn't then add it to CL. If it does then take result of contraction
  // and add to L1, L2, or L3 as above.
  // state: 1 = loop1, 2 = loop2, 3 = loop2+1
  let mut state = 1
  if cdr(l2) is Nil {
    cl = l2
    state = 3
  }
  // contract3 may also return a negative result
  let strip = (sf : Value) => mapcar(
    x => if atom(x) {
      x
    } else if share_itensor__negprodp(x) {
      l1 = cons(Fix(-1L), l1)
      caddr(x)
    } else {
      x
    },
    sf,
  )
  while true {
    if state == 1 {
      f = car(l2)
      l2 = cdr(l2)
      sf = contract3(f, l2)
      if sf is Nil {
        cl = cons(f, cl)
      } else {
        sf = strip(sf)
        l2 = cdr(sf)
        sf = car(sf)
        if atom(sf) {
          l1 = cons(sf, l1)
        } else if rpobj(sf).truthy() {
          if getcon(caar(sf)).truthy() {
            l2 = cons(sf, l2)
          } else {
            l3 = cons(sf, l3)
          }
        } else {
          l1 = cons(sf, l1)
        }
      }
      // If L2 has at least 2 elements left then continue loop. If L2 has 1
      // element and CL is not empty and there were some contractions
      // performed last time then add CL to L2 and try again. Otherwise add
      // L2 to CL and quit.
      if l2.truthy() {
        if cdr(l2).truthy() {
          continue
        } else if cl.truthy() && sf.truthy() {
          sf = Nil
          l2 = cons(car(l2), cl)
          cl = Nil
          continue
        } else {
          cl = nconc(l2, cl)
        }
      }
      state = 2
    }
    // The following loop goes down CL trying to contract each member with
    // some member in L3. If there is not a contraction then the element from
    // CL is added onto L3 (this causes elements of CL to be contracted with
    // each other). If there is a contraction then the result is added onto
    // L3 by setting L3 to the result of CONTRACT3 here if CL is known not to
    // be null. If L3 is empty then there is nothing left to contract.
    if state == 2 {
      if cl is Nil {
        return nconc(l1, l3)
      }
      state = 3
    }
    // loop2+1
    if l3 is Nil {
      return nconc(l1, cl)
    }
    f = car(cl)
    cl = cdr(cl)
    sf = contract3(f, l3)
    if sf.truthy() {
      sf = strip(sf)
      l3 = sf
    } else {
      l3 = cons(f, l3)
    }
    state = 2
  }
  Nil
}

///|
/// Create a 'normalized' (i.e., old-style) rpobj
fn d_renorm(e : Value, force? : Value = Nil) -> Value raise {
  let mut force = force
  if !rpobj(e).truthy() {
    merr("Not an RPOBJ: ~M", [e]) |> ignore
  }
  if symval(q_d_allsym).truthy() {
    force = t
  }
  let mut c = cdaddr(e)
  let mut v : Value = Nil
  let mut i = reverse(cdadr(e))
  while true {
    if i is Nil || (atom(car(i)) && force is Nil) {
      // Remaining covariant indices
      v = append(reverse(i), v)
      break
    }
    if atom(car(i)) {
      v = cons(car(i), v)
    } else {
      c = cons(caddar(i), c)
    }
    i = cdr(i)
  }
  cons(
    car(e),
    append(
      list2(share_itensor__ml(v), share_itensor__ml(c)),
      cdddr(e),
    ),
  )
}

///|
/// Add a minus sign to all elements in a list
fn neglist(l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else {
    cons(share_itensor__neg_index(car(l)), neglist(cdr(l)))
  }
}

///|
/// Create an 'abnormal' (i.e., new-style) rpobj
fn abnorm(e : Value) -> Value raise {
  append(
    list3(
      car(e),
      append(d_covi(e), neglist(conti(e))),
      share_itensor__empty_ml(),
    ),
    cdddr(e),
  )
}

///|
/// Substitute using EQUAL, to catch member lists
fn substlist(b : Value, a : Value, l : Value) -> Value raise {
  if l is Nil {
    l
  } else if equal(a, car(l)) {
    cons(b, cdr(l))
  } else {
    cons(car(l), substlist(b, a, cdr(l)))
  }
}

///|
/// Removes items not in i from l.
fn removenotin(i : Value, l : Value) -> Value raise {
  if l is Nil {
    l
  } else if memq(car(l), i).truthy() {
    cons(car(l), removenotin(i, cdr(l)))
  } else {
    removenotin(i, cdr(l))
  }
}

///|
/// Removes items not in i from l. But the ones in l have a minus sign!
fn removenotinm(i : Value, l : Value) -> Value raise {
  if l is Nil {
    l
  } else if atom(car(l)) {
    cons(car(l), removenotinm(i, cdr(l)))
  } else if isprod(caar(l)).truthy() &&
    eql(cadar(l), Fix(-1L)) &&
    memq(caddar(l), i) is Nil {
    removenotinm(i, cdr(l))
  } else {
    cons(car(l), removenotinm(i, cdr(l)))
  }
}

///|
/// Removes indices duplicated once with and once without a minus sign
fn contractinside(c : Value) -> Value raise {
  let mut c = c
  let mut i = minusi(c)
  while i is Cons(_) {
    if member_equal(car(i), c).truthy() &&
      member_equal(share_itensor__neg_index(car(i)), c).truthy() {
      c = delete(car(i), remove_equal(share_itensor__neg_index(car(i)), c))
    }
    i = cdr(i)
  }
  c
}

///|
/// Is (caar g) one of the objects no tensor can contract?
fn share_itensor__uncontractable(op : Value) -> Bool {
  eq(op, q_d_kdelta) ||
  eq(op, q_p_kdelta) ||
  eq(op, q_d_levi_civita) ||
  eq(op, q_p_levi_civita) ||
  eq(op, q_d_icurvature) ||
  eq(op, q_p_icurvature) ||
  eq(op, q_d_itr) ||
  eq(op, q_p_itr)
}

///|
/// (+ (length (plusi x)) (length (minusi y)))
fn share_itensor__nidx(x : Value, y : Value) -> Int raise {
  length(plusi(x)) + length(minusi(y))
}

///|
/// The Kronecker-delta part of CONTRACT1: f is a Kronecker delta.
fn share_itensor__contract1_kdelta(
  a0 : Value,
  b0 : Value,
  c0 : Value,
  d0 : Value,
  e : Value,
  g : Value,
) -> Value raise {
  // We normalize the indices first
  let mut b = append(minusi(a0), b0)
  let mut a = plusi(a0)
  let mut c = c0
  let mut d = d0
  // We cannot contract with higher-order or malformed Kronecker deltas
  if length(a) != 1 || length(b) != 1 {
    return Nil
  }
  a = car(a)
  b = car(b)
  let r = if cdr(c).truthy() && !numberp(b) && memq(b, cdr(c)).truthy() {
    c = subst(a, b, cdr(c))
    if memq(caar(g), symval(q_christoffels)) is Nil && cdr(d).truthy() {
      a = contract2(c, cdr(d))
      if a.truthy() {
        c = car(a)
        d = share_itensor__ml(cdr(a))
      }
    }
    c = contractinside(c)
    nconc(list3(car(g), share_itensor__ml(c), d), e)
  } else if e.truthy() && !numberp(b) && memq(b, e).truthy() {
    nconc(
      list3(car(g), c, d),
      if symval(q_d_iframe_flag).truthy() {
        subst(a, b, e)
      } else {
        itensor_sort(subst(a, b, e))
      },
    )
  } else if cdr(d).truthy() && !numberp(a) && memq(a, cdr(d)).truthy() {
    d = subst(b, a, cdr(d))
    if cdr(c).truthy() {
      a = contract2(cdr(c), d)
      if a.truthy() {
        d = cdr(a)
        c = share_itensor__ml(car(a))
      }
    }
    nconc(list3(car(g), c, share_itensor__ml(d)), e)
  } else if cdr(c).truthy() &&
    !numberp(a) &&
    member_equal(share_itensor__neg_index(a), cdr(c)).truthy() {
    c = substlist(
      share_itensor__neg_index(b),
      share_itensor__neg_index(a),
      cdr(c),
    )
    c = contractinside(c)
    nconc(list3(car(g), share_itensor__ml(c), d), e)
  } else {
    Nil
  }
  simplifya(r, Nil)
}

///|
/// This does the actual contraction of f with g. If f has any derivative
/// indices then it can't contract g. If f is Kronecker delta then see which
/// of the covariant, contravariant, or derivative indices matches those in
/// g.
fn contract1(f : Value, g : Value) -> Value raise {
  if cdddr(f).truthy() {
    return Nil
  }
  let mut a = copy_tree(derat(cdadr(f)))
  let mut b = copy_tree(cdaddr(f))
  let mut c = copy_tree(derat(cadr(g)))
  let mut d = copy_tree(caddr(g))
  let e = copy_tree(cdddr(g))
  // This section is all Kronecker-delta code
  if eq(caar(f), q_p_kdelta) || eq(caar(f), q_d_kdelta) {
    return share_itensor__contract1_kdelta(a, b, c, d, e, g)
  }
  // No tensor can contract Kronecker-deltas, Levi-Civita symbols, or the
  // torsion tensor.
  if share_itensor__uncontractable(caar(g)) {
    return Nil
  }
  // If g has derivative indices then F must be constant in order to
  // contract it
  if e.truthy() && kindp(caar(f), q_d_constant) is Nil {
    return Nil
  }
  // Contraction property of f is a list of (a.b)'s
  let mut cf = getcon(caar(f))
  if cf is Nil {
    return Nil
  }
  // Determine the sign of the result based on the expression's symmetry
  // properties. We use CANFORM to sort indices in the canonical order and
  // then extract the resulting expression's sign.
  let sgn : Value = if eql(
      Fix(-1L),
      cadr(share_itensor__canform(list3(list2(q_mtimes, q_simp), f, g))),
    ) {
    Fix(-1L)
  } else {
    Fix(1L)
  }
  // If g matches an a then use the b for name of result. If an a is a space
  // use name of G for result.
  while true {
    if eq(caar(cf), q_op_sp) {
      cf = car(g)
      break
    } else if eq(caar(cf), caar(g)) {
      cf = list1(cdar(cf))
      break
    } else {
      cf = cdr(cf)
      if cf is Nil {
        return Nil
      }
    }
  }
  c = cdr(c)
  d = cdr(d)
  // If CONTRACT2 of f's contravariant and g's covariant or f's covariant and
  // g's contravariant indices is nil then return nil
  let mut ff : Value = Nil
  let mut done = false
  if b.truthy() && c.truthy() {
    ff = contract2(b, c)
    if ff.truthy() {
      b = car(ff)
      c = cdr(ff)
      done = true
    }
  }
  if !done && a.truthy() && d.truthy() {
    ff = contract2(a, d)
    if ff.truthy() {
      a = car(ff)
      d = cdr(ff)
      done = true
    }
  }
  if !done && a.truthy() && minusi(c).truthy() {
    ff = contract2(a, minusi(c))
    if ff.truthy() {
      done = true
      // (cdr f) now contains the free indices in (minusi c). Find the
      // corresponding items in c, and remove all other negative indices
      // (i.e., those that were dropped by contract2): remove items from c
      // one by one, and substitute an item from (car f), which we remove
      // from (car f).
      let mut i = c
      let mut j = car(ff)
      let mut k : Value = Nil
      while true {
        if i is Nil {
          a = removenotin(j, a)
          c = reverse(k)
          break
        }
        if atom(car(i)) || member(caddar(i), cdr(ff)).truthy() {
          k = cons(car(i), k)
        } else if j.truthy() {
          k = cons(car(j), k)
          j = cdr(j)
        }
        i = cdr(i)
      }
    }
  }
  if !done && minusi(a).truthy() && c.truthy() {
    ff = contract2(minusi(a), c)
    if ff.truthy() {
      done = true
      let mut i = c
      let mut j = car(ff)
      let mut k : Value = Nil
      while true {
        if i is Nil {
          c = reverse(k)
          a = append(plusi(a), mapcar(x => share_itensor__neg_index(x), j))
          break
        }
        if member(car(i), cdr(ff)).truthy() {
          k = cons(car(i), k)
        } else if j.truthy() {
          k = cons(share_itensor__neg_index(car(j)), k)
          j = cdr(j)
        }
        i = cdr(i)
      }
    }
  }
  if !done {
    return Nil
  }
  // Form combined indices of result
  if d.truthy() {
    b = append(b, d)
  }
  if c.truthy() {
    a = append(c, a)
  }
  // VTT: Special handling of Christoffel symbols. We can only contract them
  // when we turn ICHR1 into ICHR2 or vice versa; other index combinations
  // are illegal. This code checks if the index pattern is a valid one and
  // replaces ICHR1 with ICHR2 or vice versa as appropriate.
  let ch1 = symval(q_christoffels1)
  let ch2 = symval(q_christoffels2)
  if member(car(cf), ch1).truthy() {
    // VTT - before anything else, check that we're contracting on the last
    // index only
    if !equal(append(c, last(cdadr(g))), cdadr(g)) {
      return Nil
    } else if share_itensor__nidx(a, b) == 2 && share_itensor__nidx(b, a) == 1 {
      cf = cons(elt(ch2, position(car(cf), ch1)), cdr(cf))
    } else if !(share_itensor__nidx(a, b) == 3 && share_itensor__nidx(b, a) == 0) {
      return Nil
    }
  } else if member(car(cf), ch2).truthy() {
    if share_itensor__nidx(a, b) == 3 && share_itensor__nidx(b, a) == 0 {
      cf = cons(elt(ch1, position(car(cf), ch2)), cdr(cf))
    } else if !(share_itensor__nidx(a, b) == 2 && share_itensor__nidx(b, a) == 1) {
      return Nil
    }
  } else if member(car(cf), symval(q_christoffels)).truthy() {
    return Nil
  }
  let mut fv = meval(
    list3(cf, share_itensor__ml(a), share_itensor__ml(b)),
  )
  for x in e.iter() {
    fv = idiff(fv, x)
  }
  if eql(sgn, Fix(-1L)) {
    list3(list1(q_mtimes), sgn, fv)
  } else {
    fv
  }
}

///|
/// In what amounts to quite an abuse of the Kronecker delta concept, we
/// permit an exceptional index combination of two contravariant indices.
/// This helps lc2kdt convert Levi-Civita symbols in a manner that does not
/// require resorting to numeric indices, causing all sorts of problems with
/// RENAME and CONTRACT.
fn d_kdelta(l1 : Value, l2 : Value) -> Value raise {
  let l2 = append(l2, minusi(l1))
  let l1 = plusi(l1)
  let lists = d_listp(l1).truthy() && d_listp(l2).truthy()
  if lists &&
    num_eq(d_length(l1), Fix(0L)) &&
    num_eq(d_length(l2), Fix(2L)) {
    if eq(cadr(l2), caddr(l2)) {
      Fix(1L)
    } else if numberp(cadr(l2)) && numberp(caddr(l2)) {
      if num_eq(cadr(l2), caddr(l2)) {
        t
      } else {
        Fix(0L)
      }
    } else {
      list3(list1(q_p_kdelta), l1, l2)
    }
  } else if lists &&
    num_eq(d_length(l1), Fix(2L)) &&
    num_eq(d_length(l2), Fix(0L)) {
    if eq(cadr(l1), caddr(l1)) {
      Fix(1L)
    } else if numberp(cadr(l1)) && numberp(caddr(l1)) {
      if num_eq(cadr(l1), caddr(l1)) {
        t
      } else {
        Fix(0L)
      }
    } else {
      list3(list1(q_p_kdelta), l1, l2)
    }
  } else if !(lists && length(l1) == length(l2)) {
    merr("Improper arg to DELTA: ~M", [list3(list1(q_p_kdelta), l1, l2)])
  } else {
    delta(cdr(l1), cdr(l2))
  }
}

///|
/// kdels defines the symmetric combination of the Kronecker symbols
fn d_kdels(l1 : Value, l2 : Value) -> Value raise {
  if !(d_listp(l1).truthy() && d_listp(l2).truthy() && length(l1) == length(l2)) {
    merr("Improper arg to DELTA: ~M", [list3(list1(q_p_kdels), l1, l2)])
  } else {
    delta(cdr(l1), cdr(l2), eps=Fix(1L))
  }
}

///|
fn delta(lower : Value, upper : Value, eps? : Value = Fix(-1L)) -> Value raise {
  if lower is Nil {
    symval(q_d_dim)
  } else if cdr(lower) is Nil {
    if equal(car(upper), car(lower)) {
      if numberp(car(upper)) {
        Fix(1L)
      } else {
        symval(q_d_dim)
      }
    } else if numberp(car(upper)) && numberp(car(lower)) {
      Fix(0L)
    } else {
      list3(
        list1(q_p_kdelta),
        share_itensor__ml(lower),
        share_itensor__ml(upper),
      )
    }
  } else {
    let mut left : Value = Nil
    let mut right = lower
    let mut result : Value = Nil
    while right.truthy() {
      result = cons(
        simptimes(
          list4(
            list1(q_mtimes),
            delta(list1(car(right)), list1(car(upper)), eps~),
            delta(append(left, cdr(right)), cdr(upper), eps~),
            if length(left) % 2 == 1 {
              eps
            } else {
              Fix(1L)
            },
          ),
          Fix(1L),
          t,
        ),
        result,
      )
      left = append(left, list1(car(right)))
      right = cdr(right)
    }
    simplus(cons(list1(q_mplus), result), Fix(1L), t)
  }
}
