// Port of src/cpoly.lisp, part 1: $ALLROOTS with double floats (part 2,
// cpoly_2.mbt, is the bigfloat version $BFALLROOTS).
//
// This is a lisp version of algorithm 419 from the Communications of
// the ACM (p 97 vol 15 feb 1972) by Jenkins and Traub.  That
// algorithm is followed very closely.  Note the following
// modifications: arrays are indexed from 0 instead of 1.  This means
// that the variables n and nn are one less than the acm verson.  The
// zeros are put into the arrays pr-sl and pi-sl, rather than into
// their own arrays.  The algorithm seems to benefit be taking are
// mre 0.01 times the published values.
//
// The Lisp special variables (*pr-sl*, *cr*, *nn*, ...) are used only by
// this file and nothing in it re-enters Maxima, so they are kept in the
// private state records below.  The double-float arithmetic is done with
// checked operations that signal the same arithmetic errors SBCL's
// floating-point traps do (overflow, invalid operation, division by zero),
// keeping the exact IEEE operation order of the Lisp code.

///|
/// Integer and boolean state shared by the float and bigfloat versions:
/// *nn* *n* *polysc* *polysc1* *nz* *my-type* *conv* *bool*.
priv struct CpolyIState {
  mut nn : Int
  mut n : Int
  mut polysc : Int
  mut polysc1 : Int
  mut nz : Int
  mut my_type : Int
  mut conv : Bool
  mut bool_ : Bool
}

///|
/// Double-float state: the arrays *pr-sl* ... *qhi-sl* and the scalar
/// specials of the float version.
priv struct CpolyFState {
  mut pr : Array[Double]
  mut pi : Array[Double]
  mut shr : Array[Double]
  mut shi : Array[Double]
  mut qpr : Array[Double]
  mut qpi : Array[Double]
  mut hr : Array[Double]
  mut hi : Array[Double]
  mut qhr : Array[Double]
  mut qhi : Array[Double]
  mut logbas : Double
  mut infin : Double
  mut are : Double
  mut mre : Double
  mut cr : Double
  mut ci : Double
  mut sr : Double
  mut si : Double
  mut tr : Double
  mut ti : Double
  mut zr : Double
  mut zi : Double
  mut pvr : Double
  mut pvi : Double
  mut u : Double
  mut v : Double
  mut a : Double
  mut b : Double
  mut c : Double
  mut d : Double
  mut a1 : Double
  mut a3 : Double
  mut a7 : Double
  mut e : Double
  mut f : Double
  mut g : Double
  mut h : Double
  mut szr : Double
  mut szi : Double
  mut lzr : Double
  mut lzi : Double
  mut ui : Double
  mut vi : Double
  mut s : Double
}

///|
let cpoly__i : CpolyIState = {
  nn: 0,
  n: 0,
  polysc: 0,
  polysc1: 0,
  nz: 0,
  my_type: 0,
  conv: false,
  bool_: false,
}

///|
let cpoly__f : CpolyFState = {
  pr: [],
  pi: [],
  shr: [],
  shi: [],
  qpr: [],
  qpi: [],
  hr: [],
  hi: [],
  qhr: [],
  qhi: [],
  logbas: 0.0,
  infin: 0.0,
  are: 0.0,
  mre: 0.0,
  cr: 0.0,
  ci: 0.0,
  sr: 0.0,
  si: 0.0,
  tr: 0.0,
  ti: 0.0,
  zr: 0.0,
  zi: 0.0,
  pvr: 0.0,
  pvi: 0.0,
  u: 0.0,
  v: 0.0,
  a: 0.0,
  b: 0.0,
  c: 0.0,
  d: 0.0,
  a1: 0.0,
  a3: 0.0,
  a7: 0.0,
  e: 0.0,
  f: 0.0,
  g: 0.0,
  h: 0.0,
  szr: 0.0,
  szi: 0.0,
  lzr: 0.0,
  lzi: 0.0,
  ui: 0.0,
  vi: 0.0,
  s: 0.0,
}

// ---------------------------------------------------------------------------
// Checked double-float arithmetic (SBCL traps overflow, invalid and
// division-by-zero).

///|
/// most-positive-double-float
let cpoly__most_positive_flonum : Double = 1.7976931348623157e308

///|
/// double-float-epsilon (SBCL: 2^-53 * (1 + 2^-52))
let cpoly__flonum_epsilon : Double = (0x3CA0000000000001L).reinterpret_as_double()

///|
fn cpoly__chk(x : Double) -> Double raise {
  if x.is_nan() {
    raise LispError::Condition(
      intern("floating-point-invalid-operation"),
      "arithmetic error FLOATING-POINT-INVALID-OPERATION signalled",
      Nil,
    )
  }
  if x.is_inf() {
    raise LispError::Condition(
      intern("floating-point-overflow"),
      "arithmetic error FLOATING-POINT-OVERFLOW signalled",
      Nil,
    )
  }
  x
}

///|
fn cpoly__add(a : Double, b : Double) -> Double raise {
  cpoly__chk(a + b)
}

///|
fn cpoly__sub(a : Double, b : Double) -> Double raise {
  cpoly__chk(a - b)
}

///|
fn cpoly__mul(a : Double, b : Double) -> Double raise {
  cpoly__chk(a * b)
}

///|
fn cpoly__div(a : Double, b : Double) -> Double raise {
  if b == 0.0 {
    raise division_by_zero()
  }
  cpoly__chk(a / b)
}

///|
fn cpoly__sqrt(x : Double) -> Double raise {
  cpoly__chk(x.sqrt())
}

///|
fn cpoly__log(x : Double) -> Double raise {
  if x == 0.0 {
    raise division_by_zero()
  }
  cpoly__chk(dlog(x))
}

///|
fn cpoly__exp(x : Double) -> Double raise {
  cpoly__chk(dexp(x))
}

///|
fn cpoly__scale(x : Double, k : Int) -> Double raise {
  cpoly__chk(scale_float(x, k))
}

///|
/// `(floor x)` of a double, as a fixnum.
fn cpoly__floor(x : Double) -> Int raise {
  to_int(floor1(Flo(x)))
}

///|
/// Checked `(aref a i)`.
fn cpoly__g(a : Array[Double], i : Int) -> Double raise {
  if i < 0 || i >= a.length() {
    raise LispError::SimpleError(
      "Invalid index \{i} for (SIMPLE-VECTOR \{a.length()}), should be a non-negative integer below \{a.length()}.",
    )
  }
  a[i]
}

///|
/// Checked `(setf (aref a i) v)`.
fn cpoly__s(a : Array[Double], i : Int, v : Double) -> Unit raise {
  if i < 0 || i >= a.length() {
    raise LispError::SimpleError(
      "Invalid index \{i} for (SIMPLE-VECTOR \{a.length()}), should be a non-negative integer below \{a.length()}.",
    )
  }
  a[i] = v
}

///|
/// A Lisp variable that may still be NIL when compared: comparing NIL with
/// `<` is a type error in Lisp.
fn cpoly__val(x : Double?) -> Double raise {
  match x {
    Some(v) => v
    None => raise type_error(Nil, "REAL")
  }
}

///|
/// Maxima's ERRSET macro: `(value)` on success; on an error, nil unless the
/// special ERRSET is true, in which case the error is re-signalled.
fn cpoly__errset(f : () -> Value raise) -> Value raise {
  f() catch {
    LispError::Throw(_, _) as e => raise e
    LispError::ReturnFrom(_, _) as e => raise e
    LispError::Go(_) as e => raise e
    e => if symval(q_errset).truthy() { raise e } else { Nil }
  } noraise {
    v => list1(v)
  }
}

///|
/// cos and sin of 94 degrees, as computed by the Lisp code
/// `(cos (float (* 94/180 pi)))`.
fn cpoly__rot94() -> (Double, Double) {
  let ang = 47.0 / 90.0 * @math.PI
  (dcos(ang), dsin(ang))
}

// ---------------------------------------------------------------------------
// $ALLROOTS

///|
fn d_allroots(expr : Value) -> Value raise {
  with_specials(
    [
      (q_d_partswitch, Nil),
      (q_d_keepfloat, Nil),
      (q_d_demoivre, Nil),
      (q_d_listconstvars, Nil),
      (q_d_algebraic, Nil),
      (q_d_ratfac, Nil),
    ],
    () => cpoly__allroots(expr),
  )
}

///|
fn cpoly__allroots(expr : Value) -> Value raise {
  let st = cpoly__f
  let ist = cpoly__i
  let mut complex = false
  set(q_d_keepfloat, t) |> ignore
  set(q_d_listconstvars, t) |> ignore
  set(q_d_algebraic, t) |> ignore
  let mut expr = meqhk(expr)
  let expr1 = expr
  let mut var_ = remove(q_d__pcti, cdr(d_listofvars(expr)))
  if !var_.truthy() {
    var_ = list1(gensym())
  }
  if length(var_) != 1 {
    merr(
      "allroots: expected a polynomial in one variable; found variables ~M",
      [cons(list1(q_mlist), var_)],
    )
    |> ignore
  }
  var_ = car(var_)
  expr = d_rat(expr, list2(q_d__pcti, var_))
  let mut res = reverse(car(cdddr(car(expr))))
  let mut i = length(res) - length(caddar(expr))
  while i != 0 {
    res = cdr(res)
    i -= 1
  }
  let mut den = cddr(expr)
  expr = cadr(expr)
  // check denominator is a complex number
  if numberp(den) {
    den = list2(den, Fix(0L))
  } else if eq(car(den), cadr(res)) {
    den = cddr(den)
    if numberp(car(den)) {
      if cddr(den) is Nil {
        den = list2(Fix(0L), car(den))
      } else if numberp(caddr(den)) {
        den = list2(caddr(den), car(den))
      } else {
        cpoly_err(expr1) |> ignore
      }
    } else {
      cpoly_err(expr1) |> ignore
    }
  } else {
    cpoly_err(expr1) |> ignore
  }
  // if the name variable has disappeared, this is caught here
  ist.nn = 0
  if numberp(expr) {
    expr = list2(expr, Fix(0L))
  } else if eq(car(expr), car(res)) {
    ist.nn = 1
  } else if eq(car(expr), cadr(res)) {
    expr = cddr(expr)
    if numberp(car(expr)) {
      if cddr(expr) is Nil {
        expr = list2(Fix(0L), car(expr))
      } else if numberp(caddr(expr)) {
        expr = list2(caddr(expr), car(expr))
      } else {
        cpoly_err(expr1) |> ignore
      }
    } else {
      cpoly_err(expr1) |> ignore
    }
  } else {
    cpoly_err(expr1) |> ignore
  }
  if ist.nn == 0 {
    if symval(q_d_polyfactor).truthy() {
      st.cr = 0.0
      st.ci = 0.0
      cpoly__cdivid(
        to_double(car(expr)),
        to_double(cadr(expr)),
        to_double(car(den)),
        to_double(cadr(den)),
      )
      return simplify(
        list3(
          list1(q_mplus),
          simplify(list3(list1(q_mtimes), q_d__pcti, Flo(st.ci))),
          Flo(st.cr),
        ),
      )
    } else {
      return list1(list2(q_mlist, q_simp))
    }
  }
  let degree = to_int(cadr(expr))
  ist.nn = degree + 1
  st.pr = Array::make(ist.nn, 0.0)
  st.pi = Array::make(ist.nn, 0.0)
  let ok = catch_tag(q_notpoly, () => cpoly__errset(() => {
    let mut ex = cdr(expr)
    let pct_i = cadr(res)
    while !(ex is Nil) {
      let l = degree - to_int(car(ex))
      let mut r = cadr(ex)
      if numberp(r) {
        cpoly__s(st.pr, l, to_double(r))
      } else {
        if !eq(car(r), pct_i) {
          throw_tag(q_notpoly, Nil) |> ignore
        }
        r = cddr(r)
        cpoly__s(st.pi, l, to_double(car(r)))
        r = caddr(r)
        if r.truthy() {
          cpoly__s(st.pr, l, to_double(r))
        }
        complex = true
      }
      ex = cddr(ex)
    }
    Nil
  }))
  if !ok.truthy() {
    // this should catch expressions like sin(x)-x
    cpoly_err(expr1) |> ignore
  }
  st.shr = Array::make(ist.nn, 0.0)
  st.shi = Array::make(ist.nn, 0.0)
  st.qpr = Array::make(ist.nn, 0.0)
  st.hr = Array::make(degree, 0.0)
  st.qhr = Array::make(degree, 0.0)
  st.qpi = Array::make(ist.nn, 0.0)
  if complex {
    st.hi = Array::make(degree, 0.0)
    st.qhi = Array::make(degree, 0.0)
  }
  ist.nn = degree
  let res1 = if complex {
    cpoly__errset(() => cpoly_sl(int(degree)))
  } else {
    cpoly__errset(() => rpoly_sl(int(degree)))
  }
  if !res1.truthy() {
    mtell(list1(Str("allroots: unexpected error; treat results with caution.~%")))
    |> ignore
  }
  if ist.nn == degree {
    merr("allroots: no roots found.", []) |> ignore
  }
  let mut res : Value = Nil
  let polyfactor = symval(q_d_polyfactor).truthy()
  if ist.nn != 0 {
    mtell(
      list([
        Str("allroots: only ~S out of ~S roots found.~%"),
        int(degree - ist.nn),
        int(degree),
      ]),
    )
    |> ignore
    expr = Flo(0.0)
    for i in 0..=ist.nn {
      expr = simplify(
        list3(
          list1(q_mplus),
          expr,
          simplify(
            list3(
              list1(q_mtimes),
              simplify(
                list3(
                  list1(q_mplus),
                  simplify(
                    list3(list1(q_mtimes), q_d__pcti, Flo(cpoly__g(st.pi, i))),
                  ),
                  Flo(cpoly__g(st.pr, i)),
                ),
              ),
              simplify(list3(list1(q_mexpt), var_, int(ist.nn - i))),
            ),
          ),
        ),
      )
    }
    res = cons(expr, res)
  } else if polyfactor {
    st.cr = 0.0
    st.ci = 0.0
    cpoly__cdivid(
      cpoly__g(st.pr, 0),
      cpoly__g(st.pi, 0),
      to_double(car(den)),
      to_double(cadr(den)),
    )
    expr = simplify(
      list3(
        list1(q_mplus),
        simplify(list3(list1(q_mtimes), q_d__pcti, Flo(st.ci))),
        Flo(st.cr),
      ),
    )
    res = cons(expr, res)
  }
  let mut i = degree
  while i != ist.nn {
    expr = simplify(
      list3(
        list1(q_mplus),
        simplify(list3(list1(q_mtimes), q_d__pcti, Flo(cpoly__g(st.pi, i)))),
        Flo(cpoly__g(st.pr, i)),
      ),
    )
    res = if polyfactor {
      cons(
        if complex || cpoly__g(st.pi, i) == 0.0 {
          simplify(
            list3(list1(q_mplus), var_, simplify(list2(list1(q_mminus), expr))),
          )
        } else {
          i = i - 1
          simplify(
            list4(
              list1(q_mplus),
              simplify(list3(list1(q_mexpt), var_, Fix(2L))),
              simplify(list3(list1(q_mtimes), var_, Flo(cpoly__g(st.pr, i)))),
              Flo(cpoly__g(st.pr, i + 1)),
            ),
          )
        },
        res,
      )
    } else {
      let expr = simplify(list3(list1(q_mequal), var_, expr))
      cons(
        if symval(q_d_programmode).truthy() {
          expr
        } else {
          displine(expr)
        },
        res,
      )
    }
    i = i - 1
  }
  simplify(
    if polyfactor {
      cons(list1(q_mtimes), res)
    } else {
      cons(list1(q_mlist), nreverse(res))
    },
  )
}

///|
fn cpoly_err(expr : Value) -> Value raise {
  merr("allroots: expected a polynomial; found ~M", [expr])
}

///|
fn cpoly_sl(degree : Value) -> Value raise {
  int(cpoly__cpoly(to_int(degree)))
}

///|
fn cpoly__cpoly(degree : Int) -> Int raise {
  let st = cpoly__f
  let ist = cpoly__i
  let mut degree = degree
  st.logbas = cpoly__log(2.0)
  st.infin = cpoly__most_positive_flonum
  st.are = cpoly__flonum_epsilon
  st.mre = 0.0
  let mut xx = cpoly__sqrt(0.5)
  let mut yy = 0.0
  let (cosr, sinr) = cpoly__rot94()
  st.cr = 0.0
  st.ci = 0.0
  st.sr = 0.0
  st.si = 0.0
  st.tr = 0.0
  st.ti = 0.0
  st.zr = 0.0
  st.zi = 0.0
  let mut bnd = 0.0
  ist.n = 0
  ist.polysc = 0
  ist.polysc1 = 0
  ist.conv = false
  st.mre = cpoly__mul(cpoly__mul(2.0, cpoly__sqrt(2.0)), st.are)
  yy = -xx
  let mut i = degree
  while cpoly__g(st.pr, i) == 0.0 && cpoly__g(st.pi, i) == 0.0 {
    i -= 1
  }
  ist.nn = i
  ist.n = i - 1
  degree = ist.nn
  for i in 0..=ist.nn {
    cpoly__s(st.shr, i, cpoly__cmod(cpoly__g(st.pr, i), cpoly__g(st.pi, i)))
  }
  if ist.nn > 0 {
    cpoly__scale_sl()
  }
  while true {
    if 2 > ist.nn {
      cpoly__cdivid(
        -cpoly__g(st.pr, 1),
        -cpoly__g(st.pi, 1),
        cpoly__g(st.pr, 0),
        cpoly__g(st.pi, 0),
      )
      cpoly__s(st.pr, 1, st.cr)
      cpoly__s(st.pi, 1, st.ci)
      ist.nn = 0
      break
    }
    for i in 0..=ist.nn {
      cpoly__s(st.shr, i, cpoly__cmod(cpoly__g(st.pr, i), cpoly__g(st.pi, i)))
    }
    bnd = cpoly__cauchy()
    // (catch 'newroot ...)
    newroot~: for cnt1 in 1..=2 {
      cpoly__noshft(5)
      for cnt2 in 1..=9 {
        let xx1 = cpoly__sub(cpoly__mul(cosr, xx), cpoly__mul(sinr, yy))
        yy = cpoly__add(cpoly__mul(sinr, xx), cpoly__mul(cosr, yy))
        xx = xx1
        st.sr = cpoly__mul(bnd, xx)
        st.si = cpoly__mul(bnd, yy)
        cpoly__fxshft(10 * cnt2)
        if ist.conv {
          cpoly__s(st.pr, ist.nn, st.zr)
          cpoly__s(st.pi, ist.nn, st.zi)
          ist.nn = ist.n
          ist.n = ist.n - 1
          for i in 0..=ist.nn {
            cpoly__s(st.pr, i, cpoly__g(st.qpr, i))
            cpoly__s(st.pi, i, cpoly__g(st.qpi, i))
          }
          break newroot~
        }
      }
    }
    if !ist.conv {
      break
    }
  }
  for i in (ist.nn + 1)..=degree {
    cpoly__s(st.pr, i, cpoly__scale(cpoly__g(st.pr, i), ist.polysc1))
    cpoly__s(st.pi, i, cpoly__scale(cpoly__g(st.pi, i), ist.polysc1))
  }
  let mut j = ist.polysc - ist.polysc1 * degree
  for i in 0..=ist.nn {
    cpoly__s(st.pr, i, cpoly__scale(cpoly__g(st.pr, i), j))
    cpoly__s(st.pi, i, cpoly__scale(cpoly__g(st.pi, i), j))
    j = j + ist.polysc1
  }
  ist.nn
}

///|
fn noshft_sl(l1 : Value) -> Value raise {
  cpoly__noshft(to_int(l1))
  Nil
}

///|
fn cpoly__noshft(l1 : Int) -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  let mut xni = ist.nn.to_double()
  let t1 = cpoly__div(1.0, ist.nn.to_double())
  for i in 0..=ist.n {
    cpoly__s(st.hr, i, cpoly__mul(cpoly__mul(cpoly__g(st.pr, i), xni), t1))
    cpoly__s(st.hi, i, cpoly__mul(cpoly__mul(cpoly__g(st.pi, i), xni), t1))
    xni = cpoly__sub(xni, 1.0)
  }
  for jj in 1..=l1 {
    ignore(jj)
    let n = ist.n
    if cpoly__cmod(cpoly__g(st.hr, n), cpoly__g(st.hi, n)) >
      cpoly__mul(
        cpoly__mul(10.0, st.are),
        cpoly__cmod(cpoly__g(st.pr, n), cpoly__g(st.pi, n)),
      ) {
      cpoly__cdivid(
        -cpoly__g(st.pr, ist.nn),
        -cpoly__g(st.pi, ist.nn),
        cpoly__g(st.hr, n),
        cpoly__g(st.hi, n),
      )
      st.tr = st.cr
      st.ti = st.ci
      let mut j = n
      while !(1 > j) {
        let t1 = cpoly__g(st.hr, j - 1)
        let t2 = cpoly__g(st.hi, j - 1)
        cpoly__s(
          st.hr,
          j,
          cpoly__sub(
            cpoly__add(cpoly__g(st.pr, j), cpoly__mul(t1, st.tr)),
            cpoly__mul(t2, st.ti),
          ),
        )
        cpoly__s(
          st.hi,
          j,
          cpoly__add(
            cpoly__add(cpoly__g(st.pi, j), cpoly__mul(t1, st.ti)),
            cpoly__mul(t2, st.tr),
          ),
        )
        j -= 1
      }
      cpoly__s(st.hr, 0, cpoly__g(st.pr, 0))
      cpoly__s(st.hi, 0, cpoly__g(st.pi, 0))
    } else {
      let mut j = n
      while !(1 > j) {
        cpoly__s(st.hr, j, cpoly__g(st.hr, j - 1))
        cpoly__s(st.hi, j, cpoly__g(st.hi, j - 1))
        j -= 1
      }
      cpoly__s(st.hr, 0, 0.0)
      cpoly__s(st.hi, 0, 0.0)
    }
  }
}

///|
fn fxshft_sl(l2 : Value) -> Value raise {
  cpoly__fxshft(to_int(l2))
  Nil
}

///|
fn cpoly__fxshft(l2 : Int) -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  let mut test_ = true
  let mut pasd = false
  let mut otr = 0.0
  let mut oti = 0.0
  let mut svsr = 0.0
  let mut svsi = 0.0
  ist.bool_ = false
  st.pvr = 0.0
  st.pvi = 0.0
  cpoly__polyev()
  ist.conv = false
  cpoly__calct()
  for j in 1..=l2 {
    otr = st.tr
    oti = st.ti
    cpoly__nexth()
    cpoly__calct()
    st.zr = cpoly__add(st.sr, st.tr)
    st.zi = cpoly__add(st.si, st.ti)
    if !ist.bool_ && test_ && j != l2 {
      if cpoly__mul(0.5, cpoly__cmod(st.zr, st.zi)) >
        cpoly__cmod(cpoly__sub(st.tr, otr), cpoly__sub(st.ti, oti)) {
        if pasd {
          for i in 0..=ist.n {
            cpoly__s(st.shr, i, cpoly__g(st.hr, i))
            cpoly__s(st.shi, i, cpoly__g(st.hi, i))
          }
          svsr = st.sr
          svsi = st.si
          cpoly__vrshft(10) |> ignore
          if ist.conv {
            break
          }
          test_ = false
          for i in 0..=ist.n {
            cpoly__s(st.hr, i, cpoly__g(st.shr, i))
            cpoly__s(st.hi, i, cpoly__g(st.shi, i))
          }
          st.sr = svsr
          st.si = svsi
          cpoly__polyev()
          cpoly__calct()
        } else {
          pasd = true
        }
      } else {
        pasd = false
      }
    }
  }
  if !ist.conv {
    cpoly__vrshft(10) |> ignore
  }
}

///|
fn vrshft_sl(l3 : Value) -> Value raise {
  lbool(cpoly__vrshft(to_int(l3)))
}

///|
/// Returns true when the Lisp DO loop was left with (return t).
fn cpoly__vrshft(l3 : Int) -> Bool raise {
  let st = cpoly__f
  let ist = cpoly__i
  ist.conv = false
  st.sr = st.zr
  st.si = st.zi
  let mut bool1 = false
  let mut omp : Double? = None
  let mut relstp : Double? = None
  for i in 1..=l3 {
    cpoly__polyev()
    let mp = cpoly__cmod(st.pvr, st.pvi)
    let ms = cpoly__cmod(st.sr, st.si)
    if cpoly__mul(20.0, cpoly__errev(ms, mp)) > mp {
      ist.conv = true
      st.zr = st.sr
      st.zi = st.si
      return true
    }
    if i == 1 {
      omp = Some(mp)
    } else if bool1 || cpoly__val(omp) > mp || !(cpoly__val(relstp) < 0.05) {
      if cpoly__mul(0.1, mp) > cpoly__val(omp) {
        return true
      } else {
        omp = Some(mp)
      }
    } else {
      let mut tp = cpoly__val(relstp)
      bool1 = true
      if st.are > cpoly__val(relstp) {
        tp = st.are
      }
      let r1 = cpoly__sqrt(tp)
      let sr1 = cpoly__sub(
        cpoly__mul(cpoly__add(r1, 1.0), st.sr),
        cpoly__mul(r1, st.si),
      )
      st.si = cpoly__add(
        cpoly__mul(cpoly__add(r1, 1.0), st.si),
        cpoly__mul(r1, st.sr),
      )
      st.sr = sr1
      cpoly__polyev()
      for j in 1..=5 {
        ignore(j)
        cpoly__calct()
        cpoly__nexth()
      }
      omp = Some(st.infin)
    }
    cpoly__calct()
    cpoly__nexth()
    cpoly__calct()
    if !ist.bool_ {
      relstp = Some(
        cpoly__div(cpoly__cmod(st.tr, st.ti), cpoly__cmod(st.sr, st.si)),
      )
      st.sr = cpoly__add(st.sr, st.tr)
      st.si = cpoly__add(st.si, st.ti)
    }
  }
  false
}

///|
fn calct_sl() -> Value raise {
  cpoly__calct()
  Nil
}

///|
fn cpoly__calct() -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  let mut hvr = cpoly__g(st.hr, 0)
  cpoly__s(st.qhr, 0, hvr)
  let mut hvi = cpoly__g(st.hi, 0)
  cpoly__s(st.qhi, 0, hvi)
  for i in 1..=ist.n {
    let t_ = cpoly__sub(
      cpoly__add(cpoly__g(st.hr, i), cpoly__mul(hvr, st.sr)),
      cpoly__mul(hvi, st.si),
    )
    hvi = cpoly__add(
      cpoly__add(cpoly__g(st.hi, i), cpoly__mul(hvr, st.si)),
      cpoly__mul(hvi, st.sr),
    )
    cpoly__s(st.qhi, i, hvi)
    hvr = t_
    cpoly__s(st.qhr, i, hvr)
  }
  ist.bool_ = !(
    cpoly__cmod(hvr, hvi) >
    cpoly__mul(
      cpoly__mul(10.0, st.are),
      cpoly__cmod(cpoly__g(st.hr, ist.n), cpoly__g(st.hi, ist.n)),
    )
  )
  if !ist.bool_ {
    cpoly__cdivid(-st.pvr, -st.pvi, hvr, hvi)
    st.tr = st.cr
    st.ti = st.ci
  } else {
    st.tr = 0.0
    st.ti = 0.0
  }
}

///|
fn nexth_sl() -> Value raise {
  cpoly__nexth()
  Nil
}

///|
fn cpoly__nexth() -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  if ist.bool_ {
    for j in 1..=ist.n {
      cpoly__s(st.hr, j, cpoly__g(st.qhr, j - 1))
      cpoly__s(st.hi, j, cpoly__g(st.qhi, j - 1))
    }
    cpoly__s(st.hr, 0, 0.0)
    cpoly__s(st.hi, 0, 0.0)
  } else {
    for j in 1..=ist.n {
      let t1 = cpoly__g(st.qhr, j - 1)
      let t2 = cpoly__g(st.qhi, j - 1)
      cpoly__s(
        st.hr,
        j,
        cpoly__sub(
          cpoly__add(cpoly__g(st.qpr, j), cpoly__mul(t1, st.tr)),
          cpoly__mul(t2, st.ti),
        ),
      )
      cpoly__s(
        st.hi,
        j,
        cpoly__add(
          cpoly__add(cpoly__g(st.qpi, j), cpoly__mul(t1, st.ti)),
          cpoly__mul(t2, st.tr),
        ),
      )
    }
    cpoly__s(st.hr, 0, cpoly__g(st.qpr, 0))
    cpoly__s(st.hi, 0, cpoly__g(st.qpi, 0))
  }
}

///|
fn polyev_sl() -> Value raise {
  cpoly__polyev()
  Nil
}

///|
fn cpoly__polyev() -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  st.pvr = cpoly__g(st.pr, 0)
  cpoly__s(st.qpr, 0, st.pvr)
  st.pvi = cpoly__g(st.pi, 0)
  cpoly__s(st.qpi, 0, st.pvi)
  for i in 1..=ist.nn {
    let t_ = cpoly__sub(
      cpoly__add(cpoly__g(st.pr, i), cpoly__mul(st.pvr, st.sr)),
      cpoly__mul(st.pvi, st.si),
    )
    st.pvi = cpoly__add(
      cpoly__add(cpoly__g(st.pi, i), cpoly__mul(st.pvr, st.si)),
      cpoly__mul(st.pvi, st.sr),
    )
    cpoly__s(st.qpi, i, st.pvi)
    st.pvr = t_
    cpoly__s(st.qpr, i, st.pvr)
  }
}

///|
fn errev_sl(ms : Value, mp : Value) -> Value raise {
  Flo(cpoly__errev(to_double(ms), to_double(mp)))
}

///|
fn cpoly__errev(ms : Double, mp : Double) -> Double raise {
  let st = cpoly__f
  let ist = cpoly__i
  let mut e = cpoly__div(
    cpoly__mul(cpoly__cmod(cpoly__g(st.qpr, 0), cpoly__g(st.qpi, 0)), st.mre),
    cpoly__add(st.are, st.mre),
  )
  for j in 0..=ist.nn {
    e = cpoly__add(
      cpoly__cmod(cpoly__g(st.qpr, j), cpoly__g(st.qpi, j)),
      cpoly__mul(e, ms),
    )
  }
  cpoly__sub(
    cpoly__mul(e, cpoly__add(st.are, st.mre)),
    cpoly__mul(mp, st.mre),
  )
}

///|
/// Compute a lower bound on the roots of the polynomial.  Let the
/// polynomial be sum(a[k]*x^k,k,0,n).  Then the lower bound is the
/// smallest real root of sum(|a[k]|*x^k,k,0,n-1)-a[n].  For our
/// purposes, this lower bound is computed to an accuracy of .005 or
/// so.
fn cauchy_sl() -> Value raise {
  Flo(cpoly__cauchy())
}

///|
fn cpoly__cauchy() -> Double raise {
  let st = cpoly__f
  let ist = cpoly__i
  let nn = ist.nn
  let n = ist.n
  let mut x = cpoly__exp(
    cpoly__div(
      cpoly__sub(
        cpoly__log(cpoly__g(st.shr, nn)),
        cpoly__log(cpoly__g(st.shr, 0)),
      ),
      nn.to_double(),
    ),
  )
  let mut xm = 0.0
  cpoly__s(st.shr, nn, -cpoly__g(st.shr, nn))
  if cpoly__g(st.shr, n) != 0.0 {
    xm = -cpoly__div(cpoly__g(st.shr, nn), cpoly__g(st.shr, n))
    if x > xm {
      x = xm
    }
  }
  while true {
    xm = cpoly__mul(0.1, x)
    let mut f = cpoly__g(st.shr, 0)
    for i in 1..=nn {
      f = cpoly__add(cpoly__g(st.shr, i), cpoly__mul(f, xm))
    }
    if !(0.0 < f) {
      break
    }
    x = xm
  }
  let mut dx = x
  while !(5.0e-3 > cpoly__div(dx, x).abs()) {
    let mut f = cpoly__g(st.shr, 0)
    let mut df = f
    for i in 1..=n {
      f = cpoly__add(cpoly__mul(f, x), cpoly__g(st.shr, i))
      df = cpoly__add(cpoly__mul(df, x), f)
    }
    f = cpoly__add(cpoly__mul(f, x), cpoly__g(st.shr, nn))
    dx = cpoly__div(f, df)
    x = cpoly__sub(x, dx)
  }
  x
}

///|
/// Scale the coefficients of the polynomial to reduce the chance of
/// overflow or underflow.  This is different from the algorithm given
/// in TOMS 419 and 493 which just scales the coefficients by some
/// fixed factor.  Instead, this algorithm computes a scale factor for
/// the roots and adjusts the coefficients of the polynomial
/// appropriately.
///
/// The scale factor for the roots is in *polysc1*.  The roots are
/// scaled by 2^(*polysc1*).  There is an additional scaling *polysc*
/// such that the coefficients of the polynomial are all scaled by
/// 2^(*polysc*).
fn scale_sl() -> Value raise {
  cpoly__scale_sl()
  Nil
}

///|
fn cpoly__scale_sl() -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  let nn = ist.nn
  let mut j = 0
  let mut x = 0.0
  for i in 0..=nn {
    if cpoly__g(st.shr, i) == 0.0 {
      j = j + 1
    } else {
      x = cpoly__add(x, cpoly__log(cpoly__g(st.shr, i)))
    }
  }
  x = cpoly__div(x, (nn + 1 - j).to_double())
  let dx = cpoly__div(
    cpoly__sub(cpoly__log(cpoly__g(st.shr, nn)), cpoly__log(cpoly__g(st.shr, 0))),
    nn.to_double(),
  )
  ist.polysc1 = cpoly__floor(cpoly__add(0.5, cpoly__div(dx, st.logbas)))
  x = cpoly__add(
    x,
    cpoly__mul(cpoly__mul((ist.polysc1 * nn).to_double(), st.logbas), 0.5),
  )
  ist.polysc = cpoly__floor(cpoly__add(0.5, cpoly__div(x, st.logbas)))
  let mut j = -ist.polysc
  let mut i = nn
  while !(i < 0) {
    cpoly__s(st.pr, i, cpoly__scale(cpoly__g(st.pr, i), j))
    cpoly__s(st.pi, i, cpoly__scale(cpoly__g(st.pi, i), j))
    i -= 1
    j = j + ist.polysc1
  }
}

///|
fn cdivid_sl(ar : Value, ai : Value, br : Value, bi : Value) -> Value raise {
  cpoly__cdivid(to_double(ar), to_double(ai), to_double(br), to_double(bi))
  Nil
}

///|
fn cpoly__cdivid(ar : Double, ai : Double, br : Double, bi : Double) -> Unit raise {
  let st = cpoly__f
  let mut bi = bi
  let mut br = br
  if br == 0.0 && bi == 0.0 {
    st.ci = st.infin
    st.cr = st.ci
  } else if bi.abs() > br.abs() {
    let r1 = cpoly__div(br, bi)
    bi = cpoly__add(bi, cpoly__mul(br, r1))
    br = cpoly__add(ai, cpoly__mul(ar, r1))
    st.cr = cpoly__div(br, bi)
    br = cpoly__sub(cpoly__mul(ai, r1), ar)
    st.ci = cpoly__div(br, bi)
  } else {
    let r1 = cpoly__div(bi, br)
    bi = cpoly__add(br, cpoly__mul(bi, r1))
    br = cpoly__add(ar, cpoly__mul(ai, r1))
    st.cr = cpoly__div(br, bi)
    br = cpoly__sub(ai, cpoly__mul(ar, r1))
    st.ci = cpoly__div(br, bi)
  }
}

///|
fn cmod_sl(ar : Value, ai : Value) -> Value raise {
  Flo(cpoly__cmod(to_double(ar), to_double(ai)))
}

///|
fn cpoly__cmod(ar : Double, ai : Double) -> Double raise {
  let mut ar = ar.abs()
  let mut ai = ai.abs()
  if ai > ar {
    ar = cpoly__div(ar, ai)
    cpoly__mul(ai, cpoly__sqrt(cpoly__add(cpoly__mul(ar, ar), 1.0)))
  } else if ar > ai {
    ai = cpoly__div(ai, ar)
    cpoly__mul(ar, cpoly__sqrt(cpoly__add(cpoly__mul(ai, ai), 1.0)))
  } else {
    cpoly__mul(cpoly__sqrt(2.0), ar)
  }
}

// ---------------------------------------------------------------------------
// This is the algorithm for doing real polynomials.  It is algorithm 493
// from acm toms vol 1 p 178 (1975) by jenkins.  Note that array indexing
// starts from 0.  The names of the arrays have been changed to be the same
// as for cpoly.  The correspondence is: p - pr-sl, qp - qpr-sl, k - hr-sl,
// qk - qhr-sl, svk - shr-sl, temp - shi-sl.  the roots *are* put in pr-sl
// and pi-sl.  The variable *si* appears not to be used here

///|
fn rpoly_sl(degree : Value) -> Value raise {
  cpoly__rpoly(to_int(degree))
  Nil
}

///|
fn cpoly__rpoly(degree : Int) -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  let mut degree = degree
  let polyfactor = () => symval(q_d_polyfactor).truthy()
  st.logbas = cpoly__log(2.0)
  st.infin = cpoly__most_positive_flonum
  st.are = cpoly__flonum_epsilon
  st.mre = 0.0
  let mut xx = cpoly__sqrt(0.5) // sqrt(0.5)
  let mut yy = 0.0
  let (cosr, sinr) = cpoly__rot94()
  let mut aa = 0.0
  let mut cc = 0.0
  let mut bb = 0.0
  let mut bnd = 0.0
  st.sr = 0.0
  st.u = 0.0
  st.v = 0.0
  let mut t1 = 0.0
  st.szr = 0.0
  st.szi = 0.0
  st.lzr = 0.0
  st.lzi = 0.0
  ist.nz = 0
  ist.n = 0
  ist.polysc = 0
  ist.polysc1 = 0
  let mut zerok = false
  let mut conv1 = true
  st.mre = st.are
  yy = -xx
  let mut i = degree
  while cpoly__g(st.pr, i) == 0.0 {
    i -= 1
  }
  ist.nn = i
  ist.n = i - 1
  degree = ist.nn
  for i in 0..=ist.nn {
    cpoly__s(st.shr, i, cpoly__g(st.pr, i).abs())
  }
  if ist.nn > 0 {
    cpoly__scale_sl()
  }
  // Loop to find all roots
  while true {
    if ist.nn < 3 {
      if ist.nn == 2 {
        // Solve the final quadratic polynomial
        cpoly__quad(cpoly__g(st.pr, 0), cpoly__g(st.pr, 1), cpoly__g(st.pr, 2))
        if polyfactor() && st.szi != 0.0 {
          cpoly__s(st.pr, 2, cpoly__div(cpoly__g(st.pr, 2), cpoly__g(st.pr, 0)))
          cpoly__s(st.pr, 1, cpoly__div(cpoly__g(st.pr, 1), cpoly__g(st.pr, 0)))
          cpoly__s(st.pi, 2, 1.0)
        } else {
          cpoly__s(st.pr, 2, st.szr)
          cpoly__s(st.pi, 2, st.szi)
          cpoly__s(st.pr, 1, st.lzr)
          cpoly__s(st.pi, 1, st.lzi)
        }
      } else {
        // Solve the final linear polynomial
        cpoly__s(st.pr, 1, -cpoly__div(cpoly__g(st.pr, 1), cpoly__g(st.pr, 0)))
      }
      ist.nn = 0
      break
    }
    // Calculate a lower bound on the modulus of the zeros.
    for i in 0..=ist.nn {
      cpoly__s(st.shr, i, cpoly__g(st.pr, i).abs())
    }
    bnd = cpoly__cauchy()

    // Compute derivative of polynomial.  Save result in *hr-sl*.
    for i in 1..=ist.n {
      cpoly__s(
        st.hr,
        i,
        cpoly__div(
          cpoly__mul((ist.n - i).to_double(), cpoly__g(st.pr, i)),
          ist.n.to_double(),
        ),
      )
    }
    cpoly__s(st.hr, 0, cpoly__g(st.pr, 0))
    aa = cpoly__g(st.pr, ist.nn)
    bb = cpoly__g(st.pr, ist.n)
    zerok = cpoly__g(st.hr, ist.n) == 0.0
    // Do 5 steps with no shift.
    for jj in 1..=5 {
      ignore(jj)
      cc = cpoly__g(st.hr, ist.n)
      if zerok {
        let mut j = ist.n
        while !(j < 1) {
          cpoly__s(st.hr, j, cpoly__g(st.hr, j - 1))
          j -= 1
        }
        cpoly__s(st.hr, 0, 0.0)
        zerok = cpoly__g(st.hr, ist.n) == 0.0
      } else {
        t1 = -cpoly__div(aa, cc)
        let mut j = ist.n
        while !(j < 1) {
          cpoly__s(
            st.hr,
            j,
            cpoly__add(
              cpoly__mul(t1, cpoly__g(st.hr, j - 1)),
              cpoly__g(st.pr, j),
            ),
          )
          j -= 1
        }
        cpoly__s(st.hr, 0, cpoly__g(st.pr, 0))
        zerok = !(
          cpoly__g(st.hr, ist.n).abs() >
          cpoly__mul(cpoly__mul(bb.abs(), st.are), 10.0)
        )
      }
    }
    for i in 0..=ist.n {
      cpoly__s(st.shi, i, cpoly__g(st.hr, i))
    }
    let mut found = false
    for cnt in 1..=20 {
      let xx1 = cpoly__sub(cpoly__mul(cosr, xx), cpoly__mul(sinr, yy))
      yy = cpoly__add(cpoly__mul(sinr, xx), cpoly__mul(cosr, yy))
      xx = xx1
      st.sr = cpoly__mul(bnd, xx)
      st.u = cpoly__mul(-2.0, st.sr)
      st.v = bnd
      cpoly__fxshfr(20 * cnt)
      if ist.nz > 0 {
        cpoly__s(st.pr, ist.nn, st.szr)
        cpoly__s(st.pi, ist.nn, st.szi)
        if ist.nz == 2 {
          cpoly__s(st.pr, ist.n, st.lzr)
          cpoly__s(st.pi, ist.n, st.lzi)
          if polyfactor() && st.szi != 0.0 {
            cpoly__s(st.pr, ist.nn, st.v)
            cpoly__s(st.pr, ist.n, st.u)
            cpoly__s(st.pi, ist.nn, 1.0)
          }
        }
        ist.nn = ist.nn - ist.nz
        ist.n = ist.nn - 1
        for i in 0..=ist.nn {
          cpoly__s(st.pr, i, cpoly__g(st.qpr, i))
        }
        found = true
        break
      }
      for i in 0..=ist.n {
        cpoly__s(st.hr, i, cpoly__g(st.shi, i))
      }
    }
    if !found {
      conv1 = false
    }
    if !conv1 {
      break
    }
  }
  if polyfactor() {
    let mut i = degree
    while i != ist.nn {
      if cpoly__g(st.pi, i) == 0.0 {
        cpoly__s(st.pr, i, cpoly__scale(cpoly__g(st.pr, i), ist.polysc1))
      } else {
        cpoly__s(st.pr, i, cpoly__scale(cpoly__g(st.pr, i), 2 * ist.polysc1))
        i = i - 1
        cpoly__s(st.pr, i, cpoly__scale(cpoly__g(st.pr, i), ist.polysc1))
      }
      i -= 1
    }
  } else {
    for i in (ist.nn + 1)..=degree {
      cpoly__s(st.pr, i, cpoly__scale(cpoly__g(st.pr, i), ist.polysc1))
      cpoly__s(st.pi, i, cpoly__scale(cpoly__g(st.pi, i), ist.polysc1))
    }
  }
  let mut j = ist.polysc - ist.polysc1 * degree
  for i in 0..=ist.nn {
    cpoly__s(st.pr, i, cpoly__scale(cpoly__g(st.pr, i), j))
    j = j + ist.polysc1
  }
}

///|
fn fxshfr_sl(l2 : Value) -> Value raise {
  cpoly__fxshfr(to_int(l2))
  Nil
}

///|
fn cpoly__fxshfr(l2 : Int) -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  ist.my_type = 0
  st.a = 0.0
  st.b = 0.0
  st.c = 0.0
  st.d = 0.0
  st.e = 0.0
  st.f = 0.0
  st.g = 0.0
  st.h = 0.0
  st.a1 = 0.0
  st.a3 = 0.0
  st.a7 = 0.0
  ist.nz = 0
  cpoly__quadsd()
  cpoly__calcsc()
  let mut betav = 0.25
  let mut betas = 0.25
  let mut oss = st.sr
  let mut ovv = st.v
  let mut ots = 0.0
  let mut otv = 0.0
  for j in 1..=l2 {
    cpoly__nextk()
    cpoly__calcsc()
    cpoly__newest()
    let vv = st.vi
    let mut ss = 0.0
    if cpoly__g(st.hr, ist.n) != 0.0 {
      ss = -cpoly__div(cpoly__g(st.pr, ist.nn), cpoly__g(st.hr, ist.n))
    }
    let mut tv = 1.0
    let mut ts = 1.0
    if !(j == 1 || ist.my_type == 3) {
      if vv != 0.0 {
        tv = cpoly__div(cpoly__sub(vv, ovv), vv).abs()
      }
      if ss != 0.0 {
        ts = cpoly__div(cpoly__sub(ss, oss), ss).abs()
      }
      let mut tvv = 1.0
      if tv < otv {
        tvv = cpoly__mul(tv, otv)
      }
      let mut tss = 1.0
      if ts < ots {
        tss = cpoly__mul(ts, ots)
      }
      let vpass = tvv < betav
      let spass = tss < betas
      if spass || vpass {
        let svu = st.u
        let svv = st.v
        for i in 0..=ist.n {
          cpoly__s(st.shr, i, cpoly__g(st.hr, i))
        }
        st.s = ss
        let mut vtry = false
        let mut stry = false
        let mut bool_ = !(spass && (!vpass || tss < tvv))
        // The inner DO returns T when a zero has been found.
        let mut found = false
        while true {
          let mut l50 = false
          if bool_ {
            cpoly__quadit()
            if ist.nz > 0 {
              found = true
              break
            }
            vtry = true
            betav = cpoly__mul(0.25, betav)
            if stry || !spass {
              l50 = true
            } else {
              for i in 0..=ist.n {
                cpoly__s(st.hr, i, cpoly__g(st.shr, i))
              }
            }
          }
          if !l50 {
            let iflag = cpoly__realit()
            if ist.nz > 0 {
              found = true
              break
            }
            stry = true
            betas = cpoly__mul(0.25, betas)
            if iflag == 0 {
              l50 = true
            } else {
              st.ui = -cpoly__add(st.s, st.s)
              st.vi = cpoly__mul(st.s, st.s)
            }
          }
          if l50 {
            st.u = svu
            st.v = svv
            for i in 0..=ist.n {
              cpoly__s(st.hr, i, cpoly__g(st.shr, i))
            }
            if !vpass || vtry {
              break
            }
          }
          bool_ = true
        }
        if found {
          return
        }
        cpoly__quadsd()
        cpoly__calcsc()
      }
    }
    ovv = vv
    oss = ss
    otv = tv
    ots = ts
  }
}

///|
fn quadit_sl() -> Value raise {
  cpoly__quadit()
  Nil
}

///|
fn cpoly__quadit() -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  ist.nz = 0
  st.u = st.ui
  st.v = st.vi
  let mut tried = false
  let mut j = 0
  let mut relstp : Double? = None
  let mut omp : Double? = None
  while true {
    cpoly__quad(1.0, st.u, st.v)
    if cpoly__sub(st.szr.abs(), st.lzr.abs()).abs() >
      cpoly__mul(1.0e-2, st.lzr.abs()) {
      return
    }
    cpoly__quadsd()
    let mp = cpoly__add(
      cpoly__sub(st.a, cpoly__mul(st.szr, st.b)).abs(),
      cpoly__mul(st.szi, st.b).abs(),
    )
    let ms = cpoly__cmod(st.szr, st.szi)
    let ee = cpoly__errev(ms, mp)
    if !(mp > cpoly__mul(2.0e1, ee)) {
      ist.nz = 2
      return
    }
    j = j + 1
    if j > 20 {
      return
    }
    if !(
        j < 2 ||
        cpoly__val(relstp) > 1.0e-2 ||
        mp < cpoly__val(omp) ||
        tried
      ) {
      if cpoly__val(relstp) < st.are {
        relstp = Some(st.are)
      }
      relstp = Some(cpoly__sqrt(cpoly__val(relstp)))
      st.u = cpoly__sub(st.u, cpoly__mul(st.u, cpoly__val(relstp)))
      st.v = cpoly__add(st.v, cpoly__mul(st.v, cpoly__val(relstp)))
      cpoly__quadsd()
      for i in 1..=5 {
        ignore(i)
        cpoly__calcsc()
        cpoly__nextk()
      }
      tried = true
      j = 0
    }
    omp = Some(mp)
    cpoly__calcsc()
    cpoly__nextk()
    cpoly__calcsc()
    cpoly__newest()
    if st.vi == 0.0 {
      return
    }
    relstp = Some(cpoly__div(cpoly__sub(st.vi, st.v), st.vi).abs())
    st.u = st.ui
    st.v = st.vi
  }
}

///|
fn realit_sl() -> Value raise {
  int(cpoly__realit())
}

///|
fn cpoly__realit() -> Int raise {
  let st = cpoly__f
  let ist = cpoly__i
  ist.nz = 0
  let mut j = 0
  let mut t1 : Double? = None
  let mut omp : Double? = None
  while true {
    let mut pv = cpoly__g(st.pr, 0)
    cpoly__s(st.qpr, 0, pv)
    for i in 1..=ist.nn {
      pv = cpoly__add(cpoly__mul(pv, st.s), cpoly__g(st.pr, i))
      cpoly__s(st.qpr, i, pv)
    }
    let mp = pv.abs()
    let ms = st.s.abs()
    let mut ee = cpoly__mul(
      cpoly__div(st.mre, cpoly__add(st.are, st.mre)),
      cpoly__g(st.qpr, 0).abs(),
    )
    for i in 1..=ist.nn {
      ee = cpoly__add(cpoly__mul(ee, ms), cpoly__g(st.qpr, i).abs())
    }
    if !(
        mp >
        cpoly__mul(
          2.0e1,
          cpoly__sub(
            cpoly__mul(cpoly__add(st.are, st.mre), ee),
            cpoly__mul(st.mre, mp),
          ),
        )
      ) {
      ist.nz = 1
      st.szr = st.s
      st.szi = 0.0
      return 0
    }
    j = j + 1
    if j > 10 {
      return 0
    }
    if !(
        j < 2 ||
        cpoly__val(t1).abs() >
        cpoly__mul(1.0e-3, cpoly__sub(st.s, cpoly__val(t1)).abs()) ||
        !(mp > cpoly__val(omp))
      ) {
      return 1
    }
    omp = Some(mp)
    let mut kv = cpoly__g(st.hr, 0)
    cpoly__s(st.qhr, 0, kv)
    for i in 1..=ist.n {
      kv = cpoly__add(cpoly__mul(kv, st.s), cpoly__g(st.hr, i))
      cpoly__s(st.qhr, i, kv)
    }
    if kv.abs() >
      cpoly__mul(cpoly__mul(cpoly__g(st.hr, ist.n).abs(), 1.0e1), st.are) {
      let tt = -cpoly__div(pv, kv)
      t1 = Some(tt)
      cpoly__s(st.hr, 0, cpoly__g(st.qpr, 0))
      for i in 1..=ist.n {
        cpoly__s(
          st.hr,
          i,
          cpoly__add(cpoly__mul(tt, cpoly__g(st.qhr, i - 1)), cpoly__g(st.qpr, i)),
        )
      }
    } else {
      cpoly__s(st.hr, 0, 0.0)
      for i in 1..=ist.n {
        cpoly__s(st.hr, i, cpoly__g(st.qhr, i - 1))
      }
    }
    kv = cpoly__g(st.hr, 0)
    for i in 1..=ist.n {
      kv = cpoly__add(cpoly__mul(kv, st.s), cpoly__g(st.hr, i))
    }
    t1 = Some(0.0)
    if kv.abs() >
      cpoly__mul(cpoly__mul(cpoly__g(st.hr, ist.n).abs(), 10.0), st.are) {
      t1 = Some(-cpoly__div(pv, kv))
    }
    st.s = cpoly__add(st.s, cpoly__val(t1))
  }
  0
}

///|
fn calcsc_sl() -> Value raise {
  cpoly__calcsc()
  Nil
}

///|
fn cpoly__calcsc() -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  st.d = cpoly__g(st.hr, 0)
  cpoly__s(st.qhr, 0, st.d)
  st.c = cpoly__sub(cpoly__g(st.hr, 1), cpoly__mul(st.u, st.d))
  cpoly__s(st.qhr, 1, st.c)
  for i in 2..=ist.n {
    let c0 = cpoly__sub(
      cpoly__sub(cpoly__g(st.hr, i), cpoly__mul(st.u, st.c)),
      cpoly__mul(st.v, st.d),
    )
    cpoly__s(st.qhr, i, c0)
    st.d = st.c
    st.c = c0
  }
  if !(
      st.c.abs() >
      cpoly__mul(cpoly__mul(cpoly__g(st.hr, ist.n).abs(), 1.0e2), st.are) ||
      st.d.abs() >
      cpoly__mul(cpoly__mul(cpoly__g(st.hr, ist.n - 1).abs(), 1.0e2), st.are)
    ) {
    ist.my_type = 3
  } else if !(st.d.abs() < st.c.abs()) {
    ist.my_type = 2
    st.e = cpoly__div(st.a, st.d)
    st.f = cpoly__div(st.c, st.d)
    st.g = cpoly__mul(st.u, st.b)
    st.h = cpoly__mul(st.v, st.b)
    st.a3 = cpoly__add(
      cpoly__mul(cpoly__add(st.a, st.g), st.e),
      cpoly__mul(st.h, cpoly__div(st.b, st.d)),
    )
    st.a1 = cpoly__sub(cpoly__mul(st.b, st.f), st.a)
    st.a7 = cpoly__add(cpoly__mul(cpoly__add(st.f, st.u), st.a), st.h)
  } else {
    ist.my_type = 1
    st.e = cpoly__div(st.a, st.c)
    st.f = cpoly__div(st.d, st.c)
    st.g = cpoly__mul(st.u, st.e)
    st.h = cpoly__mul(st.v, st.b)
    st.a3 = cpoly__add(
      cpoly__mul(st.a, st.e),
      cpoly__mul(cpoly__add(cpoly__div(st.h, st.c), st.g), st.b),
    )
    st.a1 = cpoly__sub(st.b, cpoly__mul(st.a, cpoly__div(st.d, st.c)))
    st.a7 = cpoly__add(
      cpoly__add(st.a, cpoly__mul(st.g, st.d)),
      cpoly__mul(st.h, st.f),
    )
  }
}

///|
fn nextk_sl() -> Value raise {
  cpoly__nextk()
  Nil
}

///|
fn cpoly__nextk() -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  if ist.my_type == 3 {
    cpoly__s(st.hr, 0, 0.0)
    cpoly__s(st.hr, 1, 0.0)
    for i in 2..=ist.n {
      cpoly__s(st.hr, i, cpoly__g(st.qhr, i - 2))
    }
  } else if st.a1.abs() >
    cpoly__mul(
      cpoly__mul((if ist.my_type == 1 { st.b } else { st.a }).abs(), 1.0e1),
      st.are,
    ) {
    st.a7 = cpoly__div(st.a7, st.a1)
    st.a3 = cpoly__div(st.a3, st.a1)
    cpoly__s(st.hr, 0, cpoly__g(st.qpr, 0))
    cpoly__s(
      st.hr,
      1,
      cpoly__sub(cpoly__g(st.qpr, 1), cpoly__mul(st.a7, cpoly__g(st.qpr, 0))),
    )
    for i in 2..=ist.n {
      cpoly__s(
        st.hr,
        i,
        cpoly__add(
          cpoly__add(
            cpoly__mul(st.a3, cpoly__g(st.qhr, i - 2)),
            -cpoly__mul(st.a7, cpoly__g(st.qpr, i - 1)),
          ),
          cpoly__g(st.qpr, i),
        ),
      )
    }
  } else {
    cpoly__s(st.hr, 0, 0.0)
    cpoly__s(st.hr, 1, -cpoly__mul(st.a7, cpoly__g(st.qpr, 0)))
    for i in 2..=ist.n {
      cpoly__s(
        st.hr,
        i,
        cpoly__sub(
          cpoly__mul(st.a3, cpoly__g(st.qhr, i - 2)),
          cpoly__mul(st.a7, cpoly__g(st.qpr, i - 1)),
        ),
      )
    }
  }
}

///|
fn newest_sl() -> Value raise {
  cpoly__newest()
  Nil
}

///|
fn cpoly__newest() -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  let mut a4 = 0.0
  let mut a5 = 0.0
  if ist.my_type == 3 {
    st.ui = 0.0
    st.vi = 0.0
  } else {
    if ist.my_type == 2 {
      a4 = cpoly__add(cpoly__mul(cpoly__add(st.a, st.g), st.f), st.h)
      a5 = cpoly__add(
        cpoly__mul(cpoly__add(st.f, st.u), st.c),
        cpoly__mul(st.v, st.d),
      )
    } else {
      a4 = cpoly__add(
        cpoly__add(st.a, cpoly__mul(st.u, st.b)),
        cpoly__mul(st.h, st.f),
      )
      a5 = cpoly__add(
        st.c,
        cpoly__mul(cpoly__add(st.u, cpoly__mul(st.v, st.f)), st.d),
      )
    }
    let b1 = -cpoly__div(cpoly__g(st.hr, ist.n), cpoly__g(st.pr, ist.nn))
    let b2 = -cpoly__div(
      cpoly__add(cpoly__g(st.hr, ist.n - 1), cpoly__mul(b1, cpoly__g(st.pr, ist.n))),
      cpoly__g(st.pr, ist.nn),
    )
    let mut c1 = cpoly__mul(cpoly__mul(st.v, b2), st.a1)
    let c2 = cpoly__mul(b1, st.a7)
    let c3 = cpoly__mul(cpoly__mul(b1, b1), st.a3)
    let c4 = cpoly__sub(cpoly__sub(c1, c2), c3)
    c1 = cpoly__add(cpoly__add(a5, cpoly__mul(b1, a4)), -c4)
    if c1 == 0.0 {
      st.ui = 0.0
      st.vi = 0.0
    } else {
      st.ui = cpoly__sub(
        st.u,
        cpoly__div(
          cpoly__add(
            cpoly__mul(st.u, cpoly__add(c3, c2)),
            cpoly__mul(
              st.v,
              cpoly__add(cpoly__mul(b1, st.a1), cpoly__mul(b2, st.a7)),
            ),
          ),
          c1,
        ),
      )
      st.vi = cpoly__mul(st.v, cpoly__add(cpoly__div(c4, c1), 1.0))
    }
  }
}

///|
/// Divide the polynomial in *pr-sl* by the quadratic x^2 + (*u*)*x +
/// (*v*).  Place the quotient in *qpr-sl* and the remainder in *a* and
/// *b*.  I (rtoy) think the remainder polynomial is (*b*)*x + (*a*).
fn quadsd_sl() -> Value raise {
  cpoly__quadsd()
  Nil
}

///|
fn cpoly__quadsd() -> Unit raise {
  let st = cpoly__f
  let ist = cpoly__i
  st.b = cpoly__g(st.pr, 0)
  cpoly__s(st.qpr, 0, st.b)
  st.a = cpoly__sub(cpoly__g(st.pr, 1), cpoly__mul(st.u, st.b))
  cpoly__s(st.qpr, 1, st.a)
  for i in 2..=ist.nn {
    let c0 = cpoly__sub(
      cpoly__sub(cpoly__g(st.pr, i), cpoly__mul(st.u, st.a)),
      cpoly__mul(st.v, st.b),
    )
    cpoly__s(st.qpr, i, c0)
    st.b = st.a
    st.a = c0
  }
}

///|
/// Compute the zeros of the quadratic a0*z^2+b1*z+c0.  The larger zero
/// is returned in *szr* and *szi*.  The smaller zero is in *lzr* and
/// *lzi*.
fn quad_sl(a0 : Value, b1 : Value, c0 : Value) -> Value raise {
  cpoly__quad(to_double(a0), to_double(b1), to_double(c0))
  Nil
}

///|
fn cpoly__quad(a0 : Double, b1 : Double, c0 : Double) -> Unit raise {
  let st = cpoly__f
  st.szr = 0.0
  st.szi = 0.0
  st.lzr = 0.0
  st.lzi = 0.0
  // *e* is rebound locally here.
  let mut b0 = 0.0
  let mut l0 = 0.0
  let mut e = 0.0
  // Handle the degenerate cases of a0 = 0 or c0 = 0 first.
  if a0 == 0.0 {
    if b1 != 0.0 {
      st.szr = -cpoly__div(c0, b1)
    }
  } else if c0 == 0.0 {
    st.lzr = -cpoly__div(b1, a0)
  } else {
    // Quadratic formula.
    b0 = cpoly__div(b1, 2.0)
    if b0.abs() < c0.abs() {
      e = a0
      if c0 < 0.0 {
        e = -a0
      }
      e = cpoly__sub(cpoly__mul(b0, cpoly__div(b0, c0.abs())), e)
      l0 = cpoly__mul(cpoly__sqrt(e.abs()), cpoly__sqrt(c0.abs()))
    } else {
      e = cpoly__sub(1.0, cpoly__mul(cpoly__div(a0, b0), cpoly__div(c0, b0)))
      l0 = cpoly__mul(cpoly__sqrt(e.abs()), b0.abs())
    }
    if e < 0.0 {
      st.szr = -cpoly__div(b0, a0)
      st.lzr = st.szr
      st.szi = cpoly__div(l0, a0).abs()
      st.lzi = -st.szi
    } else {
      if !(b0 < 0.0) {
        l0 = -l0
      }
      st.lzr = cpoly__div(cpoly__sub(l0, b0), a0)
      if st.lzr != 0.0 {
        st.szr = cpoly__div(cpoly__div(c0, st.lzr), a0)
      }
    }
  }
}

///|
fn init_cpoly() -> Unit raise {
  ()
}
