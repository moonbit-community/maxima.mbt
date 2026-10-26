// Port of src/cpoly.lisp, part 2: $BFALLROOTS.
//
// This is a very straightforward conversion of $allroots to use bfloats
// instead of floats.  Bigfloat values here are the FP lists
// (mantissa exponent) of float.lisp.  The integer state (*nn*, *n*,
// *polysc*, ...) is shared with part 1 (`cpoly__i`).

///|
/// Bigfloat state: the arrays *pr-sl* ... *qhi-sl* and the scalar
/// specials of the bigfloat version.
priv struct CpolyBState {
  mut pr : Array[Value]
  mut pi : Array[Value]
  mut shr : Array[Value]
  mut shi : Array[Value]
  mut qpr : Array[Value]
  mut qpi : Array[Value]
  mut hr : Array[Value]
  mut hi : Array[Value]
  mut qhr : Array[Value]
  mut qhi : Array[Value]
  mut logbas : Value
  mut infin : Value
  mut are : Value
  mut mre : Value
  mut cr : Value
  mut ci : Value
  mut sr : Value
  mut si : Value
  mut tr : Value
  mut ti : Value
  mut zr : Value
  mut zi : Value
  mut pvr : Value
  mut pvi : Value
  mut u : Value
  mut v : Value
  mut a : Value
  mut b : Value
  mut c : Value
  mut d : Value
  mut a1 : Value
  mut a3 : Value
  mut a7 : Value
  mut e : Value
  mut f : Value
  mut g : Value
  mut h : Value
  mut szr : Value
  mut szi : Value
  mut lzr : Value
  mut lzi : Value
  mut ui : Value
  mut vi : Value
  mut s : Value
}

///|
let cpoly__b : CpolyBState = {
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
  logbas: Nil,
  infin: Nil,
  are: Nil,
  mre: Nil,
  cr: Nil,
  ci: Nil,
  sr: Nil,
  si: Nil,
  tr: Nil,
  ti: Nil,
  zr: Nil,
  zi: Nil,
  pvr: Nil,
  pvi: Nil,
  u: Nil,
  v: Nil,
  a: Nil,
  b: Nil,
  c: Nil,
  d: Nil,
  a1: Nil,
  a3: Nil,
  a7: Nil,
  e: Nil,
  f: Nil,
  g: Nil,
  h: Nil,
  szr: Nil,
  szi: Nil,
  lzr: Nil,
  lzi: Nil,
  ui: Nil,
  vi: Nil,
  s: Nil,
}

///|
/// Checked `(aref a i)`.
fn cpoly__bg(a : Array[Value], i : Int) -> Value raise {
  if i < 0 || i >= a.length() {
    raise LispError::SimpleError(
      "Invalid index \{i} for (SIMPLE-VECTOR \{a.length()}), should be a non-negative integer below \{a.length()}.",
    )
  }
  a[i]
}

///|
/// Checked `(setf (aref a i) v)`.
fn cpoly__bs(a : Array[Value], i : Int, v : Value) -> Unit raise {
  if i < 0 || i >= a.length() {
    raise LispError::SimpleError(
      "Invalid index \{i} for (SIMPLE-VECTOR \{a.length()}), should be a non-negative integer below \{a.length()}.",
    )
  }
  a[i] = v
}

///|
/// `(intofp x)` for a fixnum.
fn cpoly__fp(x : Int) -> Value raise {
  intofp(int(x))
}

///|
/// `(intofp x)` for a double literal.
fn cpoly__fpd(x : Double) -> Value raise {
  intofp(Flo(x))
}

///|
fn cpoly__gtp(a : Value, b : Value) -> Bool raise {
  fpgreaterp(a, b).truthy()
}

///|
fn cpoly__zp(x : Value) -> Bool raise {
  fpzerop(x).truthy()
}

///|
/// `(cdr *bfhalf*)`
fn cpoly__half() -> Value {
  cdr(symval(q_ear_bfhalf))
}

///|
/// `(ceiling fpprec 56)`
fn cpoly__prec_factor() -> Int raise {
  to_int(num_ceiling(symval(q_fpprec), b=Fix(56L)).0)
}

///|
fn bf__cpoly_err(expr : Value) -> Value raise {
  merr("bfallroots: expected a polynomial; found ~M", [expr])
}

///|
fn fpzerop(x : Value) -> Value raise {
  lbool(equal(list2(Fix(0L), Fix(0L)), x))
}

///|
/// (ar+%i*ai)/(br+%i*bi) -> cr+%i*ci.
fn bf__cdivid_sl(ar : Value, ai : Value, br : Value, bi : Value) -> Value raise {
  let st = cpoly__b
  if cpoly__zp(br) && cpoly__zp(bi) {
    // Division by zero.  Should we do something else besides set
    // both parts to be "infinity"?
    st.ci = st.infin
    st.cr = st.ci
    st.cr
  } else if cpoly__gtp(fpabs(bi), fpabs(br)) {
    let r1 = fpquotient(br, bi)
    let bi = fpplus(bi, fptimes_star(br, r1))
    let br = fpplus(ai, fptimes_star(ar, r1))
    st.cr = fpquotient(br, bi)
    let br = fpdifference(fptimes_star(ai, r1), ar)
    st.ci = fpquotient(br, bi)
    st.ci
  } else {
    let r1 = fpquotient(bi, br)
    let bi = fpplus(br, fptimes_star(bi, r1))
    let br = fpplus(ar, fptimes_star(ai, r1))
    st.cr = fpquotient(br, bi)
    let br = fpdifference(ai, fptimes_star(ar, r1))
    st.ci = fpquotient(br, bi)
    st.ci
  }
}

///|
fn fpsqrt(x : Value) -> Value raise {
  fproot(bcons(x), Fix(2L))
}

///|
fn bf__cmod_sl(ar : Value, ai : Value) -> Value raise {
  let mut ar = fpabs(ar)
  let mut ai = fpabs(ai)
  if cpoly__gtp(ai, ar) {
    ar = fpquotient(ar, ai)
    fptimes_star(ai, fpsqrt(fpplus(fpone(), fptimes_star(ar, ar))))
  } else if cpoly__gtp(ar, ai) {
    ai = fpquotient(ai, ar)
    fptimes_star(ar, fpsqrt(fpplus(fpone(), fptimes_star(ai, ai))))
  } else {
    fptimes_star(fpsqrt(cpoly__fp(2)), ar)
  }
}

///|
fn bf__calct_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let mut hvr = cpoly__bg(st.hr, 0)
  cpoly__bs(st.qhr, 0, hvr)
  let mut hvi = cpoly__bg(st.hi, 0)
  cpoly__bs(st.qhi, 0, hvi)
  for i in 1..=ist.n {
    let tt = fpdifference(
      fpplus(cpoly__bg(st.hr, i), fptimes_star(hvr, st.sr)),
      fptimes_star(hvi, st.si),
    )
    hvi = fpplus(
      cpoly__bg(st.hi, i),
      fpplus(fptimes_star(hvr, st.si), fptimes_star(hvi, st.sr)),
    )
    cpoly__bs(st.qhi, i, hvi)
    hvr = tt
    cpoly__bs(st.qhr, i, hvr)
  }
  ist.bool_ = !cpoly__gtp(
    bf__cmod_sl(hvr, hvi),
    fptimes_star(
      cpoly__fp(10),
      fptimes_star(
        st.are,
        bf__cmod_sl(cpoly__bg(st.hr, ist.n), cpoly__bg(st.hi, ist.n)),
      ),
    ),
  )
  if !ist.bool_ {
    bf__cdivid_sl(fpminus(st.pvr), fpminus(st.pvi), hvr, hvi) |> ignore
    st.tr = st.cr
    st.ti = st.ci
  } else {
    st.tr = cpoly__fp(0)
    st.ti = cpoly__fp(0)
  }
  Nil
}

///|
fn bf__nexth_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  if ist.bool_ {
    for j in 1..=ist.n {
      cpoly__bs(st.hr, j, cpoly__bg(st.qhr, j - 1))
      cpoly__bs(st.hi, j, cpoly__bg(st.qhi, j - 1))
    }
    cpoly__bs(st.hr, 0, cpoly__fp(0))
    cpoly__bs(st.hi, 0, cpoly__fp(0))
  } else {
    for j in 1..=ist.n {
      let t1 = cpoly__bg(st.qhr, j - 1)
      let t2 = cpoly__bg(st.qhi, j - 1)
      cpoly__bs(
        st.hr,
        j,
        fpdifference(
          fpplus(cpoly__bg(st.qpr, j), fptimes_star(t1, st.tr)),
          fptimes_star(t2, st.ti),
        ),
      )
      cpoly__bs(
        st.hi,
        j,
        fpplus(
          cpoly__bg(st.qpi, j),
          fpplus(fptimes_star(t1, st.ti), fptimes_star(t2, st.tr)),
        ),
      )
    }
    cpoly__bs(st.hr, 0, cpoly__bg(st.qpr, 0))
    cpoly__bs(st.hi, 0, cpoly__bg(st.qpi, 0))
  }
  Nil
}

///|
fn bf__polyev_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  st.pvr = cpoly__bg(st.pr, 0)
  cpoly__bs(st.qpr, 0, st.pvr)
  st.pvi = cpoly__bg(st.pi, 0)
  cpoly__bs(st.qpi, 0, st.pvi)
  for i in 1..=ist.nn {
    let tt = fpdifference(
      fpplus(cpoly__bg(st.pr, i), fptimes_star(st.pvr, st.sr)),
      fptimes_star(st.pvi, st.si),
    )
    st.pvi = fpplus(
      cpoly__bg(st.pi, i),
      fpplus(fptimes_star(st.pvr, st.si), fptimes_star(st.pvi, st.sr)),
    )
    cpoly__bs(st.qpi, i, st.pvi)
    st.pvr = tt
    cpoly__bs(st.qpr, i, st.pvr)
  }
  Nil
}

///|
fn bf__errev_sl(ms : Value, mp : Value) -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let mut e = fpquotient(
    fptimes_star(
      bf__cmod_sl(cpoly__bg(st.qpr, 0), cpoly__bg(st.qpi, 0)),
      st.mre,
    ),
    fpplus(st.are, st.mre),
  )
  for j in 0..=ist.nn {
    e = fpplus(
      bf__cmod_sl(cpoly__bg(st.qpr, j), cpoly__bg(st.qpi, j)),
      fptimes_star(e, ms),
    )
  }
  fpdifference(
    fptimes_star(e, fpplus(st.are, st.mre)),
    fptimes_star(mp, st.mre),
  )
}

///|
fn bf__cauchy_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let nn = ist.nn
  let n = ist.n
  let mut x = fpexp(
    fpquotient(
      fpdifference(fplog(cpoly__bg(st.shr, nn)), fplog(cpoly__bg(st.shr, 0))),
      cpoly__fp(nn),
    ),
  )
  let mut xm = cpoly__fp(0)
  cpoly__bs(st.shr, nn, fpminus(cpoly__bg(st.shr, nn)))
  if !cpoly__zp(cpoly__bg(st.shr, n)) {
    xm = fpminus(fpquotient(cpoly__bg(st.shr, nn), cpoly__bg(st.shr, n)))
    if cpoly__gtp(x, xm) {
      x = xm
    }
  }
  while true {
    xm = fptimes_star(cpoly__fpd(0.1), x)
    let mut f = cpoly__bg(st.shr, 0)
    for i in 1..=nn {
      f = fpplus(cpoly__bg(st.shr, i), fptimes_star(f, xm))
    }
    if cpoly__gtp(cpoly__fp(0), f) {
      break
    }
    x = xm
  }
  let mut dx = x
  while !cpoly__gtp(cpoly__fpd(5.0e-3), fpabs(fpquotient(dx, x))) {
    let mut f = cpoly__bg(st.shr, 0)
    let mut df = f
    for i in 1..=n {
      f = fpplus(fptimes_star(f, x), cpoly__bg(st.shr, i))
      df = fpplus(fptimes_star(df, x), f)
    }
    f = fpplus(fptimes_star(f, x), cpoly__bg(st.shr, nn))
    dx = fpquotient(f, df)
    x = fpdifference(x, dx)
  }
  x
}

///|
fn bf__scale_float(bf : Value, scale : Value) -> Value raise {
  let mantissa = car(bf)
  let exp_ = cadr(bf)
  if zerop(mantissa) {
    list2(mantissa, Fix(0L))
  } else {
    list2(mantissa, num_add(exp_, scale))
  }
}

///|
fn bf__scale_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let nn = ist.nn
  let mut j = 0
  let mut x = cpoly__fp(0)
  for i in 0..=nn {
    if equal(cpoly__bg(st.shr, i), cpoly__fp(0)) {
      j = j + 1
    } else {
      x = fpplus(x, fplog(cpoly__bg(st.shr, i)))
    }
  }
  x = fpquotient(x, cpoly__fp(nn + 1 - j))
  let dx = fpquotient(
    fpdifference(fplog(cpoly__bg(st.shr, nn)), fplog(cpoly__bg(st.shr, 0))),
    cpoly__fp(nn),
  )
  ist.polysc1 = to_int(
    fpentier(bcons(fpplus(cpoly__half(), fpquotient(dx, st.logbas)))),
  )
  x = fpplus(
    x,
    fptimes_star(
      cpoly__fp(ist.polysc1 * nn),
      fptimes_star(st.logbas, cpoly__half()),
    ),
  )
  ist.polysc = to_int(
    fpentier(bcons(fpplus(cpoly__half(), fpquotient(x, st.logbas)))),
  )
  let mut j = -ist.polysc
  let mut i = nn
  while !(i < 0) {
    cpoly__bs(st.pr, i, bf__scale_float(cpoly__bg(st.pr, i), int(j)))
    cpoly__bs(st.pi, i, bf__scale_float(cpoly__bg(st.pi, i), int(j)))
    i -= 1
    j = j + ist.polysc1
  }
  Nil
}

///|
fn bf__noshft_sl(l1 : Value) -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let l1 = to_int(l1)
  let mut xni = cpoly__fp(ist.nn)
  let t1 = fpquotient(fpone(), cpoly__fp(ist.nn))
  for i in 0..=ist.n {
    cpoly__bs(
      st.hr,
      i,
      fptimes_star(cpoly__bg(st.pr, i), fptimes_star(xni, t1)),
    )
    cpoly__bs(
      st.hi,
      i,
      fptimes_star(cpoly__bg(st.pi, i), fptimes_star(xni, t1)),
    )
    xni = fpdifference(xni, cpoly__fp(1))
  }
  for jj in 1..=l1 {
    ignore(jj)
    let n = ist.n
    if cpoly__gtp(
        bf__cmod_sl(cpoly__bg(st.hr, n), cpoly__bg(st.hi, n)),
        fptimes_star(
          cpoly__fp(10),
          fptimes_star(
            st.are,
            bf__cmod_sl(cpoly__bg(st.pr, n), cpoly__bg(st.pi, n)),
          ),
        ),
      ) {
      bf__cdivid_sl(
        fpminus(cpoly__bg(st.pr, ist.nn)),
        fpminus(cpoly__bg(st.pi, ist.nn)),
        cpoly__bg(st.hr, n),
        cpoly__bg(st.hi, n),
      )
      |> ignore
      st.tr = st.cr
      st.ti = st.ci
      let mut j = n
      while !(1 > j) {
        let t1 = cpoly__bg(st.hr, j - 1)
        let t2 = cpoly__bg(st.hi, j - 1)
        cpoly__bs(
          st.hr,
          j,
          fpdifference(
            fpplus(cpoly__bg(st.pr, j), fptimes_star(t1, st.tr)),
            fptimes_star(t2, st.ti),
          ),
        )
        cpoly__bs(
          st.hi,
          j,
          fpplus(
            cpoly__bg(st.pi, j),
            fpplus(fptimes_star(t1, st.ti), fptimes_star(t2, st.tr)),
          ),
        )
        j -= 1
      }
      cpoly__bs(st.hr, 0, cpoly__bg(st.pr, 0))
      cpoly__bs(st.hi, 0, cpoly__bg(st.pi, 0))
    } else {
      let mut j = n
      while !(1 > j) {
        cpoly__bs(st.hr, j, cpoly__bg(st.hr, j - 1))
        cpoly__bs(st.hi, j, cpoly__bg(st.hi, j - 1))
        j -= 1
      }
      cpoly__bs(st.hr, 0, cpoly__fp(0))
      cpoly__bs(st.hi, 0, cpoly__fp(0))
    }
  }
  Nil
}

///|
fn bf__vrshft_sl(l3 : Value) -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let l3 = to_int(l3)
  ist.conv = false
  st.sr = st.zr
  st.si = st.zi
  let mut bool1 = false
  let mut omp : Value = Nil
  let mut relstp : Value = Nil
  for i in 1..=l3 {
    bf__polyev_sl() |> ignore
    let mp = bf__cmod_sl(st.pvr, st.pvi)
    let ms = bf__cmod_sl(st.sr, st.si)
    if cpoly__gtp(fptimes_star(cpoly__fp(20), bf__errev_sl(ms, mp)), mp) {
      ist.conv = true
      st.zr = st.sr
      st.zi = st.si
      return t
    }
    if i == 1 {
      omp = mp
    } else if bool1 ||
      cpoly__gtp(omp, mp) ||
      //(not (< relstp 0.05))
      cpoly__gtp(relstp, cpoly__half()) {
      if cpoly__gtp(fptimes_star(cpoly__fpd(0.1), mp), omp) {
        return t
      } else {
        omp = mp
      }
    } else {
      let mut tp = relstp
      bool1 = true
      if cpoly__gtp(st.are, relstp) {
        tp = st.are
      }
      let r1 = fpsqrt(tp)
      let sr1 = fpdifference(
        fptimes_star(fpplus(fpone(), r1), st.sr),
        fptimes_star(r1, st.si),
      )
      st.si = fpplus(
        fptimes_star(fpplus(fpone(), r1), st.si),
        fptimes_star(r1, st.sr),
      )
      st.sr = sr1
      bf__polyev_sl() |> ignore
      for j in 1..=5 {
        ignore(j)
        bf__calct_sl() |> ignore
        bf__nexth_sl() |> ignore
      }
      omp = st.infin
    }
    bf__calct_sl() |> ignore
    bf__nexth_sl() |> ignore
    bf__calct_sl() |> ignore
    if !ist.bool_ {
      relstp = fpquotient(
        bf__cmod_sl(st.tr, st.ti),
        bf__cmod_sl(st.sr, st.si),
      )
      st.sr = fpplus(st.sr, st.tr)
      st.si = fpplus(st.si, st.ti)
    }
  }
  Nil
}

///|
fn bf__fxshft_sl(l2 : Value) -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let l2 = to_int(l2)
  let mut test_ = true
  let mut pasd = false
  let mut otr = cpoly__fp(0)
  let mut oti = cpoly__fp(0)
  let mut svsr = cpoly__fp(0)
  let mut svsi = cpoly__fp(0)
  ist.bool_ = false
  st.pvr = cpoly__fp(0)
  st.pvi = cpoly__fp(0)
  bf__polyev_sl() |> ignore
  ist.conv = false
  bf__calct_sl() |> ignore
  for j in 1..=l2 {
    otr = st.tr
    oti = st.ti
    bf__nexth_sl() |> ignore
    bf__calct_sl() |> ignore
    st.zr = fpplus(st.sr, st.tr)
    st.zi = fpplus(st.si, st.ti)
    if !ist.bool_ && test_ && j != l2 {
      if cpoly__gtp(
          fptimes_star(cpoly__half(), bf__cmod_sl(st.zr, st.zi)),
          bf__cmod_sl(fpdifference(st.tr, otr), fpdifference(st.ti, oti)),
        ) {
        if pasd {
          for i in 0..=ist.n {
            cpoly__bs(st.shr, i, cpoly__bg(st.hr, i))
            cpoly__bs(st.shi, i, cpoly__bg(st.hi, i))
          }
          svsr = st.sr
          svsi = st.si
          bf__vrshft_sl(Fix(10L)) |> ignore
          if ist.conv {
            break
          }
          test_ = false
          for i in 0..=ist.n {
            cpoly__bs(st.hr, i, cpoly__bg(st.shr, i))
            cpoly__bs(st.hi, i, cpoly__bg(st.shi, i))
          }
          st.sr = svsr
          st.si = svsi
          bf__polyev_sl() |> ignore
          bf__calct_sl() |> ignore
        } else {
          pasd = true
        }
      } else {
        pasd = false
      }
    }
  }
  if !ist.conv {
    bf__vrshft_sl(Fix(10L)) |> ignore
  }
  Nil
}

///|
/// cos(94deg) and sin(94deg), as read by the Lisp reader (doubles).
fn cpoly__bf_rot94() -> (Value, Value) raise {
  (cpoly__fpd(-0.0697564737441253), cpoly__fpd(0.9975640502598242))
}

///|
fn bf__cpoly_sl(degree : Value) -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let mut degree = to_int(degree)
  // Log of our floating point base.  (Do we need this much accuracy?)
  st.logbas = fplog(cpoly__fp(2))
  // "Largest" bfloat.  What should we use?
  st.infin = cpoly__fpd(cpoly__most_positive_flonum)
  // bfloat epsilon.  2^(-fpprec)
  st.are = bf__scale_float(cpoly__fp(2), num_neg(symval(q_fpprec)))
  st.mre = cpoly__fp(0)
  let mut xx = fproot(symval(q_ear_bfhalf), Fix(2L))
  let mut yy = cpoly__fp(0)
  // cos(94deg) and sin(94deg).  Probably don't need full bfloat
  // precision here.
  let (cosr, sinr) = cpoly__bf_rot94()
  st.cr = cpoly__fp(0)
  st.ci = cpoly__fp(0)
  st.sr = cpoly__fp(0)
  st.si = cpoly__fp(0)
  st.tr = cpoly__fp(0)
  st.ti = cpoly__fp(0)
  st.zr = cpoly__fp(0)
  st.zi = cpoly__fp(0)
  let mut bnd = cpoly__fp(0)
  ist.n = 0
  ist.polysc = 0
  ist.polysc1 = 0
  ist.conv = false
  st.mre = fptimes_star(cpoly__fp(2), fptimes_star(fpsqrt(cpoly__fp(2)), st.are))
  yy = fpminus(xx)
  let mut i = degree
  while equal(cpoly__fp(0), cpoly__bg(st.pr, i)) &&
        equal(cpoly__fp(0), cpoly__bg(st.pi, i)) {
    i -= 1
  }
  ist.nn = i
  ist.n = i - 1
  degree = ist.nn
  for i in 0..=ist.nn {
    cpoly__bs(st.shr, i, bf__cmod_sl(cpoly__bg(st.pr, i), cpoly__bg(st.pi, i)))
  }
  if ist.nn > 0 {
    bf__scale_sl() |> ignore
  }
  while true {
    if 2 > ist.nn {
      bf__cdivid_sl(
        fpminus(cpoly__bg(st.pr, 1)),
        fpminus(cpoly__bg(st.pi, 1)),
        cpoly__bg(st.pr, 0),
        cpoly__bg(st.pi, 0),
      )
      |> ignore
      cpoly__bs(st.pr, 1, st.cr)
      cpoly__bs(st.pi, 1, st.ci)
      ist.nn = 0
      break
    }
    for i in 0..=ist.nn {
      cpoly__bs(
        st.shr,
        i,
        bf__cmod_sl(cpoly__bg(st.pr, i), cpoly__bg(st.pi, i)),
      )
    }
    bnd = bf__cauchy_sl()
    // (catch 'newroot ...)
    newroot~: for cnt1 in 1..=2 {
      bf__noshft_sl(Fix(5L)) |> ignore
      for cnt2 in 1..=9 {
        let xx1 = fpdifference(fptimes_star(cosr, xx), fptimes_star(sinr, yy))
        yy = fpplus(fptimes_star(sinr, xx), fptimes_star(cosr, yy))
        xx = xx1
        st.sr = fptimes_star(bnd, xx)
        st.si = fptimes_star(bnd, yy)
        bf__fxshft_sl(int(10 * cnt2)) |> ignore
        if ist.conv {
          cpoly__bs(st.pr, ist.nn, st.zr)
          cpoly__bs(st.pi, ist.nn, st.zi)
          ist.nn = ist.n
          ist.n = ist.n - 1
          for i in 0..=ist.nn {
            cpoly__bs(st.pr, i, cpoly__bg(st.qpr, i))
            cpoly__bs(st.pi, i, cpoly__bg(st.qpi, i))
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
    cpoly__bs(st.pr, i, bf__scale_float(cpoly__bg(st.pr, i), int(ist.polysc1)))
    cpoly__bs(st.pi, i, bf__scale_float(cpoly__bg(st.pi, i), int(ist.polysc1)))
  }
  let mut j = ist.polysc - ist.polysc1 * degree
  for i in 0..=ist.nn {
    cpoly__bs(st.pr, i, bf__scale_float(cpoly__bg(st.pr, i), int(j)))
    cpoly__bs(st.pi, i, bf__scale_float(cpoly__bg(st.pi, i), int(j)))
    j = j + ist.polysc1
  }
  int(ist.nn)
}

///|
fn d_bfallroots(expr : Value) -> Value raise {
  with_specials(
    [
      (q_d_partswitch, Nil),
      (q_d_keepfloat, t),
      (q_d_demoivre, Nil),
      (q_d_listconstvars, t),
      (q_d_algebraic, t),
      (q_d_ratfac, Nil),
    ],
    () => cpoly__bfallroots(expr),
  )
}

///|
/// `(cdr ($bfloat x))`
fn cpoly__bfl(x : Value) -> Value raise {
  cdr(d_bfloat(x))
}

///|
fn cpoly__bfallroots(expr : Value) -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let mut complex = false
  let mut expr = meqhk(expr)
  let expr1 = expr
  let mut var_ = remove(q_d__pcti, cdr(d_listofvars(expr)))
  if !var_.truthy() {
    var_ = list1(gensym())
  }
  if length(var_) != 1 {
    merr(
      "bfallroots: expected a polynomial in one variable; found variables ~M",
      [cons(list1(q_mlist), var_)],
    )
    |> ignore
  }
  var_ = car(var_)
  // It's VERY important to set $bftorat to T so that we preserve
  // the precision of the bfloats when converting them to rationals
  // for $rat.  Might as well turn off printing of the rat messages
  // too.
  let mut res : Value = Nil
  with_specials([(q_d_ratprint, Nil), (q_d_bftorat, t)], () => {
    expr = d_rat(expr, list2(q_d__pcti, var_))
    res = reverse(car(cdddr(car(expr))))
  })
  let mut i = length(res) - length(caddar(expr))
  while i != 0 {
    res = cdr(res)
    i -= 1
  }
  let mut den = cddr(expr)
  expr = cadr(expr)
  // Check denominator is a complex number
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
        bf__cpoly_err(expr1) |> ignore
      }
    } else {
      bf__cpoly_err(expr1) |> ignore
    }
  } else {
    bf__cpoly_err(expr1) |> ignore
  }
  // If the name variable has disappeared, this is caught here
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
        bf__cpoly_err(expr1) |> ignore
      }
    } else {
      bf__cpoly_err(expr1) |> ignore
    }
  } else {
    bf__cpoly_err(expr1) |> ignore
  }
  if ist.nn == 0 {
    if symval(q_d_polyfactor).truthy() {
      st.cr = cpoly__fp(0)
      st.ci = cpoly__fp(0)
      bf__cdivid_sl(
        cpoly__bfl(car(expr)),
        cpoly__bfl(cadr(expr)),
        cpoly__bfl(car(den)),
        cpoly__bfl(cadr(den)),
      )
      |> ignore
      return add2(bcons(st.cr), mul2(q_d__pcti, bcons(st.ci)))
    } else {
      return list1(list2(q_mlist, q_simp))
    }
  }
  let degree = to_int(cadr(expr))
  ist.nn = degree + 1
  st.pr = Array::make(ist.nn, cpoly__fp(0))
  st.pi = Array::make(ist.nn, cpoly__fp(0))
  let ok = catch_tag(q_notpoly, () => cpoly__errset(() => {
    let mut ex = cdr(expr)
    let pct_i = cadr(res)
    while !(ex is Nil) {
      let l = degree - to_int(car(ex))
      let mut r = cadr(ex)
      if numberp(r) {
        cpoly__bs(st.pr, l, cpoly__bfl(r))
      } else {
        if !eq(car(r), pct_i) {
          throw_tag(q_notpoly, Nil) |> ignore
        }
        r = cddr(r)
        cpoly__bs(st.pi, l, cpoly__bfl(car(r)))
        r = caddr(r)
        if r.truthy() {
          cpoly__bs(st.pr, l, cpoly__bfl(r))
        }
        complex = true
      }
      ex = cddr(ex)
    }
    Nil
  }))
  if !ok.truthy() {
    // This should catch expressions like sin(x)-x
    bf__cpoly_err(expr1) |> ignore
  }
  st.shr = Array::make(ist.nn, cpoly__fp(0))
  st.shi = Array::make(ist.nn, cpoly__fp(0))
  st.qpr = Array::make(ist.nn, cpoly__fp(0))
  st.hr = Array::make(degree, cpoly__fp(0))
  st.qhr = Array::make(degree, cpoly__fp(0))
  st.qpi = Array::make(ist.nn, cpoly__fp(0))
  if complex {
    st.hi = Array::make(degree, cpoly__fp(0))
    st.qhi = Array::make(degree, cpoly__fp(0))
  }
  ist.nn = degree
  let res1 = if complex {
    cpoly__errset(() => bf__cpoly_sl(int(degree)))
  } else {
    bf__rpoly_sl(int(degree))
  }
  if !res1.truthy() {
    mtell(
      list1(Str("bfallroots: unexpected error; treat results with caution.~%")),
    )
    |> ignore
  }
  if ist.nn == degree {
    merr("bfallroots: no roots found.", []) |> ignore
  }
  res = Nil
  let polyfactor = symval(q_d_polyfactor).truthy()
  if ist.nn != 0 {
    mtell(
      list([
        Str("bfallroots: only ~S out of ~S roots found.~%"),
        int(degree - ist.nn),
        int(degree),
      ]),
    )
    |> ignore
    expr = bcons(cpoly__fp(0))
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
                    list3(
                      list1(q_mtimes),
                      q_d__pcti,
                      bcons(cpoly__bg(st.pi, i)),
                    ),
                  ),
                  bcons(cpoly__bg(st.pr, i)),
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
    st.cr = cpoly__fp(0)
    st.ci = cpoly__fp(0)
    bf__cdivid_sl(
      cpoly__bg(st.pr, 0),
      cpoly__bg(st.pi, 0),
      cpoly__bfl(car(den)),
      cpoly__bfl(cadr(den)),
    )
    |> ignore
    expr = add2(bcons(st.cr), mul2(q_d__pcti, bcons(st.ci)))
    res = cons(expr, res)
  }
  let mut i = degree
  while i != ist.nn {
    // zr+%i*zi, where zr and zi parts of the root.
    expr = add2(
      bcons(cpoly__bg(st.pr, i)),
      mul2(q_d__pcti, bcons(cpoly__bg(st.pi, i))),
    )
    res = if polyfactor {
      cons(
        if complex || cpoly__zp(cpoly__bg(st.pi, i)) {
          add2(var_, mul2(Fix(-1L), expr))
        } else {
          i = i - 1
          simplify(
            list4(
              list1(q_mplus),
              simplify(list3(list1(q_mexpt), var_, Fix(2L))),
              simplify(list3(list1(q_mtimes), var_, bcons(cpoly__bg(st.pr, i)))),
              bcons(cpoly__bg(st.pr, i + 1)),
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
fn bf__rpoly_sl(degree : Value) -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let mut degree = to_int(degree)
  let polyfactor = () => symval(q_d_polyfactor).truthy()
  st.logbas = fplog(cpoly__fp(2))
  st.infin = cpoly__fpd(cpoly__most_positive_flonum)
  st.are = bf__scale_float(cpoly__fp(2), num_neg(symval(q_fpprec)))
  st.mre = cpoly__fp(0)
  let mut xx = fproot(symval(q_ear_bfhalf), Fix(2L))
  let mut yy = cpoly__fp(0)
  // cos(94deg) and sin(94deg)
  let (cosr, sinr) = cpoly__bf_rot94()
  let mut aa = cpoly__fp(0)
  let mut cc = cpoly__fp(0)
  let mut bb = cpoly__fp(0)
  let mut bnd = cpoly__fp(0)
  st.sr = cpoly__fp(0)
  st.u = cpoly__fp(0)
  st.v = cpoly__fp(0)
  let mut t1 = cpoly__fp(0)
  st.szr = cpoly__fp(0)
  st.szi = cpoly__fp(0)
  st.lzr = cpoly__fp(0)
  st.lzi = cpoly__fp(0)
  ist.nz = 0
  ist.n = 0
  ist.polysc = 0
  ist.polysc1 = 0
  let mut zerok = false
  let mut conv1 = true
  st.mre = st.are
  yy = fpminus(xx)
  let mut i = degree
  while cpoly__zp(cpoly__bg(st.pr, i)) {
    i -= 1
  }
  ist.nn = i
  ist.n = i - 1
  degree = ist.nn
  for i in 0..=ist.nn {
    cpoly__bs(st.shr, i, fpabs(cpoly__bg(st.pr, i)))
  }
  if ist.nn > 0 {
    bf__scale_sl() |> ignore
  }
  while true {
    if ist.nn < 3 {
      if ist.nn == 2 {
        bf__quad_sl(cpoly__bg(st.pr, 0), cpoly__bg(st.pr, 1), cpoly__bg(st.pr, 2))
        |> ignore
        if polyfactor() && !cpoly__zp(st.szi) {
          cpoly__bs(
            st.pr,
            2,
            fpquotient(cpoly__bg(st.pr, 2), cpoly__bg(st.pr, 0)),
          )
          cpoly__bs(
            st.pr,
            1,
            fpquotient(cpoly__bg(st.pr, 1), cpoly__bg(st.pr, 0)),
          )
          cpoly__bs(st.pi, 2, cpoly__fp(1))
        } else {
          cpoly__bs(st.pr, 2, st.szr)
          cpoly__bs(st.pi, 2, st.szi)
          cpoly__bs(st.pr, 1, st.lzr)
          cpoly__bs(st.pi, 1, st.lzi)
        }
      } else {
        cpoly__bs(
          st.pr,
          1,
          fpminus(fpquotient(cpoly__bg(st.pr, 1), cpoly__bg(st.pr, 0))),
        )
      }
      ist.nn = 0
      break
    }
    for i in 0..=ist.nn {
      cpoly__bs(st.shr, i, fpabs(cpoly__bg(st.pr, i)))
    }
    bnd = bf__cauchy_sl()
    for i in 1..=ist.n {
      cpoly__bs(
        st.hr,
        i,
        fpquotient(
          fptimes_star(cpoly__fp(ist.n - i), cpoly__bg(st.pr, i)),
          cpoly__fp(ist.n),
        ),
      )
    }
    cpoly__bs(st.hr, 0, cpoly__bg(st.pr, 0))
    aa = cpoly__bg(st.pr, ist.nn)
    bb = cpoly__bg(st.pr, ist.n)
    zerok = cpoly__zp(cpoly__bg(st.hr, ist.n))
    for jj in 1..=5 {
      ignore(jj)
      cc = cpoly__bg(st.hr, ist.n)
      if zerok {
        let mut j = ist.n
        while !(j < 1) {
          cpoly__bs(st.hr, j, cpoly__bg(st.hr, j - 1))
          j -= 1
        }
        cpoly__bs(st.hr, 0, cpoly__fp(0))
        zerok = cpoly__zp(cpoly__bg(st.hr, ist.n))
      } else {
        t1 = fpminus(fpquotient(aa, cc))
        let mut j = ist.n
        while !(j < 1) {
          cpoly__bs(
            st.hr,
            j,
            fpplus(
              fptimes_star(t1, cpoly__bg(st.hr, j - 1)),
              cpoly__bg(st.pr, j),
            ),
          )
          j -= 1
        }
        cpoly__bs(st.hr, 0, cpoly__bg(st.pr, 0))
        zerok = !cpoly__gtp(
          fpabs(cpoly__bg(st.hr, ist.n)),
          fptimes_star(fpabs(bb), fptimes_star(st.are, cpoly__fp(10))),
        )
      }
    }
    for i in 0..=ist.n {
      cpoly__bs(st.shi, i, cpoly__bg(st.hr, i))
    }
    let mut found = false
    for cnt in 1..=20 {
      let xx1 = fpdifference(fptimes_star(cosr, xx), fptimes_star(sinr, yy))
      yy = fpplus(fptimes_star(sinr, xx), fptimes_star(cosr, yy))
      xx = xx1
      st.sr = fptimes_star(bnd, xx)
      st.u = fptimes_star(cpoly__fp(-2), st.sr)
      st.v = bnd
      bf__fxshfr_sl(int(20 * cnt)) |> ignore
      if ist.nz > 0 {
        cpoly__bs(st.pr, ist.nn, st.szr)
        cpoly__bs(st.pi, ist.nn, st.szi)
        if ist.nz == 2 {
          cpoly__bs(st.pr, ist.n, st.lzr)
          cpoly__bs(st.pi, ist.n, st.lzi)
          if polyfactor() && !cpoly__zp(st.szi) {
            cpoly__bs(st.pr, ist.nn, st.v)
            cpoly__bs(st.pr, ist.n, st.u)
            cpoly__bs(st.pi, ist.nn, cpoly__fp(1))
          }
        }
        ist.nn = ist.nn - ist.nz
        ist.n = ist.nn - 1
        for i in 0..=ist.nn {
          cpoly__bs(st.pr, i, cpoly__bg(st.qpr, i))
        }
        found = true
        break
      }
      for i in 0..=ist.n {
        cpoly__bs(st.hr, i, cpoly__bg(st.shi, i))
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
      if cpoly__zp(cpoly__bg(st.pi, i)) {
        cpoly__bs(
          st.pr,
          i,
          bf__scale_float(cpoly__bg(st.pr, i), int(ist.polysc1)),
        )
      } else {
        cpoly__bs(
          st.pr,
          i,
          bf__scale_float(cpoly__bg(st.pr, i), int(2 * ist.polysc1)),
        )
        i = i - 1
        cpoly__bs(
          st.pr,
          i,
          bf__scale_float(cpoly__bg(st.pr, i), int(ist.polysc1)),
        )
      }
      i -= 1
    }
  } else {
    for i in (ist.nn + 1)..=degree {
      cpoly__bs(
        st.pr,
        i,
        bf__scale_float(cpoly__bg(st.pr, i), int(ist.polysc1)),
      )
      cpoly__bs(
        st.pi,
        i,
        bf__scale_float(cpoly__bg(st.pi, i), int(ist.polysc1)),
      )
    }
  }
  let mut j = ist.polysc - ist.polysc1 * degree
  for i in 0..=ist.nn {
    cpoly__bs(st.pr, i, bf__scale_float(cpoly__bg(st.pr, i), int(j)))
    j = j + ist.polysc1
  }
  t
}

///|
fn bf__fxshfr_sl(l2 : Value) -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  let l2 = to_int(l2)
  ist.my_type = 0
  st.a = cpoly__fp(0)
  st.b = cpoly__fp(0)
  st.c = cpoly__fp(0)
  st.d = cpoly__fp(0)
  st.e = cpoly__fp(0)
  st.f = cpoly__fp(0)
  st.g = cpoly__fp(0)
  st.h = cpoly__fp(0)
  st.a1 = cpoly__fp(0)
  st.a3 = cpoly__fp(0)
  st.a7 = cpoly__fp(0)
  ist.nz = 0
  bf__quadsd_sl() |> ignore
  bf__calcsc_sl() |> ignore
  let mut betav = cpoly__fpd(0.25)
  let mut betas = cpoly__fpd(0.25)
  let mut oss = st.sr
  let mut ovv = st.v
  let mut ots : Value = Nil
  let mut otv : Value = Nil
  st.ui = Nil
  st.vi = Nil
  st.s = Nil
  for j in 1..=l2 {
    bf__nextk_sl() |> ignore
    bf__calcsc_sl() |> ignore
    bf__newest_sl() |> ignore
    let vv = st.vi
    let mut ss = cpoly__fp(0)
    if !cpoly__zp(cpoly__bg(st.hr, ist.n)) {
      ss = fpminus(fpquotient(cpoly__bg(st.pr, ist.nn), cpoly__bg(st.hr, ist.n)))
    }
    let mut tv = cpoly__fp(1)
    let mut ts = cpoly__fp(1)
    if !(j == 1 || ist.my_type == 3) {
      if !cpoly__zp(vv) {
        tv = fpabs(fpquotient(fpdifference(vv, ovv), vv))
      }
      if !cpoly__zp(ss) {
        ts = fpabs(fpquotient(fpdifference(ss, oss), ss))
      }
      let mut tvv = cpoly__fp(1)
      if !cpoly__gtp(tv, otv) {
        tvv = fptimes_star(tv, otv)
      }
      let mut tss = cpoly__fp(1)
      if !cpoly__gtp(ts, ots) {
        tss = fptimes_star(ts, ots)
      }
      let vpass = !cpoly__gtp(tvv, betav)
      let spass = !cpoly__gtp(tss, betas)
      if spass || vpass {
        let svu = st.u
        let svv = st.v
        for i in 0..=ist.n {
          cpoly__bs(st.shr, i, cpoly__bg(st.hr, i))
        }
        st.s = ss
        let mut vtry = false
        let mut stry = false
        let mut bool_ = !(spass && (!vpass || !cpoly__gtp(tss, tvv)))
        // The inner DO returns T when a zero has been found.
        let mut found = false
        while true {
          let mut l50 = false
          if bool_ {
            bf__quadit_sl() |> ignore
            if ist.nz > 0 {
              found = true
              break
            }
            vtry = true
            betav = fptimes_star(cpoly__fpd(0.25), betav)
            if stry || !spass {
              l50 = true
            } else {
              for i in 0..=ist.n {
                cpoly__bs(st.hr, i, cpoly__bg(st.shr, i))
              }
            }
          }
          if !l50 {
            let iflag = bf__realit_sl()
            if ist.nz > 0 {
              found = true
              break
            }
            stry = true
            betas = fptimes_star(cpoly__fpd(0.25), betas)
            if zerop(iflag) {
              l50 = true
            } else {
              st.ui = fpminus(fpplus(st.s, st.s))
              st.vi = fptimes_star(st.s, st.s)
            }
          }
          if l50 {
            st.u = svu
            st.v = svv
            for i in 0..=ist.n {
              cpoly__bs(st.hr, i, cpoly__bg(st.shr, i))
            }
            if !vpass || vtry {
              break
            }
          }
          bool_ = true
        }
        if found {
          return Nil
        }
        bf__quadsd_sl() |> ignore
        bf__calcsc_sl() |> ignore
      }
    }
    ovv = vv
    oss = ss
    otv = tv
    ots = ts
  }
  Nil
}

///|
fn bf__quadit_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  ist.nz = 0
  st.u = st.ui
  st.v = st.vi
  let mut tried = false
  let mut j = 0
  let mut relstp : Value = Nil
  let mut omp : Value = Nil
  while true {
    bf__quad_sl(cpoly__fp(1), st.u, st.v) |> ignore
    if cpoly__gtp(
        fpabs(fpdifference(fpabs(st.szr), fpabs(st.lzr))),
        fptimes_star(cpoly__fpd(1.0e-2), fpabs(st.lzr)),
      ) {
      return Nil
    }
    bf__quadsd_sl() |> ignore
    let mp = fpplus(
      fpabs(fpdifference(st.a, fptimes_star(st.szr, st.b))),
      fpabs(fptimes_star(st.szi, st.b)),
    )
    let ms = bf__cmod_sl(st.szr, st.szi)
    let ee = bf__errev_sl(ms, mp)
    if !cpoly__gtp(mp, fptimes_star(cpoly__fpd(2.0e1), ee)) {
      ist.nz = 2
      return Nil
    }
    j = j + 1
    // At a root of multiplicity m this iteration converges only
    // linearly, so the budget has to grow with the working precision.
    // The factor 20 is a heuristic, measured rather than derived.
    if j > 20 * cpoly__prec_factor() {
      return Nil
    }
    if !(
        j < 2 ||
        cpoly__gtp(relstp, cpoly__fpd(1.0e-2)) ||
        !cpoly__gtp(mp, omp) ||
        tried
      ) {
      if !cpoly__gtp(relstp, st.are) {
        relstp = st.are
      }
      relstp = fpsqrt(relstp)
      st.u = fpdifference(st.u, fptimes_star(st.u, relstp))
      st.v = fpplus(st.v, fptimes_star(st.v, relstp))
      bf__quadsd_sl() |> ignore
      for i in 1..=5 {
        ignore(i)
        bf__calcsc_sl() |> ignore
        bf__nextk_sl() |> ignore
      }
      tried = true
      j = 0
    }
    omp = mp
    bf__calcsc_sl() |> ignore
    bf__nextk_sl() |> ignore
    bf__calcsc_sl() |> ignore
    bf__newest_sl() |> ignore
    if cpoly__zp(st.vi) {
      return Nil
    }
    relstp = fpabs(fpquotient(fpdifference(st.vi, st.v), st.vi))
    st.u = st.ui
    st.v = st.vi
  }
  Nil
}

///|
fn bf__realit_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  ist.nz = 0
  let mut j = 0
  let mut t1 : Value = Nil
  let mut omp : Value = Nil
  while true {
    let mut pv = cpoly__bg(st.pr, 0)
    cpoly__bs(st.qpr, 0, pv)
    for i in 1..=ist.nn {
      pv = fpplus(fptimes_star(pv, st.s), cpoly__bg(st.pr, i))
      cpoly__bs(st.qpr, i, pv)
    }
    let mp = fpabs(pv)
    let ms = fpabs(st.s)
    let mut ee = fptimes_star(
      fpquotient(st.mre, fpplus(st.are, st.mre)),
      fpabs(cpoly__bg(st.qpr, 0)),
    )
    for i in 1..=ist.nn {
      ee = fpplus(fptimes_star(ee, ms), fpabs(cpoly__bg(st.qpr, i)))
    }
    if !cpoly__gtp(
        mp,
        fptimes_star(
          cpoly__fpd(2.0e1),
          fpdifference(
            fptimes_star(fpplus(st.are, st.mre), ee),
            fptimes_star(st.mre, mp),
          ),
        ),
      ) {
      ist.nz = 1
      st.szr = st.s
      st.szi = cpoly__fp(0)
      return Fix(0L)
    }
    j = j + 1
    // See comment in BF-QUADIT-SL.
    if j > 10 * cpoly__prec_factor() {
      return Fix(0L)
    }
    if !(
        j < 2 ||
        cpoly__gtp(
          fpabs(t1),
          fptimes_star(cpoly__fpd(1.0e-3), fpabs(fpdifference(st.s, t1))),
        ) ||
        !cpoly__gtp(mp, omp)
      ) {
      return Fix(1L)
    }
    omp = mp
    let mut kv = cpoly__bg(st.hr, 0)
    cpoly__bs(st.qhr, 0, kv)
    for i in 1..=ist.n {
      kv = fpplus(fptimes_star(kv, st.s), cpoly__bg(st.hr, i))
      cpoly__bs(st.qhr, i, kv)
    }
    if cpoly__gtp(
        fpabs(kv),
        fptimes_star(
          fpabs(cpoly__bg(st.hr, ist.n)),
          fptimes_star(cpoly__fpd(1.0e1), st.are),
        ),
      ) {
      t1 = fpminus(fpquotient(pv, kv))
      cpoly__bs(st.hr, 0, cpoly__bg(st.qpr, 0))
      for i in 1..=ist.n {
        cpoly__bs(
          st.hr,
          i,
          fpplus(
            fptimes_star(t1, cpoly__bg(st.qhr, i - 1)),
            cpoly__bg(st.qpr, i),
          ),
        )
      }
    } else {
      cpoly__bs(st.hr, 0, cpoly__fp(0))
      for i in 1..=ist.n {
        cpoly__bs(st.hr, i, cpoly__bg(st.qhr, i - 1))
      }
    }
    kv = cpoly__bg(st.hr, 0)
    for i in 1..=ist.n {
      kv = fpplus(fptimes_star(kv, st.s), cpoly__bg(st.hr, i))
    }
    t1 = cpoly__fp(0)
    if cpoly__gtp(
        fpabs(kv),
        fptimes_star(
          fpabs(cpoly__bg(st.hr, ist.n)),
          fptimes_star(cpoly__fp(10), st.are),
        ),
      ) {
      t1 = fpminus(fpquotient(pv, kv))
    }
    st.s = fpplus(st.s, t1)
  }
  Nil
}

///|
fn bf__calcsc_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  st.d = cpoly__bg(st.hr, 0)
  cpoly__bs(st.qhr, 0, st.d)
  st.c = fpdifference(cpoly__bg(st.hr, 1), fptimes_star(st.u, st.d))
  cpoly__bs(st.qhr, 1, st.c)
  for i in 2..=ist.n {
    let c0 = fpdifference(
      fpdifference(cpoly__bg(st.hr, i), fptimes_star(st.u, st.c)),
      fptimes_star(st.v, st.d),
    )
    cpoly__bs(st.qhr, i, c0)
    st.d = st.c
    st.c = c0
  }
  if !(
      cpoly__gtp(
        fpabs(st.c),
        fptimes_star(
          fpabs(cpoly__bg(st.hr, ist.n)),
          fptimes_star(cpoly__fp(100), st.are),
        ),
      ) ||
      cpoly__gtp(
        fpabs(st.d),
        fptimes_star(
          fpabs(cpoly__bg(st.hr, ist.n - 1)),
          fptimes_star(cpoly__fp(100), st.are),
        ),
      )
    ) {
    ist.my_type = 3
  } else if cpoly__gtp(fpabs(st.d), fpabs(st.c)) {
    ist.my_type = 2
    st.e = fpquotient(st.a, st.d)
    st.f = fpquotient(st.c, st.d)
    st.g = fptimes_star(st.u, st.b)
    st.h = fptimes_star(st.v, st.b)
    st.a3 = fpplus(
      fptimes_star(fpplus(st.a, st.g), st.e),
      fptimes_star(st.h, fpquotient(st.b, st.d)),
    )
    st.a1 = fpdifference(fptimes_star(st.b, st.f), st.a)
    st.a7 = fpplus(fptimes_star(fpplus(st.f, st.u), st.a), st.h)
  } else {
    ist.my_type = 1
    st.e = fpquotient(st.a, st.c)
    st.f = fpquotient(st.d, st.c)
    st.g = fptimes_star(st.u, st.e)
    st.h = fptimes_star(st.v, st.b)
    st.a3 = fpplus(
      fptimes_star(st.a, st.e),
      fptimes_star(fpplus(fpquotient(st.h, st.c), st.g), st.b),
    )
    st.a1 = fpdifference(st.b, fptimes_star(st.a, fpquotient(st.d, st.c)))
    st.a7 = fpplus(
      st.a,
      fpplus(fptimes_star(st.g, st.d), fptimes_star(st.h, st.f)),
    )
  }
  Nil
}

///|
fn bf__nextk_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  if ist.my_type == 3 {
    cpoly__bs(st.hr, 0, cpoly__fp(0))
    cpoly__bs(st.hr, 1, cpoly__fp(0))
    for i in 2..=ist.n {
      cpoly__bs(st.hr, i, cpoly__bg(st.qhr, i - 2))
    }
  } else if cpoly__gtp(
      fpabs(st.a1),
      fptimes_star(
        fpabs(if ist.my_type == 1 { st.b } else { st.a }),
        fptimes_star(cpoly__fpd(1.0e1), st.are),
      ),
    ) {
    st.a7 = fpquotient(st.a7, st.a1)
    st.a3 = fpquotient(st.a3, st.a1)
    cpoly__bs(st.hr, 0, cpoly__bg(st.qpr, 0))
    cpoly__bs(
      st.hr,
      1,
      fpdifference(
        cpoly__bg(st.qpr, 1),
        fptimes_star(st.a7, cpoly__bg(st.qpr, 0)),
      ),
    )
    for i in 2..=ist.n {
      cpoly__bs(
        st.hr,
        i,
        fpplus(
          fptimes_star(st.a3, cpoly__bg(st.qhr, i - 2)),
          fpplus(
            fpminus(fptimes_star(st.a7, cpoly__bg(st.qpr, i - 1))),
            cpoly__bg(st.qpr, i),
          ),
        ),
      )
    }
  } else {
    cpoly__bs(st.hr, 0, cpoly__fp(0))
    cpoly__bs(st.hr, 1, fpminus(fptimes_star(st.a7, cpoly__bg(st.qpr, 0))))
    for i in 2..=ist.n {
      cpoly__bs(
        st.hr,
        i,
        fpdifference(
          fptimes_star(st.a3, cpoly__bg(st.qhr, i - 2)),
          fptimes_star(st.a7, cpoly__bg(st.qpr, i - 1)),
        ),
      )
    }
  }
  Nil
}

///|
fn bf__newest_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  if ist.my_type == 3 {
    st.ui = cpoly__fp(0)
    st.vi = cpoly__fp(0)
  } else {
    let mut a4 = cpoly__fp(0)
    let mut a5 = cpoly__fp(0)
    if ist.my_type == 2 {
      a4 = fpplus(fptimes_star(fpplus(st.a, st.g), st.f), st.h)
      a5 = fpplus(
        fptimes_star(fpplus(st.f, st.u), st.c),
        fptimes_star(st.v, st.d),
      )
    } else {
      a4 = fpplus(
        st.a,
        fpplus(fptimes_star(st.u, st.b), fptimes_star(st.h, st.f)),
      )
      a5 = fpplus(
        st.c,
        fptimes_star(fpplus(st.u, fptimes_star(st.v, st.f)), st.d),
      )
    }
    let b1 = fpminus(
      fpquotient(cpoly__bg(st.hr, ist.n), cpoly__bg(st.pr, ist.nn)),
    )
    let b2 = fpminus(
      fpquotient(
        fpplus(
          cpoly__bg(st.hr, ist.n - 1),
          fptimes_star(b1, cpoly__bg(st.pr, ist.n)),
        ),
        cpoly__bg(st.pr, ist.nn),
      ),
    )
    let mut c1 = fptimes_star(fptimes_star(st.v, b2), st.a1)
    let c2 = fptimes_star(b1, st.a7)
    let c3 = fptimes_star(fptimes_star(b1, b1), st.a3)
    let c4 = fpdifference(fpdifference(c1, c2), c3)
    c1 = fpplus(fpplus(a5, fptimes_star(b1, a4)), fpminus(c4))
    if cpoly__zp(c1) {
      st.ui = cpoly__fp(0)
      st.vi = cpoly__fp(0)
    } else {
      st.ui = fpdifference(
        st.u,
        fpquotient(
          fpplus(
            fptimes_star(st.u, fpplus(c3, c2)),
            fptimes_star(
              st.v,
              fpplus(fptimes_star(b1, st.a1), fptimes_star(b2, st.a7)),
            ),
          ),
          c1,
        ),
      )
      st.vi = fptimes_star(st.v, fpplus(fpone(), fpquotient(c4, c1)))
    }
  }
  Nil
}

///|
fn bf__quadsd_sl() -> Value raise {
  let st = cpoly__b
  let ist = cpoly__i
  st.b = cpoly__bg(st.pr, 0)
  cpoly__bs(st.qpr, 0, st.b)
  st.a = fpdifference(cpoly__bg(st.pr, 1), fptimes_star(st.u, st.b))
  cpoly__bs(st.qpr, 1, st.a)
  for i in 2..=ist.nn {
    let c0 = fpdifference(
      fpdifference(cpoly__bg(st.pr, i), fptimes_star(st.u, st.a)),
      fptimes_star(st.v, st.b),
    )
    cpoly__bs(st.qpr, i, c0)
    st.b = st.a
    st.a = c0
  }
  Nil
}

///|
fn bf__quad_sl(a0 : Value, b1 : Value, c0 : Value) -> Value raise {
  let st = cpoly__b
  st.szr = cpoly__fp(0)
  st.szi = cpoly__fp(0)
  st.lzr = cpoly__fp(0)
  st.lzi = cpoly__fp(0)
  // *e* is rebound locally here.
  let mut b0 = cpoly__fp(0)
  let mut l0 = cpoly__fp(0)
  let mut e = cpoly__fp(0)
  if cpoly__zp(a0) {
    if !cpoly__zp(b1) {
      st.szr = fpminus(fpquotient(c0, b1))
    }
  } else if cpoly__zp(c0) {
    st.lzr = fpminus(fpquotient(b1, a0))
  } else {
    b0 = fpquotient(b1, cpoly__fp(2))
    if !cpoly__gtp(fpabs(b0), fpabs(c0)) {
      e = a0
      if !cpoly__gtp(c0, cpoly__fp(0)) {
        e = fpminus(a0)
      }
      e = fpdifference(fptimes_star(b0, fpquotient(b0, fpabs(c0))), e)
      l0 = fptimes_star(fpsqrt(fpabs(e)), fpsqrt(fpabs(c0)))
    } else {
      e = fpdifference(
        cpoly__fp(1),
        fptimes_star(fpquotient(a0, b0), fpquotient(c0, b0)),
      )
      l0 = fptimes_star(fpsqrt(fpabs(e)), fpabs(b0))
    }
    if !cpoly__gtp(e, cpoly__fp(0)) {
      st.szr = fpminus(fpquotient(b0, a0))
      st.lzr = st.szr
      st.szi = fpabs(fpquotient(l0, a0))
      st.lzi = fpminus(st.szi)
    } else {
      if cpoly__gtp(b0, cpoly__fp(0)) {
        l0 = fpminus(l0)
      }
      st.lzr = fpquotient(fpdifference(l0, b0), a0)
      if !cpoly__zp(st.lzr) {
        st.szr = fpquotient(fpquotient(c0, st.lzr), a0)
      }
    }
  }
  Nil
}
