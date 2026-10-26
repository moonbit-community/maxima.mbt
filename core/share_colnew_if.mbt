// Port of share/colnew/colnew-if.lisp: the Maxima interface to COLNEW
// (translated by f2cl; the MoonBit translation is the package
// dii/maxima/colnew).

///|
/// convert-to-array of a Maxima list into a double-float array.
fn share_colnew__doubles(mlist : Value) -> FixedArray[Double] raise {
  let l = cdr(mlist)
  let a : FixedArray[Double] = FixedArray::make(length(l), 0.0)
  let mut i = 0
  for x in l.iter() {
    a[i] = share_f2cl__double(x)
    i = i + 1
  }
  a
}

///|
/// convert-to-array of a Maxima list into an integer4 array.
fn share_colnew__ints(mlist : Value) -> FixedArray[Int] raise {
  let l = cdr(mlist)
  let a : FixedArray[Int] = FixedArray::make(length(l), 0)
  let mut i = 0
  for x in l.iter() {
    a[i] = to_int(x)
    i = i + 1
  }
  a
}

///|
fn share_colnew__dlist(v : FixedArray[Double]) -> Value {
  let c = Collector::new()
  for x in v {
    c.add(Flo(x))
  }
  cons(list1(q_mlist), c.result())
}

///|
fn share_colnew__ilist(v : FixedArray[Int]) -> Value {
  let c = Collector::new()
  for x in v {
    c.add(int(x))
  }
  cons(list1(q_mlist), c.result())
}

///|
/// (coerce (subseq z 0 nz) 'list) for the slice of Z at OFF.
fn share_colnew__zlist(z : FixedArray[Double], off : Int, nz : Int) -> Value raise {
  if off + nz > z.length() {
    raise LispError::SimpleError(
      "The bounding indices 0 and " + nz.to_string() +
      " are bad for a sequence of length " +
      (z.length() - off).to_string() + ".",
    )
  }
  let c = Collector::new()
  for i in 0..<nz {
    c.add(Flo(z[off + i]))
  }
  c.result()
}

///|
/// Raw interface to colnew where essentially all of the parameters for
/// colnew are exposed.  The f, df, g, dg, and init-guess parameters must be
/// functions.
fn d_colnew_expert(
  ncomp : Value,
  m : Value,
  aleft : Value,
  aright : Value,
  zeta : Value,
  ipar : Value,
  ltol : Value,
  tol : Value,
  fixpnt : Value,
  ispace : Value,
  fspace : Value,
  iflag : Value,
  f : Value,
  df : Value,
  g : Value,
  dg : Value,
  init_guess : Value,
) -> Value raise {
  // M and F are special variables (bound dynamically, as in the Lisp)
  let bm = bind(q_m, m)
  defer unbind(bm)
  let bf = bind(q_f, f)
  defer unbind(bf)
  // Convert the Maxima lists to arrays
  let a_m = share_colnew__ints(symval(q_m))
  let a_zeta = share_colnew__doubles(zeta)
  let a_ipar = share_colnew__ints(ipar)
  let a_ltol = share_colnew__ints(ltol)
  let a_tol = share_colnew__doubles(tol)
  let a_fixpnt = share_colnew__doubles(fixpnt)
  let a_ispace = share_colnew__ints(ispace)
  let a_fspace = share_colnew__doubles(fspace)
  let cf = intpol__coerce_float_fun(q_d_float, symval(q_f), [])
  let df = intpol__coerce_float_fun(q_d_float, df, [])
  let g = intpol__coerce_float_fun(q_d_float, g, [])
  let dg = intpol__coerce_float_fun(q_d_float, dg, [])
  let nz = to_int(reduce((a, b) => num_add(a, b), cdr(symval(q_m))))
  let bf2 = bind(q_f, cf)
  defer unbind(bf2)
  let fsub = fn(
    x : Double,
    z : FixedArray[Double],
    zo : Int,
    f_array : FixedArray[Double],
    fo : Int,
  ) -> Unit raise {
    let res = apply(symval(q_f), cons(Flo(x), share_colnew__zlist(z, zo, nz)))
    if listp(res) {
      let mut k = 0
      for ff in cdr(res).iter() {
        f_array[fo + k] = share_f2cl__double(d_float(ff))
        k = k + 1
      }
    }
  }
  let dfsub = fn(
    x : Double,
    z : FixedArray[Double],
    zo : Int,
    df_array : FixedArray[Double],
    o : Int,
  ) -> Unit raise {
    let res = apply(df, cons(Flo(x), share_colnew__zlist(z, zo, nz)))
    // res is a Maxima matrix.
    if listp(res) {
      let nc = to_int(ncomp)
      let mut row = 1
      for row_list in cdr(res).iter() {
        let mut col = 1
        for element in cdr(row_list).iter() {
          df_array[o + (row - 1) + nc * (col - 1)] = share_f2cl__double(
            d_float(element),
          )
          col = col + 1
        }
        row = row + 1
      }
    }
  }
  let gsub = fn(i : Int, z : FixedArray[Double], zo : Int, _dummy : Double) -> Double raise {
    let res = apply(g, cons(int(i), share_colnew__zlist(z, zo, nz)))
    // the third value, stored into COLNEW's double-float GVAL unless NIL
    if res is Nil {
      _dummy
    } else {
      share_f2cl__double(res)
    }
  }
  let dgsub = fn(
    i : Int,
    z : FixedArray[Double],
    zo : Int,
    dg_array : FixedArray[Double],
    o : Int,
  ) -> Unit raise {
    let res = apply(dg, cons(int(i), share_colnew__zlist(z, zo, nz)))
    let mut k = 0
    for ff in cdr(res).iter() {
      dg_array[o + k] = share_f2cl__double(d_float(ff))
      k = k + 1
    }
  }
  let guess = fn(
    x : Double,
    z : FixedArray[Double],
    zo : Int,
    dmval : FixedArray[Double],
    o : Int,
  ) -> Unit raise {
    let res = d_float(mcall(init_guess, list1(Flo(x))))
    let new_z = nth(1, res)
    let new_d = nth(2, res)
    let mut k = 0
    for ff in cdr(new_d).iter() {
      dmval[o + k] = share_f2cl__double(d_float(ff))
      k = k + 1
    }
    k = 0
    for ff in cdr(new_z).iter() {
      z[zo + k] = share_f2cl__double(d_float(ff))
      k = k + 1
    }
  }
  share_f2cl__install_output()
  let o_iflag = @colnew.colnew(
    to_int(ncomp),
    a_m,
    share_f2cl__double(d_float(aleft)),
    share_f2cl__double(d_float(aright)),
    a_zeta,
    a_ipar,
    a_ltol,
    a_tol,
    a_fixpnt,
    a_ispace,
    a_fspace,
    to_int(iflag),
    fsub,
    dfsub,
    gsub,
    dgsub,
    guess,
  )
  list([
    list1(q_mlist),
    int(o_iflag),
    share_colnew__dlist(a_fspace),
    share_colnew__ilist(a_ispace),
  ])
}

///|
/// This is a slight extension of the actual APPSLN function.  The X must be
/// a list.  The output is then a list of the z values for each x.  The z
/// values themselves are lists.
fn d_colnew_appsln(x : Value, zlen : Value, fspace : Value, ispace : Value) -> Value raise {
  let a_fspace = share_colnew__doubles(fspace)
  let a_ispace = share_colnew__ints(ispace)
  let z : FixedArray[Double] = FixedArray::make(to_int(zlen), 0.0)
  let result = Collector::new()
  for pnt in cdr(x).iter() {
    @colnew.appsln(share_f2cl__double(d_float(pnt)), z, a_fspace, a_ispace)
    |> ignore
    result.add(share_colnew__dlist(z))
  }
  cons(list1(q_mlist), result.result())
}
