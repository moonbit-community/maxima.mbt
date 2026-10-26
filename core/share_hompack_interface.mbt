// Port of share/hompack/hompack-interface.lisp: the Maxima interface to
// HOMPACK (translated by f2cl; the MoonBit translation is the package
// dii/maxima/hompack).
//
// The coefficient and degree arrays are built as Lisp arrays, as in the Lisp,
// and copied to the FixedArrays HOMPACK works on.  HOMPACK calls the user
// routines F and FJAC by name: their translations forward to closures in
// @hompack.f_hook / @hompack.fjac_hook, which call HOMPACK::F and
// HOMPACK::FJAC below on Lisp arrays.

///|
let share_hompack__q_eqnlist : Value = sym("eqnlist")

///|
let share_hompack__q_varlist : Value = sym("varlist")

// The parameters named VARLIST are special (rat3's VARLIST), so code called
// from here that sets VARLIST changes them: they are bound dynamically and
// read through symval(q_varlist).

///|
/// STRING-EQUAL on string designators.
fn share_hompack__string_equal(a : Value, b : String) -> Bool raise {
  match a {
    Str(s) => string_equal(s, b)
    Sym(_) => string_equal(symbol_name(a), b)
    Char(c) => string_equal(c.to_string(), b)
    _ => false
  }
}

///|
/// (reduce #'max list)
fn share_hompack__max(l : Value) -> Value raise {
  let mut m = car(l)
  for x in cdr(l).iter() {
    m = num_max(m, x)
  }
  m
}

///|
fn share_hompack__to_doubles(v : Value) -> FixedArray[Double] raise {
  let n = length(v)
  let a : FixedArray[Double] = FixedArray::make(n, 0.0)
  for i in 0..<n {
    a[i] = share_f2cl__double(aref1(v, i))
  }
  a
}

///|
fn share_hompack__to_ints(v : Value) -> FixedArray[Int] raise {
  let n = length(v)
  let a : FixedArray[Int] = FixedArray::make(n, 0)
  for i in 0..<n {
    a[i] = to_int(aref1(v, i))
  }
  a
}

///|
/// (make-array n :element-type ... :initial-contents l): the contents must
/// have exactly n elements.
fn share_hompack__check_contents(n : Int, l : Value) -> Unit raise {
  if length(l) != n {
    raise LispError::SimpleError(
      "There are " + length(l).to_string() +
      " elements in the :INITIAL-CONTENTS, but the vector length is " +
      n.to_string() + ".",
    )
  }
}

///|
fn parse_equations(
  eqnlist : Value,
  varlist : Value,
  fname : Value,
) -> (Value, Value, Value, Value) raise {
  let b = bind(q_varlist, varlist)
  defer unbind(b)
  let eqns = cdr(eqnlist)
  let vars = cdr(symval(q_varlist))
  let mut total_deg : Value = Fix(1L)
  let mut numt : Value = Nil
  let mut final_kdeg : Value = Nil
  let mut final_coef : Value = Nil
  // TODO: Check that varlist is a list of symbols.

  // Process each equation
  for eqn in eqns.iter() {
    if symval(q_d_debug_hompack).truthy() {
      displa(eqn) |> ignore
    }
    if !d_polynomialp(eqn, symval(q_varlist)).truthy() {
      merr("~M: Is not a polynomial in ~M: ~M", [fname, symval(q_varlist), eqn])
      |> ignore
    }
    let args = if share_hompack__string_equal(d_op(eqn), "+") {
      cdr(d_args(eqn))
    } else {
      list1(eqn)
    }
    let mut eqn_deg : Value = Nil
    let mut kdeg : Value = Nil
    let mut coef : Value = Nil
    numt = cons(int(length(args)), numt)
    // TODO: Verify that eqn is a sum of terms.

    // Process each term of the equation
    for term in args.iter() {
      if symval(q_d_debug_hompack).truthy() {
        displa(term) |> ignore
      }
      let mut prod : Value = Fix(1L)
      let mut term_deg : Value = Fix(0L)
      // For the term, determine the power of each variable and also create
      // a product of the variable raised to the corresponding power.
      let deg = mapcar(
        v => {
          let p = d_hipow(term, v)
          term_deg = num_add(term_deg, p)
          // TODO: Check that p is non-negative integer
          prod = mul2(prod, power(v, p))
          p
        },
        vars,
      )
      let c = d_float(d_expand(div(term, prod)))
      // Check that c is a real number since it's supposed to be the
      // numerical coefficient of the polynomial term.
      if !floatp(c) {
        merr("~M: coefficient of ~M is not a number: ~M", [fname, term, c])
        |> ignore
      }
      if symval(q_d_debug_hompack).truthy() {
        format(q_t, "deg ~A~%", [deg]) |> ignore
        format(q_t, "c ~A~%", [c]) |> ignore
        format(q_t, "term deg ~A~%", [term_deg]) |> ignore
      }
      eqn_deg = cons(term_deg, eqn_deg)
      // Accumulate these results for each term on a list.
      coef = cons(c, coef)
      kdeg = cons(cons(list1(q_mlist), deg), kdeg)
    }
    total_deg = num_mul(total_deg, share_hompack__max(eqn_deg))
    // Now accumulate the results from each equation on to the final list
    final_kdeg = cons(cons(list1(q_mlist), nreverse(kdeg)), final_kdeg)
    final_coef = cons(cons(list1(q_mlist), nreverse(coef)), final_coef)
  }
  // Finally, return the full list of coefficients and degress for each term
  // of each equation.
  (total_deg, nreverse(final_kdeg), nreverse(final_coef), nreverse(numt))
}

///|
fn convert_coef(coef : Value) -> Value raise {
  let dim_j = length(coef)
  let dim_k = to_int(share_hompack__max(mapcar(c => d_length(c), coef)))
  let array = make_array([dim_j, dim_k], elt="double-float")
  let f2cl_array = make_array([dim_j * dim_k], elt="double-float")
  if symval(q_d_debug_hompack).truthy() {
    format(q_t, "dim ~A ~A~%", [int(dim_j), int(dim_k)]) |> ignore
    format(q_t, "array ~A~%", [array]) |> ignore
  }
  // F2CL maps multi-dimensional arrays into one-dimensional arrays in
  // column-major order.  That is, the order of indices is reversed.
  let mut j = 1
  for eqn in coef.iter() {
    let mut k = 1
    for term in cdr(eqn).iter() {
      if symval(q_d_debug_hompack).truthy() {
        format(q_t, "eqn ~A coef ~A = ~A~%", [int(j), int(k), term]) |> ignore
      }
      aset(array, [j - 1, k - 1], d_float(term)) |> ignore
      aset1(
        f2cl_array,
        j - 1 + dim_j * (k - 1),
        Flo(share_f2cl__double(d_float(term))),
      )
      |> ignore
      k = k + 1
    }
    j = j + 1
  }
  if symval(q_d_debug_hompack).truthy() {
    format(q_t, "coef array ~A~%", [array]) |> ignore
  }
  f2cl_array
}

///|
fn convert_kdeg(kdeg : Value, numt : Value) -> Value raise {
  let dim_j = length(kdeg)
  let dim_l = dim_j + 1
  let dim_k = to_int(share_hompack__max(numt))
  let array = make_array([dim_j, dim_l, dim_k], elt="fixnum")
  let f2cl_array = make_array([dim_j * dim_l * dim_k], elt="fixnum")
  let mut j = 1
  for eqn in kdeg.iter() {
    let mut l = 1
    for term in cdr(eqn).iter() {
      let mut k = 1
      for p in cdr(term).iter() {
        if symval(q_d_debug_hompack).truthy() {
          format(q_t, "set eqn ~A var ~A term ~A = ~A~%", [
            int(j),
            int(k),
            int(l),
            p,
          ])
          |> ignore
        }
        aset(array, [j - 1, k - 1, l - 1], p) |> ignore
        aset1(f2cl_array, j - 1 + dim_j * (k - 1 + dim_l * (l - 1)), p)
        |> ignore
        k = k + 1
      }
      l = l + 1
    }
    j = j + 1
  }
  if symval(q_d_debug_hompack).truthy() {
    format(q_t, "kdeg array ~A~%", [array]) |> ignore
  }
  f2cl_array
}

///|
/// Solve the system of n polynomial equations in n unknowns.
///
/// EQNLIST is the list of polynomial equations (sums of
/// c[k]*x1^p1*x2^p2*...*xn^pn), VARLIST the list of the n variables.  The
/// result is [ifail, roots, iflg2, lambda, arclen, nfe]: ifail is negative
/// for an error of POLSYS, 0 for a normal return (iflg2 only contains 1) and
/// 1 otherwise; roots lists [x1 = r1, ..., xn = rn] for each path; iflg2
/// says how each path terminated; lambda is the final continuation
/// parameter, arclen the arc length and nfe the number of Jacobian
/// evaluations of each path.  Keywords: IFLG1 (0, 1, 10 or 11), EPSBIG,
/// EPSSML, NUMRR, IFLG2 (paths to track, -2 = track), SSPAR (step size
/// parameters, negative for the default).
fn d_hompack_polsys(
  eqnlist : Value,
  varlist : Value,
  iflg1? : Value = Fix(0L),
  epsbig? : Value = Flo(0.0001),
  epssml? : Value = Flo(1.0e-14),
  numrr? : Value = Fix(10L),
  iflg2? : Value = Nil,
  sspar? : Value = Nil,
) -> Value raise {
  let pretty_fname = mk(q_d_hompack_polsys, [
    share_hompack__q_eqnlist,
    share_hompack__q_varlist,
    mk(q_mequal, [q_d_iflg1, Fix(0L)]),
    mk(q_mequal, [q_d_epsbig, Flo(1.0e-4)]),
    mk(q_mequal, [q_d_epssml, Flo(1.0e-14)]),
    mk(q_mequal, [q_d_numrr, Fix(10L)]),
    mk(q_mequal, [q_d_iflg2, Nil]),
    mk(q_mequal, [q_d_sspar, Nil]),
  ])
  let b = bind(q_varlist, varlist)
  defer unbind(b)
  if !num_eq(d_length(eqnlist), d_length(symval(q_varlist))) {
    merr(
      "~M: Number of equations (~M) is not the number of variables (~M)",
      [pretty_fname, int(length(eqnlist)), int(length(symval(q_varlist)))],
    )
    |> ignore
  }
  if !(listp(symval(q_varlist)) && eq(caar(symval(q_varlist)), q_mlist)) {
    merr("~M:  ~M is not a list of variables", [pretty_fname, symval(q_varlist)])
    |> ignore
  }
  if !(eql(iflg1, Fix(0L)) ||
    eql(iflg1, Fix(1L)) ||
    eql(iflg1, Fix(10L)) ||
    eql(iflg1, Fix(11L))) {
    merr("~M: iflg1 must be 0, 1, 10, or 11.  Got ~M", [pretty_fname, iflg1])
    |> ignore
  }
  if sspar.truthy() {
    if !(sspar.truthy() && listp(sspar) && eq(caar(sspar), q_mlist)) {
      merr("~M: sspar must be a list not ~M", [pretty_fname, sspar]) |> ignore
    }
    if !num_eq(d_length(sspar), Fix(8L)) {
      merr("~M: sspar must have length 8 not ~M", [pretty_fname, d_length(sspar)])
      |> ignore
    }
    // (every (lambda (x) (typep ($float x) 'double-float)) (cdr sspar)),
    // whose value is not used
    for x in cdr(sspar).iter() {
      if !floatp(d_float(x)) {
        break
      }
    }
  }
  let (total_deg, kdeg, coef, numt) = parse_equations(
    eqnlist,
    symval(q_varlist),
    pretty_fname,
  )
  if iflg2.truthy() {
    if !num_eq(int(length(iflg2)), total_deg) {
      merr("~M: Length of iflg2 must be ~M not ~M", [
        pretty_fname,
        total_deg,
        int(length(iflg2)),
      ])
      |> ignore
    }
    if !every(x => integerp(x), cdr(iflg2)) {
      merr("~M: iflg2 must be integers: ~M", [pretty_fname, iflg2]) |> ignore
    }
  }
  let n = to_int(d_length(eqnlist))
  let mmaxt = to_int(share_hompack__max(numt))
  let tdeg = to_int(total_deg)
  let lenwk = 21 + 61 * n + 10 * n * n + 7 * n * mmaxt + 4 * n * n * mmaxt
  let wk : FixedArray[Double] = FixedArray::make(lenwk, 0.0)
  let leniwk = 43 + 7 * n + n * (1 + n) * mmaxt
  let iwk : FixedArray[Int] = FixedArray::make(lenwk, 0)
  let lamda : FixedArray[Double] = FixedArray::make(tdeg, 0.0)
  let arclen : FixedArray[Double] = FixedArray::make(tdeg, 0.0)
  let nfe : FixedArray[Int] = FixedArray::make(tdeg, 0)
  let roots : FixedArray[Double] = FixedArray::make(2 * (1 + n) * tdeg, 0.0)
  let iflg2_array : FixedArray[Int] = if iflg2.truthy() {
    share_hompack__check_contents(tdeg, cdr(iflg2))
    let a : FixedArray[Int] = FixedArray::make(tdeg, 0)
    let mut i = 0
    for x in cdr(iflg2).iter() {
      a[i] = to_int(x)
      i = i + 1
    }
    a
  } else {
    FixedArray::make(tdeg, -2)
  }
  let sspar_array : FixedArray[Double] = if sspar.truthy() {
    let l = cdr(d_float(sspar))
    share_hompack__check_contents(8, l)
    let a : FixedArray[Double] = FixedArray::make(8, 0.0)
    let mut i = 0
    for x in l.iter() {
      a[i] = share_f2cl__double(x)
      i = i + 1
    }
    a
  } else {
    FixedArray::make(8, -1.0)
  }
  let coef_array = convert_coef(coef)
  let kdeg_array = convert_kdeg(kdeg, numt)
  let numt_array : FixedArray[Int] = FixedArray::make(length(numt), 0)
  let mut i = 0
  for x in numt.iter() {
    numt_array[i] = to_int(x)
    i = i + 1
  }
  if symval(q_d_debug_hompack).truthy() {
    format(q_t, "coef-array ~A~%", [coef_array]) |> ignore
    format(q_t, "kdeg-array ~A~%", [kdeg_array]) |> ignore
  }
  share_f2cl__install_output()
  let (ret_iflg1, _) = @hompack.polsys(
    n,
    numt_array,
    share_hompack__to_doubles(coef_array),
    share_hompack__to_ints(kdeg_array),
    to_int(iflg1),
    iflg2_array,
    share_f2cl__double(epsbig),
    share_f2cl__double(epssml),
    sspar_array,
    to_int(numrr),
    n,
    mmaxt,
    tdeg,
    lenwk,
    leniwk,
    lamda,
    roots,
    arclen,
    nfe,
    wk,
    iwk,
  )
  // Convert the roots into a list where each element of the list is a list
  // of the form [x1=r1, x2=r2, ..., xn=rn].
  let r = Collector::new()
  for m in 1..=tdeg {
    let eqs = Collector::new()
    let mut vs = cdr(symval(q_varlist))
    for j in 1..=n {
      if !(vs is Cons(_)) {
        break
      }
      let var_ = car(vs)
      vs = cdr(vs)
      let base = 2 * (j - 1 + (n + 1) * (m - 1))
      eqs.add(
        list3(
          list1(q_mequal),
          var_,
          add2(Flo(roots[base]), mul2(q_d__pcti, Flo(roots[base + 1]))),
        ),
      )
    }
    r.add(cons(list1(q_mlist), eqs.result()))
  }
  // Figure out if anything bad happened.  If iflg1 is negative, just use
  // it.  Otherwise, check that iflg2 has a normal return for all values.  If
  // so, return 0.  Otherwise return 1 to indicate that.
  let ret_code = if ret_iflg1 < 0 {
    ret_iflg1
  } else if iflg2_array.iter().all(x => x == 1) {
    0
  } else {
    1
  }
  let ints = (a : FixedArray[Int]) => {
    let c = Collector::new()
    for x in a {
      c.add(int(x))
    }
    cons(list1(q_mlist), c.result())
  }
  let flos = (a : FixedArray[Double]) => {
    let c = Collector::new()
    for x in a {
      c.add(Flo(x))
    }
    cons(list1(q_mlist), c.result())
  }
  list([
    list1(q_mlist),
    int(ret_code),
    cons(list1(q_mlist), r.result()),
    ints(iflg2_array),
    flos(lamda),
    flos(arclen),
    ints(nfe),
  ])
}

///|
/// HOMPACK::F for HOMPACK_FIXPDF: evaluate the function in *F-FUN* at the
/// point X, returning the values in V.
fn hompack_f(x : Value, v : Value) -> (Value, Value) raise {
  funcall(symval(q_ear_f_fun), [x, v]) |> ignore
  (Nil, Nil)
}

///|
/// HOMPACK::FJAC for HOMPACK_FIXPDF: evaluate the k-th column of the Jacobian
/// (the function in *FJAC-FUN*) at the point X, returning the values in V.
fn hompack_fjac(x : Value, v : Value, k : Value) -> (Value, Value, Value) raise {
  funcall(symval(q_ear_fjac_fun), [x, v, k]) |> ignore
  (Nil, Nil, Nil)
}

///|
/// The Lisp array a displaced array slice of A at offset OFF is.
fn share_hompack__slice(a : FixedArray[Double], off : Int) -> Value raise {
  let n = if a.length() > off { a.length() - off } else { 0 }
  let v = make_array([n], elt="double-float")
  for i in 0..<n {
    aset1(v, i, Flo(a[off + i])) |> ignore
  }
  v
}

///|
/// Store the Lisp array V back into the slice of A at OFF.
fn share_hompack__unslice(
  v : Value,
  a : FixedArray[Double],
  off : Int,
) -> Unit raise {
  for i in 0..<length(v) {
    a[off + i] = share_f2cl__double(aref1(v, i))
  }
}

///|
/// HOMPACK's user routines F and FJAC call HOMPACK::F and HOMPACK::FJAC.
fn share_hompack__install_hooks() -> Unit {
  @hompack.f_hook.val = (x, xo, v, vo) => {
    let xa = share_hompack__slice(x, xo)
    let va = share_hompack__slice(v, vo)
    hompack_f(xa, va) |> ignore
    share_hompack__unslice(va, v, vo)
  }
  @hompack.fjac_hook.val = (x, xo, v, vo, k) => {
    let xa = share_hompack__slice(x, xo)
    let va = share_hompack__slice(v, vo)
    hompack_fjac(xa, va, int(k)) |> ignore
    share_hompack__unslice(va, v, vo)
  }
}

///|
/// (map-into v #'identity list): store the elements of LIST into the double
/// array V, as far as both go.
fn share_hompack__map_into(v : Value, l : Value) -> Unit raise {
  let mut p = l
  let mut i = 0
  while i < length(v) && p is Cons(_) {
    aset1(v, i, Flo(share_f2cl__double(car(p)))) |> ignore
    p = cdr(p)
    i = i + 1
  }
}

///|
/// Find a fixed point or zero of the functions FCNS of the variables
/// VARLIST with HOMPACK's FIXPDF.  The result is
/// [iflag, y, arctol, eps, nfe, arclen].
fn d_hompack_fixpdf(
  fcns : Value,
  varlist : Value,
  iflag? : Value = Fix(-1L),
  arctol? : Value = Flo(-1.0),
  eps? : Value = Flo(1.0e-05),
  trace? : Value = Fix(0L),
  inita? : Value = Nil,
) -> Value raise {
  let b = bind(q_varlist, varlist)
  defer unbind(b)
  let n = length(cdr(symval(q_varlist)))
  let y : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
  let ndima = n
  let a : FixedArray[Double] = FixedArray::make(ndima, 0.0)
  let yp : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
  let ypold : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
  let qr : FixedArray[Double] = FixedArray::make(n * (n + 1), 0.0)
  let alpha : FixedArray[Double] = FixedArray::make(n, 0.0)
  let tz : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
  let pivot : FixedArray[Int] = FixedArray::make(n + 1, 0)
  let wt : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
  let phi : FixedArray[Double] = FixedArray::make(16 * (n + 1), 0.0)
  let p : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
  let par : FixedArray[Double] = FixedArray::make(1, 0.0)
  let ipar : FixedArray[Int] = FixedArray::make(1, 0)
  let arclen = 0.0
  let nfe = 0
  let fvs = intpol__coerce_float_fun(q_d_float, fcns, [symval(q_varlist)])
  let fj = {
    let fj = meval(list3(list1(q_d_jacobian), fcns, symval(q_varlist)))
    // The Fortran code wants the k-th column, so transpose the Jacobian
    // here to make the interface between Maxima and Fortran a little
    // simpler.  Then we can just extract the k-th row of the transpose to
    // get what's needed.
    mapcar(
      fjf => intpol__coerce_float_fun(q_d_float, fjf, [symval(q_varlist)]),
      cdr(d_transpose(fj)),
    )
  }
  // Compute the functions at the point X and return the value in V.
  let f_fun = lfunc("f-fun", args => {
    let x = args[0]
    let v = args[1]
    let x_list = vector_to_list(x)
    let v_list = apply(fvs, x_list)
    share_hompack__map_into(v, cdr(v_list))
    v
  })
  // Compute the k'th column of the Jacobian matrix of F(x) evaluated at X
  // and store the result in V.
  let fjac_fun = lfunc("fjac-fun", args => {
    let x = args[0]
    let v = args[1]
    let k = to_int(args[2])
    let x_list = vector_to_list(x)
    let v_list = apply(elt(fj, k - 1), x_list)
    share_hompack__map_into(v, cdr(v_list))
    v
  })
  with_specials([(q_ear_f_fun, f_fun), (q_ear_fjac_fun, fjac_fun)], () => {
    if inita.truthy() {
      let mut k = 0
      for ia in cdr(inita).iter() {
        if k >= a.length() {
          break
        }
        let val = d_float(ia)
        a[k] = share_f2cl__double(val)
        y[k + 1] = share_f2cl__double(val)
        k = k + 1
      }
    }
    share_hompack__install_hooks()
    share_f2cl__install_output()
    let (r_iflag, r_arctol, r_eps, r_nfe, r_arclen) = @hompack.fixpdf(
      n,
      y,
      to_int(iflag),
      share_f2cl__double(arctol),
      share_f2cl__double(eps),
      to_int(trace),
      a,
      ndima,
      nfe,
      arclen,
      yp,
      ypold,
      qr,
      alpha,
      tz,
      pivot,
      wt,
      phi,
      p,
      par,
      ipar,
    )
    let ans_y = Collector::new()
    for i in 1..<y.length() {
      ans_y.add(Flo(y[i]))
    }
    list([
      list1(q_mlist),
      int(r_iflag),
      cons(list1(q_mlist), ans_y.result()),
      Flo(r_arctol),
      Flo(r_eps),
      int(r_nfe),
      Flo(r_arclen),
    ])
  })
}
