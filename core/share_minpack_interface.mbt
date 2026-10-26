// Port of share/minpack/minpack-interface.lisp: minpack_lsquares and
// minpack_solve, on top of the f2cl translation of MINPACK (the MoonBit
// package dii/maxima/minpack).

///|
/// `#.(sqrt double-float-epsilon)`, the default tolerance.
let minpack__default_tolerance : Double = 0x3CA0000000000001L
  .reinterpret_as_double()
  .sqrt()

///|
/// %%PRETTY-FNAME of minpack_lsquares and minpack_solve:
/// `((name) fcns vars init-x ((mequal) $jacobian t) ((mequal) $tolerance
/// <default>))`.
fn minpack__pretty_fname(name : Value) -> Value {
  mk(name, [
    sym("fcns"),
    sym("vars"),
    sym("init-x"),
    mk(q_mequal, [q_d_jacobian, t]),
    mk(q_mequal, [q_d_tolerance, Flo(minpack__default_tolerance)]),
  ])
}

///|
/// `(make-array n :element-type 'double-float :initial-contents l)`
fn minpack__dvec(n : Int, l : Value) -> FixedArray[Double] raise {
  if length(l) != n {
    raise LispError::SimpleError(
      "There are " +
      length(l).to_string() +
      " elements in the :INITIAL-CONTENTS, but the vector length is " +
      n.to_string() +
      ".",
    )
  }
  let x : FixedArray[Double] = FixedArray::make(n, 0.0)
  let mut k = 0
  for v in l.iter() {
    x[k] = share_f2cl__double(v)
    k = k + 1
  }
  x
}

///|
/// `(cl:float z 1d0)`
fn minpack__cl_float(z : Value) -> Double raise {
  if realp(z) {
    to_double(lfloat(z))
  } else {
    raise LispError::SimpleError(
      "The value " + prin1_to_string(z) + " is not of type REAL",
    )
  }
}

///|
/// `(cdr l)` where L must be a list.
fn minpack__cdr(l : Value) -> Value raise {
  if listp(l) {
    cdr(l)
  } else {
    raise LispError::SimpleError(
      "The value " + prin1_to_string(l) + " is not of type LIST",
    )
  }
}

///|
/// `(coerce x 'list)` of an array section (it extends to the end of the
/// array).
fn minpack__section_list(x : FixedArray[Double], xo : Int) -> Value {
  let c = Collector::new()
  for k in xo..<x.length() {
    c.add(Flo(x[k]))
  }
  c.result()
}

///|
/// `(subseq (coerce x 'list) 0 n)`
fn minpack__point(x : FixedArray[Double], xo : Int, n : Int) -> Value {
  let c = Collector::new()
  for k in 0..<n {
    c.add(Flo(x[xo + k]))
  }
  c.result()
}

///|
/// `(replace fvec (mapcar #'(lambda (z) (cl:float z 1d0)) l))`
fn minpack__replace(
  fvec : FixedArray[Double],
  fo : Int,
  l : Value,
) -> Unit raise {
  let vals : Array[Double] = []
  for z in l.iter() {
    vals.push(minpack__cl_float(z))
  }
  let mut k = 0
  while k < vals.length() && fo + k < fvec.length() {
    fvec[fo + k] = vals[k]
    k = k + 1
  }
}

///|
/// Extract out elements of Jacobian J (a Maxima matrix or list of rows) and
/// place into fjac, in column-major order.
fn minpack__store_jacobian(
  j : Value,
  fjac : FixedArray[Double],
  jo : Int,
  ldfjac : Int,
) -> Unit raise {
  let mut row_index = 0
  for row in minpack__cdr(j).iter() {
    let mut col_index = 0
    for col in minpack__cdr(row).iter() {
      fjac[jo + row_index + ldfjac * col_index] = minpack__cl_float(col)
      col_index = col_index + 1
    }
    row_index = row_index + 1
  }
}

///|
/// The $debug_minpack trace of a function value.
fn minpack__debug(x : FixedArray[Double], xo : Int, val : Value) -> Unit raise {
  if symval(q_d_debug_minpack).truthy() {
    // (format t "f(~{~A~^, ~}) =~%[~@<~{~A~^, ~:_~}~:>]~%" ...): the
    // values are printed in a logical block (starting at column 1) with
    // fill-style conditional newlines, as SBCL's pretty printer does with
    // a line length of 80 (a line holds at most 79 characters).
    format(t, "f(~{~A~^, ~}) =~%", [minpack__section_list(x, xo)]) |> ignore
    let sb = StringBuilder::new()
    sb.write_char('[')
    let mut col = 1
    let items = minpack__cdr(val)
    let n = length(items)
    let mut k = 0
    for v in items.iter() {
      let txt = format_to_string("~A", [v]) + (if k + 1 < n { "," } else { "" })
      if k > 0 {
        if col + 1 + txt.length() > 79 {
          sb.write_string("\n ")
          col = 1
        } else {
          sb.write_char(' ')
          col = col + 1
        }
      }
      sb.write_string(txt)
      col = col + txt.length()
      k = k + 1
    }
    sb.write_string("]\n")
    format(t, "~A", [Str(sb.to_string())]) |> ignore
  }
}

///|
/// The ECASE of the FCN routines on IFLAG.
fn minpack__ecase_error(iflag : Int) -> Unit raise {
  raise LispError::SimpleError(
    "The value " +
    iflag.to_string() +
    " fell through ECASE expression. Wanted one of (1 2).",
  )
}

///|
/// The common checks of the arguments.
fn minpack__check_list(
  fmt : String,
  pretty : Value,
  v : Value,
) -> Unit raise {
  if !(listp(v) && eq(caar(v), q_mlist)) {
    merr(fmt, [pretty, v]) |> ignore
  }
}

///|
/// Minimize the sum of the squares of m functions in n unknowns (n <= m)
///
///  VARS    list of the variables
///  INIT-X  initial guess
///  FCNS    list of the m functions
///
///  Optional keyword args (key = val)
///  TOLERANCE  tolerance in solution
///  JACOBIAN   If true, maxima computes the Jacobian directly from FCNS.
///             If false, the Jacobian is internally computed using a
///             forward-difference approximation.
///             Otherwise, it is a function returning the Jacobian
fn d_minpack_lsquares(
  fcns : Value,
  vars : Value,
  init_x : Value,
  jacobian? : Value = t,
  tolerance? : Value,
) -> Value raise {
  let pretty = minpack__pretty_fname(q_d_minpack_lsquares)
  let mut tolerance = match tolerance {
    Some(v) => v
    None => Flo(minpack__default_tolerance)
  }
  minpack__check_list("~M: ~M is not a list of functions", pretty, fcns)
  minpack__check_list("~M: ~M is not a list of variables", pretty, vars)
  minpack__check_list("~M: ~M is not a list of initial values", pretty, init_x)
  tolerance = d_float(tolerance)
  if !(realp(tolerance) && plusp(tolerance)) {
    merr("~M: tolerance must be a non-negative real number, not: ~M", [
      pretty, tolerance,
    ])
    |> ignore
  }
  let n = length(cdr(vars))
  let m = length(cdr(fcns))
  let x = minpack__dvec(n, mapcar(z => d_float(z), cdr(init_x)))
  let fvec : FixedArray[Double] = FixedArray::make(m, 0.0)
  let fjac : FixedArray[Double] = FixedArray::make(m * n, 0.0)
  let ldfjac = m
  let info = 0
  let ipvt : FixedArray[Int] = FixedArray::make(n, 0)
  let fv = share_f2cl__coerce_float_fun(fcns, vars)
  let mut fj = if eq(jacobian, t) {
    // T means compute it ourselves
    meval(list3(list1(q_d_jacobian), fcns, vars))
  } else if jacobian.truthy() {
    // Use the specified Jacobian
    jacobian
  } else {
    // No jacobian at all
    Nil
  }
  // Massage the Jacobian into a function
  if jacobian.truthy() {
    fj = share_f2cl__coerce_float_fun(fj, vars)
  }
  share_f2cl__install_output()
  if jacobian.truthy() {
    // Jacobian given (or computed by maxima), so use lmder1
    let lwa = m + 5 * n
    let wa : FixedArray[Double] = FixedArray::make(lwa, 0.0)
    let fcn_and_jacobian = fn(
      m : Int,
      n : Int,
      x : FixedArray[Double],
      xo : Int,
      fvec : FixedArray[Double],
      fo : Int,
      fjac : FixedArray[Double],
      jo : Int,
      ldfjac : Int,
      iflag : Int,
    ) -> (Int, Int, Int, Int) raise {
      match iflag {
        1 => {
          // Compute function at point x, placing result in fvec (subseq
          // needed because sometimes we're called with vector that is
          // longer than we want.  Perfectly valid Fortran, though.)
          let val = apply(fv, minpack__point(x, xo, n))
          if !(val is Cons(_)) {
            merr("Unable to evaluate function at the point ~M", [
              cons(list1(q_mlist), minpack__point(x, xo, n)),
            ])
            |> ignore
          }
          minpack__debug(x, xo, val)
          minpack__replace(fvec, fo, cdr(val))
        }
        2 => {
          // Compute Jacobian at point x, placing result in fjac
          let j = apply(fj, minpack__point(x, xo, n))
          if !(j is Cons(_)) {
            merr("Unable to evaluate Jacobian at the point ~M", [
              cons(list1(q_mlist), minpack__point(x, xo, n)),
            ])
            |> ignore
          }
          minpack__store_jacobian(j, fjac, jo, ldfjac)
        }
        _ => minpack__ecase_error(iflag)
      }
      (m, n, ldfjac, iflag)
    }
    let (_, _, _, info) = @minpack.lmder1(
      fcn_and_jacobian,
      m,
      n,
      x,
      fvec,
      fjac,
      ldfjac,
      share_f2cl__double(tolerance),
      info,
      ipvt,
      wa,
      lwa,
    )
    // Return a list of the solution and the info flag
    list([
      list1(q_mlist),
      cons(list1(q_mlist), minpack__section_list(x, 0)),
      Flo(@minpack.enorm(m, fvec, 0)),
      Fix(info.to_int64()),
    ])
  } else {
    // No Jacobian given so we need to use differences to compute a
    // numerical Jacobian.  Use lmdif1.
    let lwa = m + 5 * n + m * n
    let wa : FixedArray[Double] = FixedArray::make(lwa, 0.0)
    let fval = fn(
      m : Int,
      n : Int,
      x : FixedArray[Double],
      xo : Int,
      fvec : FixedArray[Double],
      fo : Int,
      iflag : Int,
    ) -> (Int, Int, Int) raise {
      // Compute function at point x, placing result in fvec
      let val = apply(fv, minpack__point(x, xo, n))
      if !(val is Cons(_)) {
        merr("Unable to evaluate function at the point ~M", [
          cons(list1(q_mlist), minpack__point(x, xo, n)),
        ])
        |> ignore
      }
      minpack__debug(x, xo, val)
      minpack__replace(fvec, fo, cdr(val))
      (m, n, iflag)
    }
    let (_, _, info) = @minpack.lmdif1(
      fval,
      m,
      n,
      x,
      fvec,
      share_f2cl__double(tolerance),
      info,
      ipvt,
      wa,
      lwa,
    )
    // Return a list of the solution and the info flag
    list([
      list1(q_mlist),
      cons(list1(q_mlist), minpack__section_list(x, 0)),
      Flo(@minpack.enorm(m, fvec, 0)),
      Fix(info.to_int64()),
    ])
  }
}

///|
/// Solve the system of n equations in n unknowns
///
///  VARS    list of the n variables
///  INIT-X  initial guess
///  FCNS    list of the n functions
///
///  Optional keyword args (key = val)
///  TOLERANCE  tolerance in solution
///  JACOBIAN   If true, maxima computes the Jacobian directly from FCNS.
///             If false, the Jacobian is internally computed using a
///             forward-difference approximation.
///             Otherwise, it is a function returning the Jacobian
fn d_minpack_solve(
  fcns : Value,
  vars : Value,
  init_x : Value,
  jacobian? : Value = t,
  tolerance? : Value,
) -> Value raise {
  let pretty = minpack__pretty_fname(q_d_minpack_solve)
  let tolerance = match tolerance {
    Some(v) => v
    None => Flo(minpack__default_tolerance)
  }
  minpack__check_list("~M: ~M is not a list of functions", pretty, fcns)
  minpack__check_list("~M:~%  ~M is not a list of variables", pretty, vars)
  minpack__check_list("~M:~%  ~M is not a list of initial values", pretty, init_x)
  if !(realp(tolerance) && plusp(tolerance)) {
    merr("~M:~%  tolerance must be a non-negative real number, not: ~M", [
      pretty, tolerance,
    ])
    |> ignore
  }
  if length(cdr(fcns)) != length(cdr(vars)) {
    merr(
      "~M:~%  number of equations (~A) must be the same as the number of variables (~A)~%",
      [
        pretty,
        Fix(length(cdr(fcns)).to_int64()),
        Fix(length(cdr(vars)).to_int64()),
      ],
    )
    |> ignore
  }
  let n = length(cdr(vars))
  let x = minpack__dvec(n, mapcar(z => d_float(z), cdr(init_x)))
  let fvec : FixedArray[Double] = FixedArray::make(n, 0.0)
  let fjac : FixedArray[Double] = FixedArray::make(n * n, 0.0)
  let ldfjac = n
  let info = 0
  let fv = share_f2cl__coerce_float_fun(fcns, vars)
  let mut fj = if eq(jacobian, t) {
    // T means compute it ourselves
    mfuncall(q_d_jacobian, list([fcns, vars]))
  } else if jacobian.truthy() {
    // Use the specified Jacobian
    jacobian
  } else {
    // No jacobian at all
    Nil
  }
  // Massage the Jacobian into a function
  if jacobian.truthy() {
    fj = share_f2cl__coerce_float_fun(fj, vars)
  }
  share_f2cl__install_output()
  if jacobian.truthy() {
    // Jacobian given (or computed by maxima), so use hybrj1
    let lwa = n * (n + 13) / 2
    let wa : FixedArray[Double] = FixedArray::make(lwa, 0.0)
    let fcn_and_jacobian = fn(
      n : Int,
      x : FixedArray[Double],
      xo : Int,
      fvec : FixedArray[Double],
      fo : Int,
      fjac : FixedArray[Double],
      jo : Int,
      ldfjac : Int,
      iflag : Int,
    ) -> (Int, Int, Int) raise {
      match iflag {
        1 => {
          // Compute function at point x, placing result in fvec
          let val = apply(fv, minpack__point(x, xo, n))
          minpack__replace(fvec, fo, minpack__cdr(val))
        }
        2 => {
          // Compute Jacobian at point x, placing result in fjac
          let j = apply(fj, minpack__point(x, xo, n))
          minpack__store_jacobian(j, fjac, jo, ldfjac)
        }
        _ => minpack__ecase_error(iflag)
      }
      (n, ldfjac, iflag)
    }
    let (_, _, info) = @minpack.hybrj1(
      fcn_and_jacobian,
      n,
      x,
      fvec,
      fjac,
      ldfjac,
      share_f2cl__double(tolerance),
      info,
      wa,
      lwa,
    )
    // Return a list of the solution and the info flag
    list([
      list1(q_mlist),
      cons(list1(q_mlist), minpack__section_list(x, 0)),
      Flo(@minpack.enorm(n, fvec, 0)),
      Fix(info.to_int64()),
    ])
  } else {
    // No Jacobian given so we need to use differences to compute a
    // numerical Jacobian.  Use hybrd1.
    let lwa = n * (3 * n + 13) / 2
    let wa : FixedArray[Double] = FixedArray::make(lwa, 0.0)
    let fval = fn(
      n : Int,
      x : FixedArray[Double],
      xo : Int,
      fvec : FixedArray[Double],
      fo : Int,
      iflag : Int,
    ) -> (Int, Int) raise {
      // Compute function at point x, placing result in fvec
      let val = apply(fv, minpack__point(x, xo, n))
      minpack__replace(fvec, fo, minpack__cdr(val))
      (n, iflag)
    }
    let (_, info) = @minpack.hybrd1(
      fval,
      n,
      x,
      fvec,
      share_f2cl__double(tolerance),
      info,
      wa,
      lwa,
    )
    // Return a list of the solution and the info flag
    list([
      list1(q_mlist),
      cons(list1(q_mlist), minpack__section_list(x, 0)),
      Flo(@minpack.enorm(n, fvec, 0)),
      Fix(info.to_int64()),
    ])
  }
}

///|
fn init_share_minpack_interface() -> Unit raise {
  share_f2cl__install_output()
}

///|
/// minpack-package.lisp only defines the MINPACK package.
fn init_share_minpack_package() -> Unit raise {

}
