// Port of share/fftpack5/fftpack5.lisp: the Lisp-level FFT functions of
// the FFTPACK5 package (RFFT, INVERSE-RFFT, CFFT, INVERSE-CFFT and their
// tests), on top of the f2cl translation of FFTPACK 5.1 (the MoonBit package
// moonbit-community/maxima/fftpack5).
//
// CL arrays specialized to DOUBLE-FLOAT and (COMPLEX DOUBLE-FLOAT) are
// runtime arrays whose element type is "double-float" (elements Flo) and
// "(complex double-float)" (elements Cplx(Flo, Flo)); they are copied to and
// from FixedArray[Double] / FixedArray[Complex] around the Fortran calls,
// which update the Lisp arrays in place.

///|
let fftpack5__elt_d : String = "double-float"

///|
let fftpack5__elt_c : String = "(complex double-float)"

///|
/// `(make-array n :element-type 'double-float)`
fn fftpack5__make_d(n : Value) -> Value raise {
  make_array([to_int(n)], initial=Flo(0.0), elt=fftpack5__elt_d)
}

///|
/// `(make-array n :element-type '(complex double-float))`
fn fftpack5__make_c(n : Value) -> Value raise {
  make_array([to_int(n)], initial=Cplx(Flo(0.0), Flo(0.0)), elt=fftpack5__elt_c)
}

///|
/// The TYPE-ERROR of a declared argument type.
fn fftpack5__type_error(v : Value, typ : String) -> Value raise {
  raise LispError::SimpleError(
    "The value " + prin1_to_string(v) + " is not of type " + typ,
  )
}

///|
/// The elements of a (simple-array double-float (*)).
fn fftpack5__dvec(x : Value) -> FixedArray[Double] raise {
  match x {
    Vec(a) if a.elt == fftpack5__elt_d && a.dims.length() == 1 =>
      FixedArray::makei(a.data.length(), k => match a.data[k] {
        Flo(d) => d
        _ => 0.0
      })
    _ => {
      fftpack5__type_error(x, "(SIMPLE-ARRAY DOUBLE-FLOAT (*))") |> ignore
      []
    }
  }
}

///|
/// The elements of a (simple-array (complex double-float) (*)).
fn fftpack5__cvec(x : Value) -> FixedArray[@f2cl.Complex] raise {
  match x {
    Vec(a) if a.elt == fftpack5__elt_c && a.dims.length() == 1 =>
      FixedArray::makei(a.data.length(), k => match a.data[k] {
        Cplx(Flo(re), Flo(im)) => @f2cl.cplx(re, im)
        _ => @f2cl.c_zero
      })
    _ => {
      fftpack5__type_error(x, "(SIMPLE-ARRAY (COMPLEX DOUBLE-FLOAT) (*))")
      |> ignore
      []
    }
  }
}

///|
/// Store the values the Fortran routine left in `v` back into the Lisp
/// array `x`.
fn fftpack5__store_d(x : Value, v : FixedArray[Double]) -> Unit raise {
  let a = as_array(x)
  for k, d in v {
    a.data[k] = Flo(d)
  }
}

///|
fn fftpack5__store_c(x : Value, v : FixedArray[@f2cl.Complex]) -> Unit raise {
  let a = as_array(x)
  for k, z in v {
    a.data[k] = Cplx(Flo(z.re), Flo(z.im))
  }
}

///|
/// `(setf (aref x k) v)` for a DOUBLE-FLOAT array.
fn fftpack5__set_d(x : Value, k : Int, v : Value) -> Unit raise {
  match v {
    Flo(_) => aset1(x, k, v) |> ignore
    _ => fftpack5__type_error(v, "DOUBLE-FLOAT") |> ignore
  }
}

///|
/// `(setf (aref x k) v)` for a (COMPLEX DOUBLE-FLOAT) array: V is a number
/// made by COMPLEX from two reals (a float, or a rational complex such as
/// #C(0 1), which SBCL stores converted).
fn fftpack5__set_c(x : Value, k : Int, v : Value) -> Unit raise {
  match v {
    Cplx(re, im) => aset1(x, k, Cplx(lfloat(re), lfloat(im))) |> ignore
    Fix(_) | Big(_) | Ratio(_, _) | Flo(_) =>
      aset1(x, k, Cplx(lfloat(v), Flo(0.0))) |> ignore
    _ => fftpack5__type_error(v, "(COMPLEX DOUBLE-FLOAT)") |> ignore
  }
}

///|
/// `(length x)` of a vector.
fn fftpack5__len(x : Value) -> Int raise {
  as_array(x).data.length()
}

///|
/// Get the wsave array and it's length that is needed for computing the
/// (forward and inverse) FFTs.  The value is cached, so if it's the cache,
/// return it.  Otherwise compute a new value and save it in the cache.
fn fftpack5_get_wsave_entry(n : Value) -> Value raise {
  let entry = gethash(n, symval(q_ear_wsave_cache))
  if entry.truthy() {
    return entry
  }
  let lensav = num_add(num_add(n, Fix(4L)), floor1(llog2(n, Fix(2L))))
  let wsave = fftpack5__make_d(lensav)
  let w = fftpack5__dvec(wsave)
  let ier = @fftpack5.rfft1i(to_int(n), w, 0, to_int(lensav), 0)
  fftpack5__store_d(wsave, w)
  if ier != 0 {
    // This shouldn't really ever happen.
    raise LispError::SimpleError("lensav is not big enough")
  }
  sethash(n, symval(q_ear_wsave_cache), wsave) |> ignore
  wsave
}

///|
/// Convert the output of FFTPACK RFFT1F (forward real FFT) into a more
/// user-friendly format with complex values.
fn fftpack5_convert_rfft(x : Value) -> Value raise {
  fftpack5__dvec(x) |> ignore
  let n = fftpack5__len(x)
  let nhalf = n / 2
  let out = fftpack5__make_c(Fix((1 + nhalf).to_int64()))
  // If X is the transformed value, then the output from rfftf is:
  // 0: X(0) / N
  // 1: 2*realpart(X(1))/N
  // 2: 2*imagpart(X(1))/N
  // 3: 2*realpart(X(2))/N
  // 4: 2*realpart(X(2))/N
  // ...
  // N-1: X(N-1)/N
  // The last term exists only if N is even.
  fftpack5__set_c(out, 0, complex(aref1(x, 0), i=Flo(0.0)))
  let last = if n % 2 == 0 { nhalf - 1 } else { nhalf }
  let mut k = 1
  for j in 1..=last {
    // Need to remove the factor of 2 that rfftf added.
    fftpack5__set_c(
      out,
      j,
      complex(
        num_mul(Flo(0.5), aref1(x, k)),
        i=num_mul(Flo(0.5), aref1(x, k + 1)),
      ),
    )
    k = k + 2
  }
  if n % 2 == 0 {
    fftpack5__set_c(out, nhalf, complex(aref1(x, n - 1), i=Flo(0.0)))
  }
  out
}

///|
/// Convert the complex-valued input, X, (that was produced by rfft) into
/// the form needed by rfft1b.  The length of the transform, N, is needed
/// because it cannot be uniquely determined from the length of X.
fn fftpack5_convert_inverse_rfft(x : Value, n : Value) -> Value raise {
  fftpack5__cvec(x) |> ignore
  let res = fftpack5__make_d(n)
  fftpack5__set_d(res, 0, realpart(aref1(x, 0)))
  let lenx = fftpack5__len(x)
  let hi = if evenp(n) { lenx - 1 } else { lenx }
  let mut k = 1
  for j in 1..<hi {
    let z = aref1(x, j)
    // Put back the factor of 2 that we removed in rfft but is needed by
    // rfft1b.
    fftpack5__set_d(res, k, num_mul(Fix(2L), realpart(z)))
    fftpack5__set_d(res, k + 1, num_mul(Fix(2L), imagpart(z)))
    k = k + 2
  }
  if evenp(n) {
    fftpack5__set_d(res, to_int(n) - 1, realpart(aref1(x, lenx - 1)))
  }
  res
}

///|
/// Compute the real FFT of X.
///
/// Let N be the length of X.  The FFT is:
///
///  Y[n] = 1/N*sum(x[k] * exp(2*%i*%pi*k*n/N), k, 0, N-1)
///
/// for n = 0, 1,...,floor(N/2)+1
///
/// WARNING: This definition differs from the formula used for CFFT which
/// uses exp(-2*%pi*%i*k*n/N)!
fn fftpack5_rfft(x : Value) -> Value raise {
  let xv = fftpack5__dvec(x)
  let n = xv.length()
  let work : FixedArray[Double] = FixedArray::make(n, 0.0)
  let wsave = fftpack5_get_wsave_entry(Fix(n.to_int64()))
  let w = fftpack5__dvec(wsave)
  let lensav = w.length()
  let ier = @fftpack5.rfft1f(n, 1, xv, n, w, 0, lensav, work, n, 0)
  fftpack5__store_d(x, xv)
  fftpack5__store_d(wsave, w)
  if ier != 0 {
    // This should never happen because we always allocate enough space for
    // x, wsave, and the work array.
    raise LispError::SimpleError(
      format_to_string("rfft1f failed with code ~A", [Fix(ier.to_int64())]),
    )
  }
  fftpack5_convert_rfft(x)
}

///|
/// Compute the inverse real FFT of X. N is the length of the transform (and
/// not the length of X!).
///
/// See RFFT for the definition of the FFT used in these routines.
fn fftpack5_inverse_rfft(x : Value, n : Value) -> Value raise {
  fftpack5__cvec(x) |> ignore
  // Check to see if N is consistent with the length of X.  However, this
  // isn't foolproof.  For a real FFT of length 5, the FFT array has length
  // 3.  But a real FFT of length 4 also has an array length of 3.
  if !num_eq(Fix(fftpack5__len(x).to_int64()), num_add(Fix(1L), floor1(num_div(n, Fix(2L))))) {
    raise LispError::SimpleError(
      format_to_string("Length of X (~A) is not compatible with N (~D)", [
        Fix(fftpack5__len(x).to_int64()),
        n,
      ]),
    )
  }
  let inv = fftpack5_convert_inverse_rfft(x, n)
  let nn = to_int(n)
  let work : FixedArray[Double] = FixedArray::make(nn, 0.0)
  let wsave = fftpack5_get_wsave_entry(n)
  let w = fftpack5__dvec(wsave)
  let lensav = w.length()
  let iv = fftpack5__dvec(inv)
  let ier = @fftpack5.rfft1b(nn, 1, iv, nn, w, 0, lensav, work, nn, 0)
  fftpack5__store_d(inv, iv)
  fftpack5__store_d(wsave, w)
  if ier != 0 {
    // This should never happen because we should have always allocated the
    // correct size of the arrays.
    raise LispError::SimpleError(
      format_to_string("rfft1b failed with code ~A", [Fix(ier.to_int64())]),
    )
  }
  inv
}

///|
/// The C library's log2 (what SBCL's two-argument LOG uses for doubles).
extern "C" fn fftpack5__c_log2(x : Double) -> Double = "log2"

///|
/// `(flet ((db (s n) ...)))` of the tests: the ratio S/N in decibels.
fn fftpack5__db(s : Value, n : Value) -> Value raise {
  if zerop(n) {
    Flo(1000.0)
  } else {
    // SBCL's (log x 10) for a double x: log2(x)/log2(10)
    let r = to_double(num_div(s, n))
    num_mul(Fix(10L), Flo(fftpack5__c_log2(r) / fftpack5__c_log2(10.0)))
  }
}

///|
/// `(incf acc (expt v 2))`
fn fftpack5__acc_sq(acc : Value, v : Value) -> Value raise {
  num_add(acc, expt(v, Fix(2L)))
}

///|
/// Test the rfft and inverse-rfft routines using a simple ramp of length n.
/// The six values of the Lisp function.
fn fftpack5_test_rfft_mv(
  n : Value,
  verbose : Value,
) -> (Value, Value, Value, Value, Value, Value) raise {
  // For testing, use a simple ramp: 1, 2, 3, ..., N.
  // With some care, we can derive the FFT for this is
  //
  // X[0] = (N + 1) / 2
  // X[n] = -1/2 - cot(%pi*n/N)/2, n = 1, N
  let nn = to_int(n)
  let x = fftpack5__make_d(n)
  for k in 0..<nn {
    aset1(x, k, Flo((k + 1).to_double())) |> ignore
  }
  let xfrm = fftpack5_rfft(x)
  let xfrm_len = fftpack5__len(xfrm)
  let expected = fftpack5__make_c(Fix(xfrm_len.to_int64()))
  let mut noise_pwr : Value = Flo(0.0)
  let mut signal_pwr : Value = Flo(0.0)
  fftpack5__set_c(
    expected,
    0,
    complex(num_mul(Flo(0.5), num_add(n, Fix(1L))), i=Flo(0.0)),
  )
  let omega = lfloat(num_div(Flo(@math.PI), n))
  for k in 1..<xfrm_len {
    fftpack5__set_c(
      expected,
      k,
      complex(
        Flo(-0.5),
        i=num_div(Flo(-0.5), ltan(num_mul(omega, Fix(k.to_int64())))),
      ),
    )
  }
  if verbose.truthy() {
    format(t, "Forward transform; actual vs expected~%", []) |> ignore
    for k in 0..<xfrm_len {
      format(t, "~4d: ~A ~A~%", [
        Fix(k.to_int64()),
        aref1(xfrm, k),
        aref1(expected, k),
      ])
      |> ignore
    }
  }
  noise_pwr = fftpack5__acc_sq(
    noise_pwr,
    num_abs(
      num_sub(aref1(xfrm, 0), num_mul(Flo(0.5), num_add(n, Fix(1L)))),
    ),
  )
  signal_pwr = fftpack5__acc_sq(
    signal_pwr,
    num_mul(Flo(0.5), num_add(n, Fix(1L))),
  )
  for k in 1..<xfrm_len {
    noise_pwr = fftpack5__acc_sq(
      noise_pwr,
      num_abs(num_sub(aref1(xfrm, k), aref1(expected, k))),
    )
    signal_pwr = fftpack5__acc_sq(signal_pwr, num_abs(aref1(expected, k)))
  }
  let inv = fftpack5_inverse_rfft(xfrm, n)
  let mut inv_noise_pwr : Value = Flo(0.0)
  let mut inv_signal_pwr : Value = Flo(0.0)
  if verbose.truthy() {
    format(t, "Inverse transform; actual vs expected~%", []) |> ignore
    for k in 0..<nn {
      format(t, "~4d: ~A ~A~%", [
        Fix(k.to_int64()),
        aref1(inv, k),
        Fix((k + 1).to_int64()),
      ])
      |> ignore
    }
  }
  for k in 0..<nn {
    inv_noise_pwr = fftpack5__acc_sq(
      inv_noise_pwr,
      num_sub(aref1(inv, k), Fix((k + 1).to_int64())),
    )
    inv_signal_pwr = fftpack5__acc_sq(
      inv_signal_pwr,
      Flo((k + 1).to_double()),
    )
  }
  (
    fftpack5__db(signal_pwr, noise_pwr),
    fftpack5__db(inv_signal_pwr, inv_noise_pwr),
    noise_pwr,
    signal_pwr,
    inv_noise_pwr,
    inv_signal_pwr,
  )
}

///|
fn fftpack5_test_rfft(n : Value, verbose? : Value = Nil) -> Value raise {
  fftpack5_test_rfft_mv(n, verbose).0
}

///|
/// Get the wsave array and it's length that is needed for computing the
/// (forward and inverse) FFTs.  The value is cached, so if it's the cache,
/// return it.  Otherwise compute a new value and save it in the cache.
fn fftpack5_get_double_wsave_entry(n : Value) -> Value raise {
  let entry = gethash(n, symval(q_ear_wsave_cache_double))
  if entry.truthy() {
    return entry
  }
  let lensav = num_add(
    num_add(num_mul(Fix(2L), n), Fix(4L)),
    floor1(llog2(n, Fix(2L))),
  )
  let wsave = fftpack5__make_d(lensav)
  let w = fftpack5__dvec(wsave)
  let ier = @fftpack5.cfft1i(to_int(n), w, to_int(lensav), 0)
  fftpack5__store_d(wsave, w)
  if ier != 0 {
    // This shouldn't really ever happen.
    raise LispError::SimpleError("lensav is not big enough")
  }
  sethash(n, symval(q_ear_wsave_cache_double), wsave) |> ignore
  wsave
}

///|
/// Compute the FFT of a complex array X
///
/// Let N be the length of  X.  The FFT is:
///
///   Y[n] = 1/N*sum(x[k] * exp(-2*%pi*%i*n*k/N), k = 0, N-1)
///
/// for n = 0, 1,...,N -1
///
/// WARNING: This definition differs from RFFT which has
/// exp(+2*%pi*%i*n*k/N)
fn fftpack5_cfft(x : Value) -> Value raise {
  let xv = fftpack5__cvec(x)
  let n = xv.length()
  let lenwrk = 2 * n
  let work : FixedArray[Double] = FixedArray::make(lenwrk, 0.0)
  let wsave = fftpack5_get_double_wsave_entry(Fix(n.to_int64()))
  let w = fftpack5__dvec(wsave)
  let lensav = w.length()
  let ier = @fftpack5.cfft1f(n, 1, xv, n, w, lensav, work, lenwrk, 0)
  fftpack5__store_c(x, xv)
  fftpack5__store_d(wsave, w)
  if ier != 0 {
    // This should never happen because we always allocate enough space for
    // x, wsave, and the work array.
    raise LispError::SimpleError(
      format_to_string("rfft1f failed with code ~A", [Fix(ier.to_int64())]),
    )
  }
  x
}

///|
fn fftpack5_inverse_cfft(x : Value) -> Value raise {
  let xv = fftpack5__cvec(x)
  let n = xv.length()
  let lenwrk = 2 * n
  let work : FixedArray[Double] = FixedArray::make(lenwrk, 0.0)
  let wsave = fftpack5_get_double_wsave_entry(Fix(n.to_int64()))
  let w = fftpack5__dvec(wsave)
  let lensav = w.length()
  let ier = @fftpack5.cfft1b(n, 1, xv, n, w, lensav, work, lenwrk, 0)
  fftpack5__store_c(x, xv)
  fftpack5__store_d(wsave, w)
  if ier != 0 {
    // This should never happen because we should have always allocated the
    // correct size of the arrays.
    raise LispError::SimpleError(
      format_to_string("rfft1b failed with code ~A", [Fix(ier.to_int64())]),
    )
  }
  x
}

///|
/// Test the cfft and inverse-cfft routines using a simple ramp; the six
/// values of the Lisp function.
fn fftpack5_test_cfft_mv(
  n : Value,
  verbose : Value,
) -> (Value, Value, Value, Value, Value, Value) raise {
  let nn = to_int(n)
  let x = fftpack5__make_c(n)
  // The test signal is a simple ramp: 1, 2, 3,..., N.
  //
  // The analytical FFT for this is:
  //
  // X[0] = (N+1)/2
  // X[n] = -1/2 + %i*cot(%pi*n/N)/2
  for k in 0..<nn {
    fftpack5__set_c(x, k, complex(Fix((k + 1).to_int64()), i=Flo(0.0)))
  }
  let xfrm = fftpack5_cfft(x)
  let xfrm_len = fftpack5__len(xfrm)
  let expected = fftpack5__make_c(Fix(xfrm_len.to_int64()))
  let mut noise_pwr : Value = Flo(0.0)
  let mut signal_pwr : Value = Flo(0.0)
  fftpack5__set_c(
    expected,
    0,
    complex(num_mul(Flo(0.5), num_add(n, Fix(1L))), i=Flo(0.0)),
  )
  let omega = lfloat(num_div(Flo(@math.PI), n))
  for k in 1..<xfrm_len {
    fftpack5__set_c(
      expected,
      k,
      complex(
        Flo(-0.5),
        i=num_div(Flo(0.5), ltan(num_mul(omega, Fix(k.to_int64())))),
      ),
    )
  }
  if verbose.truthy() {
    format(t, "Forward transform; actual vs expected~%", []) |> ignore
    for k in 0..<xfrm_len {
      format(t, "~4d: ~A ~A~%", [
        Fix(k.to_int64()),
        aref1(xfrm, k),
        aref1(expected, k),
      ])
      |> ignore
    }
  }
  noise_pwr = fftpack5__acc_sq(
    noise_pwr,
    num_abs(
      num_sub(aref1(xfrm, 0), num_mul(Flo(0.5), num_add(n, Fix(1L)))),
    ),
  )
  signal_pwr = fftpack5__acc_sq(
    signal_pwr,
    num_mul(Flo(0.5), num_add(n, Fix(1L))),
  )
  for k in 1..<xfrm_len {
    noise_pwr = fftpack5__acc_sq(
      noise_pwr,
      num_abs(num_sub(aref1(xfrm, k), aref1(expected, k))),
    )
    signal_pwr = fftpack5__acc_sq(signal_pwr, num_abs(aref1(expected, k)))
  }
  let inv = fftpack5_inverse_cfft(xfrm)
  let mut inv_noise_pwr : Value = Flo(0.0)
  let mut inv_signal_pwr : Value = Flo(0.0)
  if verbose.truthy() {
    format(t, "Inverse transform; actual vs expected~%", []) |> ignore
    for k in 0..<nn {
      format(t, "~4d: ~A ~A~%", [
        Fix(k.to_int64()),
        aref1(inv, k),
        Fix((k + 1).to_int64()),
      ])
      |> ignore
    }
  }
  for k in 0..<nn {
    inv_noise_pwr = fftpack5__acc_sq(
      inv_noise_pwr,
      num_abs(num_sub(aref1(inv, k), Fix((k + 1).to_int64()))),
    )
    inv_signal_pwr = fftpack5__acc_sq(
      inv_signal_pwr,
      Flo((k + 1).to_double()),
    )
  }
  (
    fftpack5__db(signal_pwr, noise_pwr),
    fftpack5__db(inv_signal_pwr, inv_noise_pwr),
    noise_pwr,
    signal_pwr,
    inv_noise_pwr,
    inv_signal_pwr,
  )
}

///|
fn fftpack5_test_cfft(n : Value, verbose? : Value = Nil) -> Value raise {
  fftpack5_test_cfft_mv(n, verbose).0
}

///|
fn init_share_fftpack5_fftpack5() -> Unit raise {
  // Caches of the wsave tables for single- and double-precision FFTs (the
  // key is the FFT size).
  if !boundp(q_ear_wsave_cache) {
    set(q_ear_wsave_cache, make_hash_table()) |> ignore
  }
  if !boundp(q_ear_wsave_cache_double) {
    set(q_ear_wsave_cache_double, make_hash_table()) |> ignore
  }
  share_f2cl__install_output()
}

///|
/// share/fftpack5/lisp/fftpack5.lisp is an older single-float version of
/// share/fftpack5/fftpack5.lisp that no loader uses; its functions are the
/// same as those above (the FFTPACK5 package has one set of them).
fn init_share_fftpack5_lisp_fftpack5() -> Unit raise {
  init_share_fftpack5_fftpack5()
}
