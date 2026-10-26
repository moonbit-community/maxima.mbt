// Port of share/fftpack5/fftpack5-interface.lisp: the Maxima functions
// fftpack5_fft, fftpack5_inverse_fft, fftpack5_real_fft and
// fftpack5_inverse_real_fft, and the conversions between Maxima objects and
// the specialized CL vectors of share_fftpack5_fftpack5.mbt.

///|
/// `(complex re im)` stored into a (complex double-float) array.
fn fftpack5__risplit_complex(fl : Value) -> Value raise {
  complex(car(fl), i=cdr(fl))
}

///|
/// Convert Maxima list to a (simple-array (complex double-float) (*)) with
/// the same values.
fn fftpack5_mlist__gtcomplex_cl_vector(object_ : Value) -> Value raise {
  let z = fftpack5__make_c(Fix((length(object_) - 1).to_int64()))
  let mut k = 0
  for x in cdr(object_).iter() {
    if x is Nil {
      break
    }
    let fl = risplit(d_float(x))
    fftpack5__set_c(z, k, fftpack5__risplit_complex(fl))
    k = k + 1
  }
  z
}

///|
/// Convert a CL array of complex values to a Maxima list containing the
/// same values.
fn fftpack5_complex_cl_vector__gtmlist(array : Value) -> Value raise {
  fftpack5__cvec(array) |> ignore
  let c = Collector::new()
  for w in as_array(array).data {
    c.add(add(list([realpart(w), mul(list([imagpart(w), q_d__pcti]))])))
  }
  cons(list([q_mlist, q_simp]), c.result())
}

///|
/// Convert a CL vector of maxima values to a (simple-array (complex
/// double-float) (*)) with the same complex values.
fn fftpack5_array__gtcomplex_cl_vector(array : Value) -> Value raise {
  let n = fftpack5__len(array)
  let z = fftpack5__make_c(Fix(n.to_int64()))
  for k in 0..<n {
    let fl = risplit(d_float(aref1(array, k)))
    fftpack5__set_c(z, k, fftpack5__risplit_complex(fl))
  }
  z
}

///|
/// Convert (simple-array (complex double-float) (*)) to a CL vector of
/// maxima expressions of the same value.
fn fftpack5_complex_cl_vector__gtvector(array : Value) -> Value raise {
  fftpack5__cvec(array) |> ignore
  let n = fftpack5__len(array)
  let z = make_array([n], initial=Fix(0L))
  for k in 0..<n {
    let item = aref1(array, k)
    aset1(z, k, add(list([realpart(item), mul(list([q_d__pcti, imagpart(item)]))])))
    |> ignore
  }
  z
}

///|
/// `(intern (symbol-name (gensym "$G")) ...)`: a fresh user-level name
/// $Gnnn (gNNN to the Maxima user).
fn fftpack5__gensym_name() -> Value raise {
  let g = gensym(prefix="$g")
  Sym(intern(symbol_name(g)))
}

///|
/// `(symbol-array (mget object 'array))` of a declared Maxima array.
fn fftpack5__maxima_array(object_ : Value) -> Value raise {
  symbol_array(mget(object_, q_array))
}

///|
/// Convert a Maxima OBJECT to a specialized CL vector suitable for the
/// complex FFT routines.  Two values are returned: The specialized vector
/// and a function that will convert the result of the FFT routine to a
/// Maxima object of the same type as OBJECT. MAXIMA-FUNCTION-NAME is a
/// string to use for error messages.
fn fftpack5_find_complex_fft_converters(
  object_ : Value,
  maxima_function_name? : Value = Str("fftpack5"),
) -> (Value, Value) raise {
  if d_listp(object_).truthy() {
    (
      fftpack5_mlist__gtcomplex_cl_vector(object_),
      lfunc("complex-cl-vector->mlist", args => fftpack5_complex_cl_vector__gtmlist(
        args[0],
      )),
    )
  } else if arrayp(object_) {
    (
      fftpack5_array__gtcomplex_cl_vector(object_),
      lfunc("complex-cl-vector->vector", args => fftpack5_complex_cl_vector__gtvector(
        args[0],
      )),
    )
  } else if symbolp(object_) && fftpack5__maxima_array(object_).truthy() {
    let sym_array = fftpack5__maxima_array(object_)
    (
      fftpack5_array__gtcomplex_cl_vector(sym_array),
      lfunc("find-complex-fft-converters", args => {
        let array = args[0]
        let ar = fftpack5_complex_cl_vector__gtvector(array)
        let sym_ = meval(
          list([
            list1(q_d_array),
            fftpack5__gensym_name(),
            q_d_float,
            Fix((fftpack5__len(array) - 1).to_int64()),
          ]),
        )
        putprop(mget(sym_, q_array), ar, q_array) |> ignore
        sym_
      }),
    )
  } else {
    (
      merr("~A: input is not a list or an array: ~M.", [
        maxima_function_name, object_,
      ]),
      Nil,
    )
  }
}

///|
/// Convert Maxima list to a (simple-array double-float (*)) with the same
/// values suitable for as the input for the RFFT routine.  The maxima list
/// is assumed to consist only of real values.
fn fftpack5_mlist__gtrfft_vector(object_ : Value) -> Value raise {
  let n = length(cdr(object_))
  let z = fftpack5__make_d(Fix(n.to_int64()))
  let mut k = 0
  for x in cdr(d_float(object_)).iter() {
    fftpack5__set_d(z, k, x)
    k = k + 1
  }
  z
}

///|
/// Convert CL array of real (Maxima) values to a (simple-array double-float
/// (*)) with the same values suitable for as the input for the RFFT
/// routine.  The CL array is assumed to consist only of real values.
fn fftpack5_array__gtrfft_vector(array : Value) -> Value raise {
  let n = fftpack5__len(array)
  let z = fftpack5__make_d(Fix(n.to_int64()))
  for k in 0..<n {
    fftpack5__set_d(z, k, d_float(aref1(array, k)))
  }
  z
}

///|
/// Convert a Maxima OBJECT to a specialized CL vector suitable for the RFFT
/// routines.  Two values are returned: The specialized vector and a
/// function that will convert the result of the RFFT routine to a Maxima
/// object of the same type as OBJECT.
fn fftpack5_find_rfft_converters(object_ : Value) -> (Value, Value) raise {
  if d_listp(object_).truthy() {
    (
      fftpack5_mlist__gtrfft_vector(object_),
      lfunc("complex-cl-vector->mlist", args => fftpack5_complex_cl_vector__gtmlist(
        args[0],
      )),
    )
  } else if arrayp(object_) {
    let n = fftpack5__len(object_)
    let z = fftpack5__make_c(Fix(n.to_int64()))
    for k in 0..<n {
      let fl = risplit(d_float(aref1(object_, k)))
      fftpack5__set_c(z, k, fftpack5__risplit_complex(fl))
    }
    (
      z,
      lfunc("complex-cl-vector->vector", args => fftpack5_complex_cl_vector__gtvector(
        args[0],
      )),
    )
  } else if symbolp(object_) && fftpack5__maxima_array(object_).truthy() {
    let sym_array = fftpack5__maxima_array(object_)
    (
      fftpack5_array__gtrfft_vector(sym_array),
      lfunc("find-rfft-converters", args => {
        let array = args[0]
        let ar = fftpack5_complex_cl_vector__gtvector(array)
        let sym_ = meval(
          list([
            list1(q_d_array),
            fftpack5__gensym_name(),
            q_d_float,
            Fix((fftpack5__len(array) - 1).to_int64()),
          ]),
        )
        // The value of the SETF, i.e. the Lisp array (not SYM).
        putprop(mget(sym_, q_array), ar, q_array)
      }),
    )
  } else {
    (merr("real_fft: input is not a list or an array: ~M.", [object_]), Nil)
  }
}

///|
/// Convert a Maxima OBJECT to a specialized CL vector suitable for the
/// inverse RFFT routines.  Two values are returned: The specialized vector
/// and a function that will convert the result of the inverse RFFT routine
/// to a Maxima object of the same type as OBJECT.
fn fftpack5_find_irfft_converters(object_ : Value) -> (Value, Value) raise {
  if d_listp(object_).truthy() {
    (
      fftpack5_mlist__gtcomplex_cl_vector(object_),
      lfunc("find-irfft-converters", args => {
        let c = Collector::new()
        for z in as_array(args[0]).data {
          c.add(z)
        }
        cons(list([q_mlist, q_simp]), c.result())
      }),
    )
  } else if arrayp(object_) {
    (
      fftpack5_array__gtcomplex_cl_vector(object_),
      lfunc("find-irfft-converters", args => {
        let obj = args[0]
        let result = make_array([fftpack5__len(obj)], initial=Fix(0L))
        let mut k = 0
        for z in as_array(obj).data {
          aset1(result, k, z) |> ignore
          k = k + 2
        }
        result
      }),
    )
  } else {
    (
      merr("inverse_real_fft: input is not a list or an array: ~M.", [
        object_,
      ]),
      Nil,
    )
  }
}

///|
/// fftpack5_fft(z)
///
/// Computes the FFT of the complex-valued vector <input>.  The <input> may
/// have any length, but the FFT is most efficient if the length has the
/// form 2^r*3^s*5^t.
///
/// Let x be the input and y be the transformed value.  Then the FFT is
/// defined by
///
/// y[k] = (1/n) sum(x[j] exp(+2 %i %pi j k / n), j, 0, n - 1)
fn d_fftpack5_fft(input : Value) -> Value raise {
  let (z, from_lisp) = fftpack5_find_complex_fft_converters(input)
  // To match the fft package, we want to do the inverse FFT here and then
  // we need to scale the result by 1/N.
  fftpack5_inverse_cfft(z) |> ignore
  let n = fftpack5__len(z)
  let n_float : Value = Flo(n.to_double())
  for k in 0..<n {
    fftpack5__set_c(z, k, num_div(aref1(z, k), n_float))
  }
  funcall(from_lisp, [z])
}

///|
/// fftpack5_inverse_fft(z)
///
/// Computes the inverse FFT of the complex-valued vector <input>.
///
/// Let y be the input and x be the inverse-transformed value.  Then the
/// inverse FFT is defined by
///
/// x[j] = sum(y[k] exp(-2 %i %pi j k / n), k, 0, n - 1)
fn d_fftpack5_inverse_fft(input : Value) -> Value raise {
  let (z, from_lisp) = fftpack5_find_complex_fft_converters(input)
  // To match the fft package, we want to do the forward FFT here and scale
  // the result by N.
  fftpack5_cfft(z) |> ignore
  let n = fftpack5__len(z)
  let n_float : Value = Flo(n.to_double())
  for k in 0..<n {
    fftpack5__set_c(z, k, num_mul(n_float, aref1(z, k)))
  }
  funcall(from_lisp, [z])
}

///|
/// fftpack5_real_fft(input)
///
/// Computes the FFT of the real-valued vector <input>.
///
/// y[k] = (1/n) sum(x[j] exp(+2 %i %pi j k / n), j, 0, n - 1)
///
/// for k = 0, 1, ... floor(n/2).
fn d_fftpack5_real_fft(input : Value) -> Value raise {
  let (z, from_lisp) = fftpack5_find_rfft_converters(input)
  funcall(from_lisp, [fftpack5_rfft(z)])
}

///|
/// fftpack5_inverse_real_fft(input, len)
///
/// Computes the inverse FFT of <input>, which must be in the form returned
/// by fftpack5_real_fft; <len> is the length of the inverse transform.
fn d_fftpack5_inverse_real_fft(input : Value, len : Value) -> Value raise {
  let (z, from_lisp) = fftpack5_find_irfft_converters(input)
  funcall(from_lisp, [fftpack5_inverse_rfft(z, len)])
}

///|
fn init_share_fftpack5_interface() -> Unit raise {
  share_f2cl__install_output()
}
