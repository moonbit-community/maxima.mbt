// Port of share/numeric/fft-interface.lisp: the Maxima interface to the
// FFT routines of fft-core and some related utilities.

///|
/// An array argument is converted in place, but a list is copied into a
/// work array first, so the converted values have to be handed back.
fn fft_converted(ary : Value, fast_ary : Value) -> Value raise {
  if d_listp(ary).truthy() {
    cons(list2(q_mlist, q_simp), vector_to_list(fast_ary))
  } else {
    ary
  }
}

///|
/// These functions perhaps need revision if they are needed at all.
/// Output ignores the type of input.
fn d_recttopolar(rary : Value, iary : Value) -> Value raise {
  let fast_rary = maxima_fft_fft_arg_check(q_d_recttopolar, rary)
  let fast_iary = maxima_fft_fft_arg_check(q_d_recttopolar, iary)
  maxima_fft_complex_to_polar(fast_rary, fast_iary) |> ignore
  list3(
    list2(q_mlist, q_simp),
    fft_converted(rary, fast_rary),
    fft_converted(iary, fast_iary),
  )
}

///|
fn d_polartorect(rary : Value, iary : Value) -> Value raise {
  let fast_rary = maxima_fft_fft_arg_check(q_d_polartorect, rary)
  let fast_iary = maxima_fft_fft_arg_check(q_d_polartorect, iary)
  maxima_fft_polar_to_complex(fast_rary, fast_iary) |> ignore
  list3(
    list2(q_mlist, q_simp),
    fft_converted(rary, fast_rary),
    fft_converted(iary, fast_iary),
  )
}

///|
/// `(= size (ash 1 (log-base2 size)))`
fn share_fft_interface__power_of_2_p(size : Int) -> Bool raise {
  let order = to_int(maxima_fft_log_base2(int(size)))
  num_eq(int(size), ash(Fix(1L), order))
}

///|
/// Maxima's forward FFT routine.
fn d_fft(input : Value) -> Value raise {
  let (z0, from_lisp) = maxima_fft_find_complex_fft_converters(input)
  let mut z = z0
  let size = length(z)
  if !share_fft_interface__power_of_2_p(size) {
    merror(Str("fft: size of input must be a power of 2, not ~M"), list1(int(size)))
    |> ignore
  }
  if length(z) > 1 {
    z = maxima_fft_fft_r2_nn(z)
  }
  funcall(from_lisp, [z])
}

///|
/// Maxima's inverse FFT routine.
fn d_inverse_fft(input : Value) -> Value raise {
  let (z0, from_lisp) = maxima_fft_find_complex_fft_converters(
    input,
    maxima_function_name=Str("inverse_fft"),
  )
  let mut z = z0
  let size = length(z)
  if !share_fft_interface__power_of_2_p(size) {
    merror(
      Str("inverse_fft: size of input must be a power of 2, not ~M"),
      list1(int(size)),
    )
    |> ignore
  }
  if length(z) > 1 {
    z = maxima_fft_fft_r2_nn(z, inverse_fft_p=t)
  }
  funcall(from_lisp, [z])
}

///|
/// Maxima's RFFT function.
///
/// The input is assumed to consist of objects that can be converted to a
/// real-valued float.  If the input has length N, then the output is a
/// complex result of length N/2 + 1 because of the symmetry of the FFT for
/// real inputs.
fn d_real_fft(input : Value) -> Value raise {
  let (z0, from_lisp, input_length) = maxima_fft_find_rfft_converters(input)
  let mut z = z0
  let il = to_int(input_length)
  if !share_fft_interface__power_of_2_p(il) {
    merror(
      Str("real_fft: size of input must be a power of 2, not ~M"),
      list1(input_length),
    )
    |> ignore
  }
  let n = length(z) * 2
  let result = make_array([length(z) + 1], initial=Cplx(Flo(0.0), Flo(0.0)))
  // We don't handle input of length 4 or less.  Use the complex FFT
  // routine to produce the desired (correct) output.
  if n < 3 {
    return d_fft(input)
  }
  // Compute FFT of shorter complex vector.
  z = maxima_fft_fft_r2_nn(z)
  // Reconstruct the FFT of the original from the parts
  let z0 = aref1(z, 0)
  aset1(
    result,
    0,
    complex(num_mul(Flo(0.5), num_add(realpart(z0), imagpart(z0)))),
  )
  |> ignore
  let sincos = maxima_fft_sincos_table(maxima_fft_log_base2(int(n)))
  let n_2 = length(z)
  let minus_i : Value = Cplx(Flo(0.0), Flo(-1.0))
  for k in 1..<length(z) {
    let zk = aref1(z, k)
    let zc = conjugate(aref1(z, n_2 - k))
    aset1(
      result,
      k,
      num_mul(
        Flo(0.25),
        num_add(
          num_add(zk, zc),
          num_mul(num_mul(minus_i, aref1(sincos, k)), num_sub(zk, zc)),
        ),
      ),
    )
    |> ignore
  }
  aset1(
    result,
    length(z),
    complex(num_mul(Flo(0.5), num_sub(realpart(z0), imagpart(z0)))),
  )
  |> ignore
  funcall(from_lisp, [result])
}

///|
/// Maxima's inverse RFFT routine.
///
/// The input is assumed to consist of objects that can be converted to a
/// complex-valued floats.  The input MUST have a length that is one more
/// than a power of two, as is returned by RFFT.
fn d_inverse_real_fft(input : Value) -> Value raise {
  let (ft, from_lisp) = maxima_fft_find_irfft_converters(input)
  let n = length(ft) - 1
  if n < 2 {
    // Just use the regular inverse fft to compute these values because
    // inverse_real_fft below doesn't work for these cases.
    return d_inverse_fft(input)
  }
  let order = to_int(maxima_fft_log_base2(int(n)))
  let sincos = maxima_fft_sincos_table(int(order + 1))
  let mut z = make_array([n], initial=Cplx(Flo(0.0), Flo(0.0)))
  if !num_eq(int(n), ash(Fix(1L), order)) {
    merror(
      Str(
        "inverse_real_fft: input length must be one more than a power of two, not ~M",
      ),
      list1(int(n + 1)),
    )
    |> ignore
  }
  let plus_i : Value = Cplx(Flo(0.0), Flo(1.0))
  for k in 0..<n {
    let fk = aref1(ft, k)
    let fc = conjugate(aref1(ft, n - k))
    let evenpart = num_add(fk, fc)
    let oddpart = num_mul(num_sub(fk, fc), conjugate(aref1(sincos, k)))
    aset1(z, k, num_add(evenpart, num_mul(plus_i, oddpart))) |> ignore
  }
  z = maxima_fft_fft_r2_nn(z, inverse_fft_p=t)
  funcall(from_lisp, [z])
}

///|
/// Bigfloat forward FFT.  Length of the input must be a power of 2.
fn d_bf_fft(input : Value) -> Value raise {
  let (z, from_lisp) = maxima_fft_find_bf_fft_converter(input)
  let n = length(z)
  if !share_fft_interface__power_of_2_p(n) {
    merror(Str("bf_fft: size of input must be a power of 2, not ~M"), list1(int(n)))
    |> ignore
  }
  if n > 1 {
    funcall(from_lisp, [bf_fft_r2_nn(z)])
  } else {
    funcall(from_lisp, [z])
  }
}

///|
/// Bigfloat inverse FFT.  Length of the input must be a power of 2.
fn d_bf_inverse_fft(input : Value) -> Value raise {
  let (x, unconvert) = maxima_fft_find_bf_fft_converter(
    input,
    name=Str("bf_inverse_fft"),
  )
  let n = length(x)
  if !share_fft_interface__power_of_2_p(n) {
    merror(
      Str("bf_inverse_fft: size of input must be a power of 2, not ~M"),
      list1(int(n)),
    )
    |> ignore
  }
  if n > 1 {
    funcall(unconvert, [bf_fft_r2_nn(x, inverse_fft_p=t)])
  } else {
    funcall(unconvert, [x])
  }
}

///|
fn d_bf_real_fft(input : Value) -> Value raise {
  let (z0, from_lisp) = maxima_fft_find_bf_rfft_converters(input)
  let mut z = z0
  let n = length(z) * 2
  let result = make_array([length(z) + 1], initial=Fix(0L))
  if n < 3 {
    return d_bf_fft(input)
  }
  // Compute FFT of shorter complex vector.  NOTE: the result returned by
  // bigfloat:fft has scaled the output by the length of z.  That is,
  // divided by n/2.  For our final result, we want to divide by n, so in
  // the following bits of code, we have an extra factor of 2 to divide by.
  z = bf_fft_r2_nn(z)
  // Reconstruct the FFT of the original from the parts
  let zz = aref1(z, 0)
  aset1(
    result,
    0,
    bf_mul(Flo(0.5), bf_add(bf_realpart(zz), bf_imagpart(zz))),
  )
  |> ignore
  let sincos = bf_sincos_table(maxima_fft_log_base2(int(n)))
  let n_2 = length(z)
  let minus_i : Value = Cplx(Fix(0L), Fix(-1L))
  for k in 1..<length(z) {
    let zk = aref1(z, k)
    let zc = bf_conjugate(aref1(z, n_2 - k))
    aset1(
      result,
      k,
      bf_mul(
        Flo(0.25),
        bf_add(
          bf_add(zk, zc),
          bf_mul(bf_mul(minus_i, aref1(sincos, k)), bf_sub(zk, zc)),
        ),
      ),
    )
    |> ignore
  }
  aset1(
    result,
    length(z),
    bf_mul(Flo(0.5), bf_sub(bf_realpart(zz), bf_imagpart(zz))),
  )
  |> ignore
  funcall(from_lisp, [result])
}

///|
fn d_bf_inverse_real_fft(input : Value) -> Value raise {
  let (ft, from_lisp) = maxima_fft_find_bf_irfft_converters(input)
  let n = length(ft) - 1
  if n < 2 {
    // Just use the regular inverse fft to compute these values because
    // inverse_real_fft below doesn't work for these cases.
    return d_bf_inverse_fft(input)
  }
  let z = make_array([n], initial=Fix(0L))
  let order = to_int(maxima_fft_log_base2(int(n)))
  let sincos = bf_sincos_table(int(order + 1))
  if !num_eq(int(n), ash(Fix(1L), order)) {
    merror(
      Str(
        "bf_inverse_real_fft: input length must be one more than a power of two, not ~M",
      ),
      list1(int(n + 1)),
    )
    |> ignore
  }
  let plus_i : Value = Cplx(Fix(0L), Fix(1L))
  for k in 0..<n {
    let fk = aref1(ft, k)
    let fc = bf_conjugate(aref1(ft, n - k))
    let evenpart = bf_add(fk, fc)
    let oddpart = bf_mul(bf_sub(fk, fc), bf_conjugate(aref1(sincos, k)))
    aset1(z, k, bf_add(evenpart, bf_mul(plus_i, oddpart))) |> ignore
  }
  let inverse = bf_fft_r2_nn(z, inverse_fft_p=t)
  funcall(from_lisp, [inverse])
}

///|
fn init_share_fft_interface() -> Unit raise {

}
