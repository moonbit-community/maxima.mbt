// Port of share/numeric/fft-core.lisp: the internal implementation of
// Maxima's FFT routines (package MAXIMA-FFT; the bigfloat FFT is in package
// BIGFLOAT, hence the bf_ prefix of its two functions).
//
// The "specialized" vectors of (complex double-float) of the Lisp are
// runtime vectors whose elements are CL complex numbers
// (Cplx(Flo, Flo)); CL complex arithmetic is the runtime's num_* functions.

///|
/// A fresh (simple-array (complex double-float) (n)); SBCL fills it with
/// #C(0d0 0d0).
fn share_fft_core__make_cvector(n : Int) -> Value {
  make_array([n], initial=Cplx(Flo(0.0), Flo(0.0)))
}

///|
/// `(intern (symbol-name (gensym "$G")) :maxima)`: the CL name "$G123"
/// is the port symbol "$g123".
fn share_fft_core__gentemp() -> Value raise {
  Sym(intern(invert_case(symbol_name(gensym(prefix="$G")))))
}

///|
/// `(meval `(($array) ,sym $float ,(1- n)))` with a fresh symbol.
fn share_fft_core__make_maxima_array(n : Int) -> Value raise {
  meval(
    list([
      list1(q_d_array),
      share_fft_core__gentemp(),
      q_d_float,
      int(n - 1),
    ]),
  )
}

///|
/// `(setf (symbol-array (mget sym 'array)) ar)`
fn share_fft_core__set_symbol_array(sym_ : Value, ar : Value) -> Value raise {
  setf_get(mget(sym_, q_array), q_array, ar) |> ignore
  ar
}

///|
/// `(map seqtype f seq)` over a list or a vector, collecting a list.
fn share_fft_core__seq_to_list(seq : Value) -> Value raise {
  if listp(seq) {
    seq
  } else {
    vector_to_list(seq)
  }
}

///|
/// Return the lisp array which is somehow attached to MARG.
fn maxima_fft_mgetarray(marg : Value) -> Value raise {
  if symbolp(marg) {
    let a = symbol_array(mget(marg, q_array))
    if a.truthy() {
      return a
    }
  }
  if d_listp(marg).truthy() {
    let a = list_to_vector(rest(marg))
    if a.truthy() {
      return a
    }
  }
  if arrayp(marg) {
    marg
  } else {
    Nil
  }
}

///|
fn maxima_fft_fft_arg_check(user_fcn_name : Value, ary : Value) -> Value raise {
  // The type of the elements is not checked.
  let a = maxima_fft_mgetarray(ary)
  if a.truthy() {
    a
  } else {
    merror(
      Str("~M: argument must a list or array; instead found ~:M"),
      list2(user_fcn_name, ary),
    )
  }
}

///|
fn maxima_fft_make_empty_copy(a : Value) -> Value raise {
  if d_listp(a).truthy() {
    let n = to_int(d_length(a))
    let c = Collector::new()
    for _ in 0..<n {
      c.add(Flo(0.0))
    }
    cons(list1(q_mlist), c.result())
  } else if arrayp(a) {
    make_array([length(a)], initial=Flo(0.0))
  } else if symbolp(a) {
    share_fft_core__make_maxima_array(length(maxima_fft_mgetarray(a)))
  } else {
    Nil
  }
}

///|
fn maxima_fft_complex_to_polar(re : Value, im : Value) -> Value raise {
  let n = if length(re) < length(im) { length(re) } else { length(im) }
  for k in 0..<n {
    let rp = aref1(re, k)
    let ip = aref1(im, k)
    aset1(re, k, num_abs(complex(rp, i=ip))) |> ignore
    aset1(im, k, latan(ip, x=rp)) |> ignore
  }
  Nil
}

///|
fn maxima_fft_polar_to_complex(mag : Value, phase_ : Value) -> Value raise {
  let n = if length(mag) < length(phase_) {
    length(mag)
  } else {
    length(phase_)
  }
  for k in 0..<n {
    let r = aref1(mag, k)
    let p = aref1(phase_, k)
    aset1(mag, k, num_mul(r, lcos(p))) |> ignore
    aset1(phase_, k, num_mul(r, lsin(p))) |> ignore
  }
  Nil
}

///|
/// Return the M such that 2^m <= N.  If N is a power of two, M =
/// log2(N).
fn maxima_fft_log_base2(n : Value) -> Value raise {
  int(integer_length(n) - 1)
}

///|
/// For an FFT order of M, return an array of complex twiddle factors for
/// the FFT. The array contains the values exp(i*pi*k/2^(m-1)).
fn maxima_fft_sincos_table(m : Value) -> Value raise {
  let tables = symval(q_ear_sincos_tables)
  let cached = gethash(m, tables)
  if cached.truthy() {
    return cached
  }
  // Need to create the sincos table.  Only need to have a half period.
  let n = to_int(ash(Fix(1L), to_int(m) - 1))
  let p = num_div(Flo(3.141592653589793), int(n))
  let table = share_fft_core__make_cvector(n)
  for k in 0..<n {
    aset1(table, k, cis(num_mul(int(k), p))) |> ignore
  }
  // Make the half point exactly correct
  if n > 1 {
    aset1(table, n / 2, Cplx(Flo(0.0), Flo(1.0))) |> ignore
  }
  sethash(m, tables, table) |> ignore
  table
}

///|
/// Convert Maxima list to a (simple-array (complex double-float) (*))
/// with the same values.
fn maxima_fft_mlist__gtcomplex_cl_vector(object_ : Value) -> Value raise {
  let z = share_fft_core__make_cvector(length(object_) - 1)
  let mut k = 0
  for x in cdr(object_).iter() {
    if x is Nil {
      break
    }
    let fl = risplit(d_float(x))
    aset1(z, k, complex(car(fl), i=cdr(fl))) |> ignore
    k = k + 1
  }
  z
}

///|
/// Convert a CL array of complex values to a Maxima list containing the
/// same values.
fn maxima_fft_complex_cl_vector__gtmlist(array : Value) -> Value raise {
  let c = Collector::new()
  for i in 0..<length(array) {
    let w = aref1(array, i)
    c.add(add2(realpart(w), mul2(imagpart(w), q_d__pcti)))
  }
  cons(list2(q_mlist, q_simp), c.result())
}

///|
/// Convert a CL vector of maxima values to a (simple-array (complex
/// double-float) (*)) with the same complex values.
fn maxima_fft_array__gtcomplex_cl_vector(array : Value) -> Value raise {
  let n = length(array)
  let z = share_fft_core__make_cvector(n)
  for k in 0..<n {
    let fl = risplit(d_float(aref1(array, k)))
    aset1(z, k, complex(car(fl), i=cdr(fl))) |> ignore
  }
  z
}

///|
/// Convert (simple-array (complex double-float) (*)) to a CL vector of
/// maxima expressions of the same value.
fn maxima_fft_complex_cl_vector__gtvector(array : Value) -> Value raise {
  let n = length(array)
  let z = make_array([n], initial=Fix(0L))
  for k in 0..<n {
    let item = aref1(array, k)
    aset1(z, k, add2(realpart(item), mul2(q_d__pcti, imagpart(item)))) |> ignore
  }
  z
}

///|
/// Convert a Maxima OBJECT to a specialized CL vector suitable for the
/// complex FFT routines.  Two values are returned: The specialized vector
/// and a function that will convert the result of the FFT routine to a
/// Maxima object of the same type as OBJECT. MAXIMA-FUNCTION-NAME is a
/// string to use for error messages.
fn maxima_fft_find_complex_fft_converters(
  object_ : Value,
  maxima_function_name? : Value = Str("fft"),
) -> (Value, Value) raise {
  if d_listp(object_).truthy() {
    (
      maxima_fft_mlist__gtcomplex_cl_vector(object_),
      symbol_function(q_maxima_fft_complex_cl_vector__gtmlist),
    )
  } else if arrayp(object_) {
    (
      maxima_fft_array__gtcomplex_cl_vector(object_),
      symbol_function(q_maxima_fft_complex_cl_vector__gtvector),
    )
  } else if symbolp(object_) && symbol_array(mget(object_, q_array)).truthy() {
    let sym_array = symbol_array(mget(object_, q_array))
    (
      maxima_fft_array__gtcomplex_cl_vector(sym_array),
      lfunc("complex-fft-symbol-array", args => {
        let array = arg(args, 0)
        let ar = maxima_fft_complex_cl_vector__gtvector(array)
        let sym_ = share_fft_core__make_maxima_array(length(array))
        share_fft_core__set_symbol_array(sym_, ar) |> ignore
        sym_
      }),
    )
  } else {
    (
      merror(
        Str("~A: input is not a list or an array: ~M."),
        list2(maxima_function_name, object_),
      ),
      Nil,
    )
  }
}

///|
/// The radix-2 FFT loop shared by the double-float and bigfloat versions:
/// `mul`, `add`, `sub` and `conj` are the arithmetic of the package.
fn share_fft_core__fft_loop(
  x : Value,
  b : Value,
  sincos : Value,
  inverse_fft_p : Bool,
  mul : (Value, Value) -> Value raise,
  add : (Value, Value) -> Value raise,
  sub : (Value, Value) -> Value raise,
  conj : (Value) -> Value raise,
) -> Value raise {
  let n = length(x)
  let half_n = n / 2
  let mut pairs_in_group = n / 2
  let mut number_of_groups = 1
  let mut distance = n / 2
  let mut a = x
  let mut b = b
  while number_of_groups < n {
    let mut index = 0
    for k in 0..<number_of_groups {
      let jfirst = 2 * k * pairs_in_group
      let jlast = jfirst + pairs_in_group - 1
      let jtwiddle = k * pairs_in_group
      let w = {
        let w = aref1(sincos, jtwiddle)
        if inverse_fft_p {
          conj(w)
        } else {
          w
        }
      }
      for j in jfirst..=jlast {
        let temp = mul(w, aref1(a, j + distance))
        aset1(b, index, add(aref1(a, j), temp)) |> ignore
        aset1(b, index + half_n, sub(aref1(a, j), temp)) |> ignore
        index = index + 1
      }
    }
    let tmp = a
    a = b
    b = tmp
    pairs_in_group = pairs_in_group / 2
    number_of_groups = number_of_groups * 2
    distance = distance / 2
  }
  a
}

///|
/// Fast Fourier Transform using a simple radix-2 implementation with
/// inputs and outputs in natural order.  The definition of the forward
/// FFT follows Maxima's definition of the forward FFT.
///
/// Compute the FFT of X which MUST be a specialzed vector of complex
/// double-float's whose length MUST be a power of 2.  If INVERSE-FFT-P is
/// non-NIL, the inverse FFT is computed.  The scaling by 1/N is included
/// in the inverse FFT.  The contents of the input X may be destroyed.
fn maxima_fft_fft_r2_nn(x : Value, inverse_fft_p? : Value = Nil) -> Value raise {
  let n = length(x)
  let sincos = maxima_fft_sincos_table(maxima_fft_log_base2(int(n)))
  let a = share_fft_core__fft_loop(
    x,
    share_fft_core__make_cvector(n),
    sincos,
    inverse_fft_p.truthy(),
    (p, q) => num_mul(p, q),
    (p, q) => num_add(p, q),
    (p, q) => num_sub(p, q),
    p => conjugate(p),
  )
  if inverse_fft_p.truthy() {
    a
  } else {
    for k in 0..<n {
      let w = aref1(a, k)
      aset1(a, k, num_div(w, int(n))) |> ignore
    }
    a
  }
}

// RFFT
//
// The FFT of a real signal of length N can be computed using complex FFT
// of length N/2.  For large values of N, this can represent significant
// savings in computation.

///|
/// Convert Maxima list to a (simple-array (complex double-float) (*))
/// with the same values suitable for as the input for the RFFT routine.
/// The maxima list is assumed to consist only of real values.
fn maxima_fft_mlist__gtrfft_vector(object_ : Value) -> Value raise {
  let n = length(cdr(object_))
  let z = share_fft_core__make_cvector(n / 2)
  let mut k = 0
  let mut l = cdr(object_)
  while consp(l) {
    let re = car(l)
    let im = cadr(l)
    if im is Nil {
      break
    }
    aset1(z, k, complex(d_float(re), i=d_float(im))) |> ignore
    k = k + 1
    l = cddr(l)
  }
  z
}

///|
/// Convert CL array of real (Maxima) values to a (simple-array (complex
/// double-float) (*)) with the same values suitable for as the input for
/// the RFFT routine.
fn maxima_fft_array__gtrfft_vector(array : Value) -> Value raise {
  let n = length(array)
  let z = share_fft_core__make_cvector(n / 2)
  let mut k = 0
  let mut m = 0
  while k < n {
    aset1(
      z,
      m,
      complex(d_float(aref1(array, k)), i=d_float(aref1(array, k + 1))),
    )
    |> ignore
    k = k + 2
    m = m + 1
  }
  z
}

///|
/// Convert a Maxima OBJECT to a specialized CL vector suitable for the
/// RFFT routines.  Three values are returned: The specialized vector, a
/// function that will convert the result of the RFFT routine to a Maxima
/// object of the same type as OBJECT, and the length of the input.
fn maxima_fft_find_rfft_converters(
  object_ : Value,
) -> (Value, Value, Value) raise {
  if d_listp(object_).truthy() {
    (
      maxima_fft_mlist__gtrfft_vector(object_),
      symbol_function(q_maxima_fft_complex_cl_vector__gtmlist),
      int(length(object_) - 1),
    )
  } else if arrayp(object_) {
    let z = share_fft_core__make_cvector(length(object_))
    for k in 0..<length(object_) {
      let fl = risplit(d_float(aref1(object_, k)))
      aset1(z, k, complex(car(fl), i=cdr(fl))) |> ignore
    }
    (
      z,
      symbol_function(q_maxima_fft_complex_cl_vector__gtvector),
      int(length(object_)),
    )
  } else if symbolp(object_) && symbol_array(mget(object_, q_array)).truthy() {
    let sym_array = symbol_array(mget(object_, q_array))
    (
      maxima_fft_array__gtrfft_vector(sym_array),
      lfunc("rfft-symbol-array", args => {
        let array = arg(args, 0)
        let ar = maxima_fft_complex_cl_vector__gtvector(array)
        let sym_ = share_fft_core__make_maxima_array(length(array))
        share_fft_core__set_symbol_array(sym_, ar)
      }),
      int(length(sym_array)),
    )
  } else {
    (
      merror(Str("real_fft: input is not a list or an array: ~M."), list1(object_)),
      Nil,
      Nil,
    )
  }
}

///|
/// Convert a Maxima OBJECT to a specialized CL vector suitable for the
/// inverse RFFT routines.  Two values are returned: The specialized vector
/// and a function that will convert the result of the inverse RFFT
/// routine to a Maxima object of the same type as OBJECT.
fn maxima_fft_find_irfft_converters(object_ : Value) -> (Value, Value) raise {
  if d_listp(object_).truthy() {
    (
      maxima_fft_mlist__gtcomplex_cl_vector(object_),
      lfunc("irfft-mlist", args => {
        let obj = arg(args, 0)
        let c = Collector::new()
        for i in 0..<length(obj) {
          let z = aref1(obj, i)
          c.add(realpart(z))
          c.add(imagpart(z))
        }
        cons(list2(q_mlist, q_simp), c.result())
      }),
    )
  } else if arrayp(object_) {
    (
      maxima_fft_array__gtcomplex_cl_vector(object_),
      lfunc("irfft-array", args => {
        let obj = arg(args, 0)
        let result = make_array([2 * length(obj)], initial=Fix(0L))
        for i in 0..<length(obj) {
          let z = aref1(obj, i)
          aset1(result, 2 * i, realpart(z)) |> ignore
          aset1(result, 2 * i + 1, imagpart(z)) |> ignore
        }
        result
      }),
    )
  } else {
    (
      merror(
        Str("inverse_real_fft: input is not a list or an array: ~M."),
        list1(object_),
      ),
      Nil,
    )
  }
}

// Bigfloat FFT
//
// The same set of FFT routines as for floats, but modified to return a
// bigfloat result.

///|
/// Convert a sequence to an array of complex bigfloat numbers.
fn maxima_fft_seq__gtbfft_vector(seq : Value) -> Value raise {
  let items = share_fft_core__seq_to_list(seq)
  let out : Array[Value] = []
  for z in items.iter() {
    let ri = risplit(d_bfloat(z))
    out.push(bf_bigfloat(car(ri), im=cdr(ri)))
  }
  vector(out)
}

///|
fn maxima_fft_mlist__gtbfft_vector(mlist : Value) -> Value raise {
  maxima_fft_seq__gtbfft_vector(cdr(mlist))
}

///|
fn maxima_fft_lisp_array__gtbfft_vector(arr : Value) -> Value raise {
  maxima_fft_seq__gtbfft_vector(arr)
}

///|
fn maxima_fft_bfft_vector__gtseq(arr : Value, seqtype : Value) -> Value raise {
  let c = Collector::new()
  for i in 0..<length(arr) {
    c.add(maxima_to(aref1(arr, i)))
  }
  if eq(seqtype, q_list) {
    c.result()
  } else {
    list_to_vector(c.result())
  }
}

///|
fn maxima_fft_bfft_vector__gtmlist(arr : Value) -> Value raise {
  cons(list2(q_mlist, q_simp), maxima_fft_bfft_vector__gtseq(arr, q_list))
}

///|
fn maxima_fft_bfft_vector__gtlisp_array(arr : Value) -> Value raise {
  maxima_fft_bfft_vector__gtseq(arr, q_vector)
}

///|
/// Outputs a Maxima array as does Maxima's 'array()' function.
fn maxima_fft_bfft_vector__gtmaxima_symbol_array(arr : Value) -> Value raise {
  let lisp_array = maxima_fft_bfft_vector__gtlisp_array(arr)
  let maxima_symbol = share_fft_core__make_maxima_array(length(arr))
  share_fft_core__set_symbol_array(maxima_symbol, lisp_array) |> ignore
  maxima_symbol
}

///|
fn maxima_fft_find_bf_fft_converter(
  input : Value,
  name? : Value = Str("bf_fft"),
) -> (Value, Value) raise {
  if d_listp(input).truthy() {
    (
      maxima_fft_mlist__gtbfft_vector(input),
      symbol_function(q_maxima_fft_bfft_vector__gtmlist),
    )
  } else if arrayp(input) {
    (
      maxima_fft_lisp_array__gtbfft_vector(input),
      symbol_function(q_maxima_fft_bfft_vector__gtlisp_array),
    )
  } else if symbolp(input) && symbol_array(mget(input, q_array)).truthy() {
    (
      maxima_fft_lisp_array__gtbfft_vector(symbol_array(mget(input, q_array))),
      symbol_function(q_maxima_fft_bfft_vector__gtmaxima_symbol_array),
    )
  } else {
    (
      merror(
        Str("~A: input is not a list or an array: ~M."),
        list2(name, input),
      ),
      Nil,
    )
  }
}

///|
fn maxima_fft_mlist__gtbf_rfft_vector(object_ : Value) -> Value raise {
  let n = length(cdr(object_))
  let z = make_array([n / 2], initial=Fix(0L))
  let mut k = 0
  let mut l = cdr(object_)
  while consp(l) {
    let re = car(l)
    let im = cadr(l)
    if im is Nil {
      break
    }
    aset1(z, k, complex(d_float(re), i=d_float(im))) |> ignore
    k = k + 1
    l = cddr(l)
  }
  z
}

///|
fn maxima_fft_lisp_array__gtbf_rfft_vector(object_ : Value) -> Value raise {
  let z = make_array([length(object_)], initial=Fix(0L))
  for k in 0..<length(object_) {
    let fl = risplit(d_float(aref1(object_, k)))
    aset1(z, k, complex(car(fl), i=cdr(fl))) |> ignore
  }
  z
}

///|
fn maxima_fft_find_bf_rfft_converters(object_ : Value) -> (Value, Value) raise {
  if d_listp(object_).truthy() {
    (
      maxima_fft_mlist__gtbf_rfft_vector(object_),
      symbol_function(q_maxima_fft_bfft_vector__gtmlist),
    )
  } else if arrayp(object_) {
    (
      maxima_fft_lisp_array__gtbf_rfft_vector(object_),
      symbol_function(q_maxima_fft_bfft_vector__gtlisp_array),
    )
  } else if symbolp(object_) && symbol_array(mget(object_, q_array)).truthy() {
    (
      maxima_fft_lisp_array__gtbf_rfft_vector(
        symbol_array(mget(object_, q_array)),
      ),
      lfunc("bf-rfft-symbol-array", args => {
        let array = arg(args, 0)
        let ar = maxima_fft_bfft_vector__gtlisp_array(array)
        let sym_ = share_fft_core__make_maxima_array(length(array))
        share_fft_core__set_symbol_array(sym_, ar)
      }),
    )
  } else {
    (
      merror(Str("bf_rfft: input is not a list or an array: ~M."), list1(object_)),
      Nil,
    )
  }
}

///|
fn maxima_fft_find_bf_irfft_converters(object_ : Value) -> (Value, Value) raise {
  if d_listp(object_).truthy() {
    (
      maxima_fft_mlist__gtbfft_vector(object_),
      lfunc("bf-irfft-mlist", args => {
        let obj = arg(args, 0)
        let c = Collector::new()
        for i in 0..<length(obj) {
          let z = aref1(obj, i)
          c.add(maxima_to(bf_realpart(z)))
          c.add(maxima_to(bf_imagpart(z)))
        }
        cons(list2(q_mlist, q_simp), c.result())
      }),
    )
  } else if arrayp(object_) {
    (
      maxima_fft_lisp_array__gtbfft_vector(object_),
      lfunc("bf-irfft-array", args => {
        let obj = arg(args, 0)
        let result = make_array([2 * length(obj)], initial=Fix(0L))
        for i in 0..<length(obj) {
          let z = aref1(obj, i)
          // CL REALPART/IMAGPART, as in the Lisp.
          aset1(result, 2 * i, realpart(z)) |> ignore
          aset1(result, 2 * i + 1, imagpart(z)) |> ignore
        }
        result
      }),
    )
  } else {
    (
      merror(
        Str("bf_inverse_real_fft: input is not a list or an array: ~M."),
        list1(object_),
      ),
      Nil,
    )
  }
}

// Bigfloat implementation of Fast Fourier Transform using a radix-2
// algorithm with inputs and outputs in natural order (package BIGFLOAT).

///|
/// For an FFT order of M, return an array of complex bigfloat twiddle
/// factors for the FFT. The array contains the values
/// exp(i*pi*k/2^(m-1)).  The cache key includes fpprec in case the caller
/// changes the requested precision.
fn bf_sincos_table(m : Value) -> Value raise {
  let tables = symval(q_ear_bf_sincos_tables)
  let key = list2(m, symval(q_fpprec))
  let cached = gethash(key, tables)
  if cached.truthy() {
    return cached
  }
  // Need to create the sincos table.  Only need to have a half period.
  let n = to_int(ash(Fix(1L), to_int(m) - 1))
  let p = bf_div(bf_p_pi(bf_bigfloat(Fix(1L))), int(n))
  let table = make_array([n], initial=Fix(0L))
  for k in 0..<n {
    aset1(table, k, bf_cis(bf_mul(int(k), p))) |> ignore
  }
  // Make the half point exactly correct
  if n > 1 {
    aset1(table, n / 2, bf_bigfloat(Fix(0L), im=Fix(1L))) |> ignore
  }
  sethash(list2(m, symval(q_fpprec)), tables, table) |> ignore
  table
}

///|
/// Fast Fourier Transform using a simple radix-2 implementation with
/// inputs and outputs in natural order.  The input and output are assumed
/// to be bigfloats objects.
fn bf_fft_r2_nn(x : Value, inverse_fft_p? : Value = Nil) -> Value raise {
  let n = length(x)
  let sincos = bf_sincos_table(maxima_fft_log_base2(int(n)))
  let a = share_fft_core__fft_loop(
    copy_seq(x),
    make_array([n], initial=Fix(0L)),
    sincos,
    inverse_fft_p.truthy(),
    (p, q) => bf_mul(p, q),
    (p, q) => bf_add(p, q),
    (p, q) => bf_sub(p, q),
    p => bf_conjugate(p),
  )
  if inverse_fft_p.truthy() {
    a
  } else {
    for k in 0..<length(a) {
      aset1(a, k, bf_div(aref1(a, k), int(n))) |> ignore
    }
    a
  }
}

///|
fn init_share_fft_core() -> Unit raise {
  if !boundp(q_ear_sincos_tables) {
    set(q_ear_sincos_tables, make_hash_table()) |> ignore
  }
  if !boundp(q_ear_bf_sincos_tables) {
    set(q_ear_bf_sincos_tables, make_hash_table(kind=Equal)) |> ignore
  }
}
