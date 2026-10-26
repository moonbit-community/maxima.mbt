// Port of share/contrib/chebformax.lisp (Richard Fateman): a package for
// Chebyshev approximations of functions on [-1,1]. A chebseries is
// (($chebseries) a0 a1 ... ) holding double-float coefficients.

///|
/// tocheb computes all the a_j, j=0 to n-1 for the Maxima function f.
fn d_tocheb(f : Value, n : Value) -> Value raise {
  cons(list1(q_d_chebseries), ajs(f, n))
}

///|
/// compute a[j]s for Maxima this way
fn ajs(f : Value, n : Value) -> Value raise {
  let c = Collector::new()
  let mut j = int(0)
  while num_le(j, one_minus(n)) {
    c.add(aj(f, j, n))
    j = one_plus(j)
  }
  c.result()
}

///|
/// It turns out we will be re-using certain key values repeatedly, so we
/// save them in the hash table *cosc*.
fn cachecos(r : Value) -> Value raise {
  let v = gethash(r, symval(q_ear_cosc))
  if v.truthy() {
    v
  } else {
    sethash(r, symval(q_ear_cosc), lcos(r))
  }
}

///|
/// compute just one coefficient, a_j out of n for function f
fn aj(f : Value, j : Value, n : Value) -> Value raise {
  let in_ = num_div(Flo(1.0), n) // inverse of n
  let mut sum = int(0)
  let mut k = int(0)
  while num_le(k, one_minus(n)) {
    let h = num_mul(
      num_mul(Flo(3.141592653589793), num_add(k, Flo(0.5))),
      in_,
    )
    sum = num_add(
      sum,
      num_mul(
        cachecos(num_mul(h, j)),
        mapply1(f, list1(cachecos(h)), f, f),
      ),
    )
    k = one_plus(k)
  }
  num_mul(
    num_mul(
      num_mul(in_, int(2)),
      num_sub(int(2), if num_eq(j, n) { int(0) } else { int(1) }),
    ),
    sum,
  )
}

///|
/// Clenshaw algorithm: evaluate p=sum'(a_nT_n(x), i=0 to N), a is a
/// chebseries; sum' multiplies a_0 by 1/2.
fn d_cheb_call(a : Value, x : Value) -> Value raise {
  if eq(caar(a), q_d_chebseries) {
    let x = to_double(x)
    let mut bj2 = 0.0
    let mut bj1 = 0.0
    let mut bj0 = 0.0
    let mut a = reverse(cdr(a)) // could hack this away. maybe later
    while cdr(a).truthy() {
      let p = to_double(car(a))
      a = cdr(a)
      bj0 = 2.0 * x * bj1 + -bj2 + p
      bj2 = bj1
      bj1 = bj0
    }
    let p = to_double(car(a))
    Flo(x * bj1 + 0.5 * p + -bj2)
  } else {
    raise LispError::SimpleError(
      format_to_string("expecting chebseries,not ~s", [a]),
    )
  }
}

///|
/// a slower version, chebplus, is below
fn d_chebadd(a : Value, b : Value) -> Value raise {
  let mut a = a
  let mut b = b
  let mut ans : Value = Nil
  if length(a) > length(b) {
    a = append(cdr(a), Nil) // copy
    ans = a
    b = cdr(b)
    while b.truthy() {
      rplaca(a, num_add(car(a), car(b))) |> ignore
      b = cdr(b)
      a = cdr(a)
    }
  } else {
    b = append(cdr(b), Nil) // copy
    ans = b
    a = cdr(a)
    while a.truthy() {
      rplaca(b, num_add(car(b), car(a))) |> ignore
      a = cdr(a)
      b = cdr(b)
    }
  }
  cons(list1(q_d_chebseries), ans)
}

///|
/// (coerce l 'simple-array). SBCL does not accept SIMPLE-ARRAY (without an
/// element type and rank) as a sequence type for COERCE and signals a type
/// error for any list, so $CHEBMUL and $CHEBINT fail in the reference
/// Maxima; the port reproduces that.
fn share_chebformax__coerce_simple_array(l : Value) -> Array[Value] raise {
  raise LispError::SimpleError(
    prin1_to_string(l) + " can't be converted to type SIMPLE-ARRAY.",
  )
}

///|
/// Assumes each is a chebseries. No error checking here. A slower version
/// is below.
fn d_chebmul(a : Value, b : Value) -> Value raise {
  let aa = share_chebformax__coerce_simple_array(rest(a))
  let bb = share_chebformax__coerce_simple_array(rest(b))
  let la = aa.length()
  let lb = bb.length()
  let ans : Array[Value] = Array::make(la + lb - 1, Flo(0.0))
  aa[0] = num_mul(Flo(0.5), aa[0])
  bb[0] = num_mul(Flo(0.5), bb[0])
  for i in 0..<la {
    for j in 0..<lb {
      let term = num_mul(aa[i], bb[j])
      ans[i + j] = num_add(ans[i + j], term)
      let d = (i - j).abs()
      ans[d] = num_add(ans[d], term)
    }
  }
  for i in 1..=(la + lb - 2) {
    // not ans[0]
    ans[i] = num_mul(ans[i], Flo(0.5))
  }
  cons(list1(q_d_chebseries), list(ans))
}

///|
/// how about composition? f, g are chebseries; simple hack is to evaluate
/// f(g(x)) as needed.
fn d_chebcomp(f : Value, g : Value, n : Value) -> Value raise {
  d_tocheb(
    lfunc("chebcomp", args => d_cheb_call(f, d_cheb_call(g, args[0]))),
    // how many points are justified though??
    n,
  )
}

///|
fn d_chebplus(f : Value, g : Value) -> Value raise {
  d_tocheb(
    lfunc("chebplus", args => num_add(
      d_cheb_call(f, args[0]),
      d_cheb_call(g, args[0]),
    )),
    int(if length(f) > length(g) { length(f) } else { length(g) }),
  )
}

///|
fn d_chebtimes(f : Value, g : Value) -> Value raise {
  d_tocheb(
    lfunc("chebtimes", args => num_mul(
      d_cheb_call(f, args[0]),
      d_cheb_call(g, args[0]),
    )),
    int(length(f) + length(g) - 1),
  )
}

///|
/// f is a chebseries. Compute 1/f
fn d_chebinv(f : Value, n : Value) -> Value raise {
  d_tocheb(
    lfunc("chebinv", args => num_div(Flo(1.0), d_cheb_call(f, args[0]))),
    n,
  )
}

///|
/// Apply any maxima function to a chebseries. The Lisp code calls $TOCHEB
/// (a function of two arguments) with three arguments, which is a CL
/// program error.
fn d_chebapply(fun : Value, cs : Value, n : Value) -> Value raise {
  let _ = lfunc("chebapply", args => mapply1(fun, list1(args[0]), fun, fun))
  let _ = cs
  let _ = n
  raise LispError::SimpleError("invalid number of arguments: 3")
}

///|
/// Indefinite integration of the function given by a.
///   integrate(t[n](x),x) =
///   if n=0 then t[1].
///   if n=1 then  1/2*t[0] +1/4*t[2]  else
///   1/2*(t[n+1]/(n+1) - t[n-1]/(n-1))
fn d_chebint(a : Value) -> Value raise {
  let aa = vector(share_chebformax__coerce_simple_array(rest(a)))
  let la = length(aa)
  let ans = make_array([if 2 > la + 1 { 2 } else { la + 1 }], initial=Flo(0.0))
  aset1(aa, 0, num_mul(Flo(0.5), aref1(aa, 0))) |> ignore
  aset1(ans, 1, aref1(aa, 0)) |> ignore // int(const)= const*x
  aset1(ans, 0, num_mul(Flo(0.25), aref1(aa, 1))) |> ignore // int(x) = x^2/2 =1/4*T[0]+
  aset1(ans, 2, num_mul(Flo(0.25), aref1(aa, 1))) |> ignore // ...+ 1/4*T[2]
  for i in 2..<la {
    let term = num_mul(Flo(0.5), aref1(aa, i))
    aset1(ans, i + 1, num_add(aref1(ans, i + 1), num_div(term, int(i + 1))))
    |> ignore
    aset1(ans, i - 1, num_sub(aref1(ans, i - 1), num_div(term, int(i - 1))))
    |> ignore
  }
  aset1(ans, 0, num_mul(Flo(0.5), aref1(ans, 0))) |> ignore // so sum' works
  cons(list1(q_d_chebseries), vector_to_list(ans))
}

///|
fn init_share_chebformax() -> Unit raise {
  // store useful values of cosine here.
  defvar_init(q_ear_cosc, make_hash_table())
}
