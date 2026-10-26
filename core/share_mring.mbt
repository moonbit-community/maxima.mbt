// Port of share/linearalgebra/mring.lisp: a Maxima ring structure.
//
// The CL defstruct `mring` is a `make_struct("mring", ...)` instance (it is
// stored on the `ring` property of the ring names and passed around as a
// Lisp value). Its slot accessors `mring-name` ... are installed as Lisp
// functions by `init_share_mring` (src/invert.lisp calls them through
// MFUNCALL); MoonBit code uses `share_mring__slot`.
//
// Description of the mring fields:
//
// For floating point numbers (both real and complex), the lu_factor code
// uses partial pivoting. Thus lu_factor needs to be able to compare the
// magnitudes, using the function `great` (always called on the magnitude of
// a ring element). For nonordered fields (such as generalring) where partial
// pivoting isn't needed, `great` is (lambda (a b) (eq t (meqp b 0))): it
// inhibits row swapping unless it is absolutely needed to avoid dividing by
// zero.
//
// The function coerce-to-lisp-float is only used by lu_factor to estimate
// the matrix condition number; nil inhibits estimating it.

///|
let share_mring__slot_names : Array[String] = [
  "name", "coerce-to-lisp-float", "abs", "great", "add", "div", "rdiv", "reciprocal",
  "mult", "sub", "negate", "psqrt", "add-id", "mult-id", "fzerop", "adjoint", "maxima-to-mring",
  "mring-to-maxima",
]

///|
fn share_mring__slot(fld : Value, name : String) -> Value raise {
  match share_mring__slot_names.search(name) {
    Some(i) => struct_ref(fld, i)
    None => abort("mring: no slot " + name)
  }
}

///|
fn share_mring__name(fld : Value) -> Value raise {
  struct_ref(fld, 0)
}

///|
/// `(funcall (mring-<slot> fld) args...)`
fn share_mring__call(fld : Value, name : String, args : Array[Value]) -> Value raise {
  funcall(share_mring__slot(fld, name), args)
}

///|
/// `(make-mring :name ...)` from (slot, value) pairs; missing slots are nil.
fn share_mring__make(slots : Array[(String, Value)]) -> Value {
  let vals = Array::make(share_mring__slot_names.length(), Value::Nil)
  for s in slots {
    match share_mring__slot_names.search(s.0) {
      Some(i) => vals[i] = s.1
      None => ()
    }
  }
  make_struct("mring", vals)
}

///|
fn share_mring__f1(name : String, f : (Value) -> Value raise) -> Value {
  lfunc(name, args => f(args[0]))
}

///|
fn share_mring__f2(name : String, f : (Value, Value) -> Value raise) -> Value {
  lfunc(name, args => f(args[0], args[1]))
}

///|
fn share_mring__f0(name : String, f : () -> Value raise) -> Value {
  lfunc(name, _ => f())
}

///|
fn d_require_ring(ringname : Value, pos : Value, fun : Value) -> Value raise {
  if d_member(ringname, symval(q_d__pctmrings)).truthy() ||
    member(ringname, symval(q_ear_gf_rings)).truthy() {
    get(ringname, q_ring)
  } else {
    merr("The ~:M argument of the function '~:M' must be the name of a ring", [
      pos, fun,
    ])
  }
}

///|
fn share_mring__fzerop_float(s : Value) -> Value raise {
  lbool(num_lt(num_abs(s), num_mul(Fix(4L), symval(q_n_plusflonum_epsilon_plus))))
}

///|
fn coerce_expr_to_clcomplex(ex : Value) -> Value raise {
  with_specials([(q_d_numer, t), (q_d_float, t)], () => {
    let split = risplit(ex)
    // convert int, rat, and bfloat to float
    let re = d_float(car(split))
    let im = d_float(cdr(split))
    if floatp(re) && floatp(im) {
      complex(re, i=im)
    } else {
      merr("Unable to convert ~:M to a complex float", [ex])
    }
  })
}

///|
fn rational_square_root(z : Value) -> Value raise {
  let mut re = realpart(z)
  let mut im = imagpart(z)
  re = div(d_num(re), d_denom(re))
  im = div(d_num(im), d_denom(im))
  let q = risplit(
    ftake(q_p_sqrt, [add2(re, mul2(q_d__pcti, im))]),
  )
  re = car(q)
  im = cdr(q)
  if d_ratnump(re).truthy() && d_ratnump(im).truthy() {
    complex(
      num_div(d_num(re), d_denom(re)),
      i=num_div(d_num(im), d_denom(im)),
    )
  } else {
    Nil
  }
}

///|
fn fp_abs(a : Value) -> Value raise {
  list2(num_abs(first(a)), second(a))
}

///|
fn share_mring__fp_err(a : Value, b : Value, s : Value) -> Value raise {
  ceiling1(
    num_add(
      num_add(Fix(1L), num_abs(num_div(num_mul(first(a), second(a)), s))),
      num_abs(num_div(num_mul(first(b), second(b)), s)),
    ),
  )
}

///|
fn fp_plus(a : Value, b : Value) -> Value raise {
  if num_eq(first(a), Flo(0.0)) {
    b
  } else if num_eq(first(b), Flo(0.0)) {
    a
  } else {
    let s = num_add(first(a), first(b))
    if num_eq(Flo(0.0), s) {
      merr("floating point divide by zero", []) |> ignore
    }
    list2(s, share_mring__fp_err(a, b, s))
  }
}

///|
fn fp_(a : Value, b : Value) -> Value raise {
  if num_eq(first(a), Flo(0.0)) {
    list2(num_neg(first(b)), second(b))
  } else if num_eq(first(b), Flo(0.0)) {
    a
  } else {
    let s = num_sub(first(a), first(b))
    if num_eq(Flo(0.0), s) {
      merr("floating point divide by zero", []) |> ignore
    }
    list2(s, share_mring__fp_err(a, b, s))
  }
}

///|
fn fp_star(a : Value, b : Value) -> Value raise {
  if num_eq(first(a), Flo(0.0)) || num_eq(first(b), Flo(0.0)) {
    list2(Flo(0.0), Fix(0L))
  } else {
    list2(
      num_mul(first(a), first(b)),
      num_add(num_add(Fix(1L), second(a)), second(b)),
    )
  }
}

///|
fn fp_sl(a : Value, b : Value) -> Value raise {
  if num_eq(first(a), Fix(0L)) {
    list2(Flo(0.0), Fix(0L))
  } else {
    list2(
      num_div(first(a), first(b)),
      num_add(num_add(Fix(1L), second(a)), second(b)),
    )
  }
}

///|
fn d_addmatrices(fn_ : Value, m : Value) -> Value raise {
  mfuncall(q_d_apply, list2(q_d_matrixmap, cons(list1(q_mlist), cons(fn_, m))))
}

///|
/// `(reduce f l :from-end t)` for a nonempty list.
fn share_mring__reduce_from_end(
  f : Value,
  l : Value,
) -> Value raise {
  let xs = list_to_array(l)
  if xs.length() == 0 {
    return funcall(f, [])
  }
  let mut acc = xs[xs.length() - 1]
  let mut i = xs.length() - 2
  while i >= 0 {
    acc = funcall(f, [xs[i], acc])
    i -= 1
  }
  acc
}

///|
fn ring_eval(e : Value, fld : Value) -> Value raise {
  let fadd = share_mring__slot(fld, "add")
  let fnegate = share_mring__slot(fld, "negate")
  let fmult = share_mring__slot(fld, "mult")
  let fdiv = share_mring__slot(fld, "div")
  let fabs = share_mring__slot(fld, "abs")
  let fconvert = share_mring__slot(fld, "maxima-to-mring")
  if d_numberp(e).truthy() || symbolp(e) {
    funcall(fconvert, [meval(e)])
  } else if op_equalp(e, list1(q_mplus)).truthy() {
    share_mring__reduce_from_end(fadd, mapcar(s => ring_eval(s, fld), margs(e)))
  } else if op_equalp(e, list1(q_mminus)).truthy() {
    funcall(fnegate, [ring_eval(first(margs(e)), fld)])
  } else if op_equalp(e, list1(q_mtimes)).truthy() {
    share_mring__reduce_from_end(fmult, mapcar(s => ring_eval(s, fld), margs(e)))
  } else if op_equalp(e, list1(q_mquotient)).truthy() {
    funcall(fdiv, [
      ring_eval(first(margs(e)), fld),
      ring_eval(second(margs(e)), fld),
    ])
  } else if op_equalp(e, list1(q_mabs)).truthy() {
    funcall(fabs, [ring_eval(first(margs(e)), fld)])
  } else if (
      eq(share_mring__name(fld), q_d_floatfield) ||
      eq(share_mring__name(fld), q_d_complexfield)
    ) &&
    consp(e) &&
    consp(car(e)) &&
    gethash(mop(e), symval(q_ear_flonum_op)).truthy() {
    apply(
      gethash(mop(e), symval(q_ear_flonum_op)),
      mapcar(s => ring_eval(s, fld), margs(e)),
    )
  } else {
    merr("Unable to evaluate ~:M in the ring '~:M'", [e, share_mring__name(fld)])
  }
}

///|
fn d_ringeval(e : Value) -> Value raise {
  let found = car(member(meval(nth(2, e)), symval(q_d__pctmrings)))
  let fld = get(if found.truthy() { found } else { q_d_generalring }, q_ring)
  share_mring__call(fld, "mring-to-maxima", [ring_eval(nth(1, e), fld)])
}

///|
fn share_mring__noncommuting_env(f : () -> Value raise) -> Value raise {
  with_specials(
    [
      (q_d_matrix_element_mult, Str(".")),
      (q_d_matrix_element_transpose, q_d_transpose),
    ],
    f,
  )
}

///|
fn share_mring__nc_inverse(b : Value) -> Value raise {
  if d_matrixp(b).truthy() {
    d_invert_by_lu(b, fld=q_d_noncommutingring)
  } else {
    take(list1(q_mncexpt), [b, Fix(-1L)])
  }
}

///|
fn init_share_mring() -> Unit raise {
  d_put(q_d_mring, Fix(1L), q_d_version) |> ignore
  // The defstruct accessors, as Lisp functions.
  for i, name in share_mring__slot_names {
    let k = i
    defun(sym("mring-" + name), args => struct_ref(args[0], k))
  }
  defun(sym("mring-p"), args => lbool(struct_typep(args[0], "mring")))
  if !boundp(q_d__pctmrings) {
    set(
      q_d__pctmrings,
      list([
        list1(q_mlist),
        q_d_floatfield,
        q_d_complexfield,
        q_d_rationalfield,
        q_d_crering,
        q_d_generalring,
        q_d_bigfloatfield,
        q_d_runningerror,
        q_d_noncommutingring,
      ]),
    )
    |> ignore
  }
  let identity = share_mring__f1("identity", s => s)
  let plus = share_mring__f2("+", (a, b) => num_add(a, b))
  let minus = share_mring__f2("-", (a, b) => num_sub(a, b))
  let times = share_mring__f2("*", (a, b) => num_mul(a, b))
  let divide = share_mring__f2("/", (a, b) => num_div(a, b))
  let recip = share_mring__f1("/", a => num_inv(a))
  let negate = share_mring__f1("-", a => num_neg(a))
  let cl_abs = share_mring__f1("abs", a => num_abs(a))
  let gt = share_mring__f2(">", (a, b) => lbool(num_gt(a, b)))
  let general_great = share_mring__f2("great", (_a, b) => lbool(
    eq(t, meqp(b, Fix(0L))),
  ))
  let general_fzerop = share_mring__f1("fzerop", s => lbool(
    eq(t, meqp(s, Fix(0L))),
  ))
  let cabs = share_mring__f1("$cabs", s => ftake(q_p_cabs, [s]))
  let msqrt = share_mring__f1("psqrt", s => ftake(q_mexpt, [
    s,
    div(Fix(1L), Fix(2L)),
  ]))
  let mconj = share_mring__f1("adjoint", s => ftake(q_d_conjugate, [s]))
  let recip_m = share_mring__f1("reciprocal", s => div(Fix(1L), s))
  let neg_m = share_mring__f1("negate", s => mul2(Fix(-1L), s))
  // flonum-epsilon is defined in clmacs
  let floatfield = share_mring__make([
    ("name", q_d_floatfield),
    ("coerce-to-lisp-float", identity),
    ("abs", cl_abs),
    ("great", gt),
    ("add", plus),
    ("div", divide),
    ("rdiv", divide),
    ("reciprocal", recip),
    ("mult", times),
    ("sub", minus),
    ("negate", negate),
    (
      "psqrt",
      share_mring__f1("psqrt", s => if num_ge(s, Fix(0L)) { lsqrt(s) } else {
        Nil
      }),
    ),
    ("add-id", share_mring__f0("add-id", () => Flo(0.0))),
    ("mult-id", share_mring__f0("mult-id", () => Flo(1.0))),
    ("fzerop", share_mring__f1("fzerop", share_mring__fzerop_float)),
    ("adjoint", identity),
    ("mring-to-maxima", identity),
    (
      "maxima-to-mring",
      share_mring__f1("maxima-to-mring", s => {
        let s = d_float(s)
        if floatp(s) {
          s
        } else {
          merr("Unable to convert ~:M to a float", [s])
        }
      }),
    ),
  ])
  set(q_ear_floatfield, floatfield) |> ignore
  setf_get(q_d_floatfield, q_ring, floatfield) |> ignore
  let complexfield = share_mring__make([
    ("name", q_d_complexfield),
    ("coerce-to-lisp-float", identity),
    ("abs", cl_abs),
    ("great", gt),
    ("add", plus),
    ("div", divide),
    ("rdiv", divide),
    ("reciprocal", recip),
    ("mult", times),
    ("sub", minus),
    ("negate", negate),
    (
      "psqrt",
      share_mring__f1("psqrt", s => if num_eq(Fix(0L), imagpart(s)) &&
        num_ge(realpart(s), Fix(0L)) {
        lsqrt(s)
      } else {
        Nil
      }),
    ),
    ("add-id", share_mring__f0("add-id", () => Flo(0.0))),
    ("mult-id", share_mring__f0("mult-id", () => Flo(1.0))),
    ("fzerop", share_mring__f1("fzerop", share_mring__fzerop_float)),
    ("adjoint", share_mring__f1("conjugate", a => conjugate(a))),
    (
      "mring-to-maxima",
      share_mring__f1("mring-to-maxima", s => add2(
        realpart(s),
        mul2(q_d__pcti, imagpart(s)),
      )),
    ),
    ("maxima-to-mring", q_coerce_expr_to_clcomplex),
  ])
  set(q_ear_complexfield, complexfield) |> ignore
  setf_get(q_d_complexfield, q_ring, complexfield) |> ignore
  // We allow both real and complex rational numbers.
  let rationalfield = share_mring__make([
    ("name", q_d_rationalfield),
    ("coerce-to-lisp-float", Nil),
    ("abs", cl_abs),
    ("great", share_mring__f2("great", (_a, b) => lbool(eql(b, Fix(0L))))),
    ("add", plus),
    ("div", divide),
    ("rdiv", divide),
    ("reciprocal", recip),
    ("mult", times),
    ("sub", minus),
    ("negate", negate),
    ("psqrt", q_rational_square_root),
    ("add-id", share_mring__f0("add-id", () => Fix(0L))),
    ("mult-id", share_mring__f0("mult-id", () => Fix(1L))),
    ("fzerop", share_mring__f1("fzerop", s => lbool(eql(s, Fix(0L))))),
    ("adjoint", identity),
    (
      "mring-to-maxima",
      share_mring__f1("mring-to-maxima", s => {
        let re = realpart(s)
        let im = imagpart(s)
        add2(
          div(numerator(re), denominator(re)),
          mul2(q_d__pcti, div(numerator(im), denominator(im))),
        )
      }),
    ),
    (
      "maxima-to-mring",
      share_mring__f1("maxima-to-mring", s => {
        let s = d_rationalize(s)
        let z = trisplit(s)
        let re = car(z)
        let im = cdr(z)
        if d_ratnump(re).truthy() && d_ratnump(im).truthy() {
          complex(
            num_div(d_num(re), d_denom(re)),
            i=num_div(d_num(im), d_denom(im)),
          )
        } else {
          merr("Unable to convert ~:M to a rational number", [s])
        }
      }),
    ),
  ])
  set(q_ear_rationalfield, rationalfield) |> ignore
  setf_get(q_d_rationalfield, q_ring, rationalfield) |> ignore
  let crering = share_mring__make([
    ("name", q_d_crering),
    ("coerce-to-lisp-float", Nil),
    ("abs", cabs),
    ("great", general_great),
    ("add", share_mring__f2("add", add2)),
    ("div", share_mring__f2("div", div)),
    ("rdiv", share_mring__f2("div", div)),
    ("reciprocal", recip_m),
    ("mult", share_mring__f2("mult", mult)),
    ("sub", share_mring__f2("sub", sub)),
    ("negate", neg_m),
    ("psqrt", msqrt),
    ("add-id", share_mring__f0("add-id", () => Fix(0L))),
    ("mult-id", share_mring__f0("mult-id", () => Fix(1L))),
    ("fzerop", general_fzerop),
    ("adjoint", mconj),
    ("mring-to-maxima", identity),
    ("maxima-to-mring", share_mring__f1("maxima-to-mring", s => d_rat(s, Nil))),
  ])
  set(q_ear_crering, crering) |> ignore
  setf_get(q_d_crering, q_ring, crering) |> ignore
  let generalring = share_mring__make([
    ("name", q_d_generalring),
    ("coerce-to-lisp-float", Nil),
    ("abs", cabs),
    ("great", general_great),
    ("add", share_mring__f2("add", add2)),
    ("div", share_mring__f2("div", div)),
    ("rdiv", share_mring__f2("div", div)),
    ("reciprocal", recip_m),
    ("mult", share_mring__f2("mul", mul2)),
    ("sub", share_mring__f2("sub", sub)),
    ("negate", neg_m),
    ("psqrt", msqrt),
    ("add-id", share_mring__f0("add-id", () => Fix(0L))),
    ("mult-id", share_mring__f0("mult-id", () => Fix(1L))),
    ("fzerop", general_fzerop),
    ("adjoint", mconj),
    ("mring-to-maxima", identity),
    ("maxima-to-mring", identity),
  ])
  set(q_ear_generalring, generalring) |> ignore
  setf_get(q_d_generalring, q_ring, generalring) |> ignore
  let bigfloatfield = share_mring__make([
    ("name", q_d_bigfloatfield),
    (
      "coerce-to-lisp-float",
      share_mring__f1("coerce-to-lisp-float", s => {
        let s = d_rectform(d_float(s))
        complex(d_realpart(s), i=d_imagpart(s))
      }),
    ),
    ("abs", cabs),
    ("great", q_mgrp),
    ("add", share_mring__f2("add", (a, b) => d_rectform(add2(a, b)))),
    ("div", share_mring__f2("div", (a, b) => d_rectform(div(a, b)))),
    ("rdiv", share_mring__f2("div", (a, b) => d_rectform(div(a, b)))),
    ("reciprocal", recip_m),
    ("mult", share_mring__f2("mult", (a, b) => d_rectform(mul2(a, b)))),
    ("sub", share_mring__f2("sub", (a, b) => d_rectform(sub(a, b)))),
    ("negate", neg_m),
    (
      "psqrt",
      share_mring__f1("psqrt", s => if mlsp(s, Fix(0L)).truthy() {
        Nil
      } else {
        ftake(q_p_sqrt, [s])
      }),
    ),
    ("add-id", share_mring__f0("add-id", () => symval(q_ear_bigfloatzero))),
    ("mult-id", share_mring__f0("mult-id", () => symval(q_ear_bigfloatone))),
    (
      "fzerop",
      share_mring__f1("fzerop", s => like(s, symval(q_ear_bigfloatzero))),
    ),
    ("adjoint", identity),
    ("mring-to-maxima", identity),
    (
      "maxima-to-mring",
      share_mring__f1("maxima-to-mring", s => {
        let s = d_rectform(d_bfloat(s))
        if complex_number_p(s, ntypep=q_bigfloat_or_number_p).truthy() {
          s
        } else {
          merr("Unable to convert matrix entry to a big float", [])
        }
      }),
    ),
  ])
  set(q_ear_bigfloatfield, bigfloatfield) |> ignore
  setf_get(q_d_bigfloatfield, q_ring, bigfloatfield) |> ignore
  // --- *gf-rings* --- (used by src/numth.lisp)
  let gf_coeff_ring = share_mring__make([
    ("name", q_gf_coeff_ring),
    ("coerce-to-lisp-float", Nil),
    ("abs", q_gf_cmod),
    ("great", share_mring__f2("great", (_a, b) => lbool(num_eq(Fix(0L), b)))),
    ("add", q_gf_cplus_b),
    (
      "div",
      share_mring__f2("div", (a, b) => gf_ctimes(a, gf_cinv(b))),
    ),
    (
      "rdiv",
      share_mring__f2("rdiv", (a, b) => gf_ctimes(a, gf_cinv(b))),
    ),
    ("reciprocal", q_gf_cinv),
    ("mult", q_gf_ctimes),
    (
      "sub",
      share_mring__f2("sub", (a, b) => gf_cplus_b(a, gf_cminus_b(b))),
    ),
    ("negate", q_gf_cminus_b),
    (
      "psqrt",
      share_mring__f1("psqrt", a => {
        let rs = zn_nrt(a, Fix(2L), symval(q_ear_gf_char))
        if rs.truthy() {
          car(rs)
        } else {
          Nil
        }
      }),
    ),
    ("add-id", share_mring__f0("add-id", () => Fix(0L))),
    ("mult-id", share_mring__f0("mult-id", () => Fix(1L))),
    ("fzerop", share_mring__f1("fzerop", s => lbool(num_eq(Fix(0L), s)))),
    ("adjoint", Nil),
    ("mring-to-maxima", identity),
    ("maxima-to-mring", identity),
  ])
  set(q_ear_gf_coeff_ring, gf_coeff_ring) |> ignore
  setf_get(q_gf_coeff_ring, q_ring, gf_coeff_ring) |> ignore
  fn gf_like(name : Value, red : Value, ord : Value) -> Value {
    share_mring__make([
      ("name", name),
      ("coerce-to-lisp-float", Nil),
      ("abs", q_gf_mod),
      ("great", share_mring__f2("great", (_a, b) => lbool(b is Nil))),
      ("add", q_gf_plus),
      (
        "div",
        share_mring__f2("div", (a, b) => gf_times(
          a,
          gf_inv(b, symval(red)),
          symval(red),
        )),
      ),
      (
        "rdiv",
        share_mring__f2("rdiv", (a, b) => gf_times(
          a,
          gf_inv(b, symval(red)),
          symval(red),
        )),
      ),
      ("reciprocal", share_mring__f1("reciprocal", a => gf_inv(a, symval(red)))),
      ("mult", share_mring__f2("mult", (a, b) => gf_times(a, b, symval(red)))),
      ("sub", share_mring__f2("sub", (a, b) => gf_plus(a, gf_minus(b)))),
      ("negate", q_gf_minus),
      (
        "psqrt",
        share_mring__f1("psqrt", a => {
          let rs = gf_nrt_exit(gf_nrt(a, Fix(2L), symval(red), symval(ord)))
          if rs.truthy() {
            cadr(rs)
          } else {
            Nil
          }
        }),
      ),
      ("add-id", share_mring__f0("add-id", () => Nil)),
      ("mult-id", share_mring__f0("mult-id", () => list2(Fix(0L), Fix(1L)))),
      ("fzerop", share_mring__f1("fzerop", s => lbool(s is Nil))),
      ("adjoint", Nil),
      ("mring-to-maxima", q_gf_x2p),
      ("maxima-to-mring", q_gf_p2x),
    ])
  }

  let gf_ring = gf_like(q_gf_ring, q_ear_gf_red, q_ear_gf_ord)
  set(q_ear_gf_ring, gf_ring) |> ignore
  setf_get(q_gf_ring, q_ring, gf_ring) |> ignore
  let ef_ring = gf_like(q_ef_ring, q_ear_ef_red, q_ear_ef_ord)
  set(q_ear_ef_ring, ef_ring) |> ignore
  setf_get(q_ef_ring, q_ring, ef_ring) |> ignore
  let runningerror = share_mring__make([
    ("name", q_d_runningerror),
    (
      "coerce-to-lisp-float",
      share_mring__f1("coerce-to-lisp-float", s => if consp(s) {
        first(s)
      } else {
        s
      }),
    ),
    ("abs", q_fp_abs),
    (
      "great",
      share_mring__f2("great", (a, b) => lbool(num_gt(first(a), first(b)))),
    ),
    ("add", q_fp_plus),
    ("div", q_fp_sl),
    ("rdiv", q_fp_sl),
    (
      "reciprocal",
      share_mring__f1("reciprocal", s => fp_sl(list2(Fix(1L), Fix(0L)), s)),
    ),
    ("mult", q_fp_star),
    ("sub", q_fp_),
    (
      "negate",
      share_mring__f1("negate", s => list2(num_neg(first(s)), second(s))),
    ),
    (
      "psqrt",
      share_mring__f1("psqrt", s => if num_gt(first(s), Fix(0L)) {
        list2(lsqrt(first(s)), num_add(Fix(1L), second(s)))
      } else {
        Nil
      }),
    ),
    ("add-id", share_mring__f0("add-id", () => list2(Fix(0L), Fix(0L)))),
    ("mult-id", share_mring__f0("mult-id", () => list2(Fix(1L), Fix(0L)))),
    ("fzerop", share_mring__f1("fzerop", s => like(first(s), Fix(0L)))),
    ("adjoint", identity),
    (
      "mring-to-maxima",
      share_mring__f1("mring-to-maxima", s => cons(list1(q_mlist), s)),
    ),
    (
      "maxima-to-mring",
      share_mring__f1("maxima-to-mring", s => if d_listp(s).truthy() {
        cdr(s)
      } else {
        list2(d_float(s), Fix(1L))
      }),
    ),
  ])
  set(q_ear_runningerror, runningerror) |> ignore
  setf_get(q_d_runningerror, q_ring, runningerror) |> ignore
  let noncommutingring = share_mring__make([
    ("name", q_d_noncommutingring),
    ("coerce-to-lisp-float", Nil),
    ("abs", cabs),
    (
      "great",
      share_mring__f2("great", (_a, b) => lbool(
        !invertible_matrixp(b, q_d_noncommutingring).truthy(),
      )),
    ),
    ("add", share_mring__f2("add", add2)),
    (
      "div",
      share_mring__f2("div", (a, b) => share_mring__noncommuting_env(() => {
        let b = share_mring__nc_inverse(b)
        take(list1(q_mnctimes), [a, b])
      })),
    ),
    (
      "rdiv",
      share_mring__f2("rdiv", (a, b) => share_mring__noncommuting_env(() => {
        let b = share_mring__nc_inverse(b)
        take(list1(q_mnctimes), [b, a])
      })),
    ),
    (
      "reciprocal",
      share_mring__f1("reciprocal", s => share_mring__noncommuting_env(() => share_mring__nc_inverse(
        s,
      ))),
    ),
    (
      "mult",
      share_mring__f2("mult", (a, b) => share_mring__noncommuting_env(() => take(
        list1(q_mnctimes),
        [a, b],
      ))),
    ),
    ("sub", share_mring__f2("sub", sub)),
    ("negate", neg_m),
    ("add-id", share_mring__f0("add-id", () => Fix(0L))),
    ("psqrt", share_mring__f1("psqrt", s => take(list1(q_p_sqrt), [s]))),
    ("mult-id", share_mring__f0("mult-id", () => Fix(1L))),
    (
      "fzerop",
      share_mring__f1("fzerop", s => lbool(
        !invertible_matrixp(s, q_d_noncommutingring).truthy(),
      )),
    ),
    (
      "adjoint",
      share_mring__f1("adjoint", s => d_transpose(
        take(list1(q_d_conjugate), [s]),
      )),
    ),
    ("mring-to-maxima", identity),
    ("maxima-to-mring", identity),
  ])
  set(q_ear_noncommutingring, noncommutingring) |> ignore
  setf_get(q_d_noncommutingring, q_ring, noncommutingring) |> ignore
}
