// Port of share/cobyla/bf-cobyla-interface.lisp: bf_fmin_cobyla, the
// bigfloat version of fmin_cobyla.  COBYLA itself is the translation of
// share/cobyla/lisp/bf-*.lisp in the package dii/maxima/cobyla, generic over
// its BfReal trait; the instance below is the BIGFLOAT package's generic
// arithmetic (numeric.lisp) on Lisp values.

///|
/// A value of the bigfloat-package COBYLA: a CL real or a BIGFLOAT object.
struct BfCobylaValue(Value)

///|
impl @cobyla.BfReal for BfCobylaValue with from_double(d) {
  BfCobylaValue(Flo(d))
}

///|
impl @cobyla.BfReal for BfCobylaValue with from_int(i) {
  BfCobylaValue(Fix(i.to_int64()))
}

///|
impl @cobyla.BfReal for BfCobylaValue with add(a, b) {
  BfCobylaValue(bf_add(a.0, b.0))
}

///|
impl @cobyla.BfReal for BfCobylaValue with sub(a, b) {
  BfCobylaValue(bf_sub(a.0, b.0))
}

///|
impl @cobyla.BfReal for BfCobylaValue with mul(a, b) {
  BfCobylaValue(bf_mul(a.0, b.0))
}

///|
impl @cobyla.BfReal for BfCobylaValue with div(a, b) {
  BfCobylaValue(bf_div(a.0, b.0))
}

///|
impl @cobyla.BfReal for BfCobylaValue with neg(a) {
  BfCobylaValue(bf_neg(a.0))
}

///|
impl @cobyla.BfReal for BfCobylaValue with expt(a, b) {
  BfCobylaValue(bf_expt(a.0, b.0))
}

///|
impl @cobyla.BfReal for BfCobylaValue with lt(a, b) {
  bf_lt(a.0, b.0)
}

///|
impl @cobyla.BfReal for BfCobylaValue with gt(a, b) {
  bf_gt(a.0, b.0)
}

///|
impl @cobyla.BfReal for BfCobylaValue with le(a, b) {
  bf_le(a.0, b.0)
}

///|
impl @cobyla.BfReal for BfCobylaValue with ge(a, b) {
  bf_ge(a.0, b.0)
}

///|
impl @cobyla.BfReal for BfCobylaValue with eq(a, b) {
  bf_eq(a.0, b.0)
}

///|
impl @cobyla.BfReal for BfCobylaValue with max(a, b) {
  BfCobylaValue(bf_max(a.0, list1(b.0)))
}

///|
impl @cobyla.BfReal for BfCobylaValue with min(a, b) {
  BfCobylaValue(bf_min(a.0, list1(b.0)))
}

///|
impl @cobyla.BfReal for BfCobylaValue with abs(a) {
  BfCobylaValue(bf_abs(a.0))
}

///|
impl @cobyla.BfReal for BfCobylaValue with sqrt(a) {
  BfCobylaValue(bf_sqrt(a.0))
}

///|
impl @cobyla.BfReal for BfCobylaValue with coerce_bigfloat(a) {
  BfCobylaValue(bf_coerce(a.0, sym("bigfloat")))
}

///|
/// FORMAT's ~w,d,e,k,'o,'p,'c/bigfloat:format-e/ directive: FORMAT-E is
/// called with the stream, the value, the colon/at flags and the
/// parameters (an empty one is NIL).
impl @cobyla.BfReal for BfCobylaValue with format_directive(a, d) {
  if !d.has_suffix("/bigfloat:format-e/") {
    return princ_to_string(a.0)
  }
  let body = d.substring(start=1, end=d.length() - "/bigfloat:format-e/".length())
  if !(numeric__bfp(a.0) || numeric__cbfp(a.0)) {
    // FORMAT-E prints any other number with CL's ~E and the same
    // parameters, which is the f2cl runtime's ~E (SBCL's FORMAT-EXP-AUX).
    let arg : @f2cl.FArg = match a.0 {
      Flo(x) => AD(x)
      Fix(n) => AI(n.to_int())
      _ => return princ_to_string(a.0)
    }
    let sb = StringBuilder::new()
    let saved = @f2cl.output_hook.val
    @f2cl.output_hook.val = s => sb.write_string(s)
    @f2cl.fformat(6, [Dir("~" + body + "E")], [arg])
    @f2cl.output_hook.val = saved
    return sb.to_string()
  }
  let params : Array[Value] = []
  for p in body.split(",") {
    let p = p.to_string()
    params.push(
      if p == "" {
        Nil
      } else if p.has_prefix("'") {
        Char(p.get_char(1).unwrap())
      } else {
        let mut v = 0L
        for ch in p {
          v = v * 10L + (ch.to_int() - '0'.to_int()).to_int64()
        }
        Fix(v)
      },
    )
  }
  fn param(k : Int) -> Value {
    if k < params.length() {
      params[k]
    } else {
      Nil
    }
  }

  with_output_to_string(s => bf_format_e(
    s,
    a.0,
    Nil,
    Nil,
    w=param(0),
    d=param(1),
    e=param(2),
    k=param(3),
    overflowchar=param(4),
    padchar=param(5),
    exponentchar=param(6),
  )
  |> ignore) catch {
    _ => princ_to_string(a.0)
  }
}

///|
/// CALCFC(N, M, X, F, CON) with X and the section of the work array CON as
/// Lisp vectors: bigfloat::calcfc, which funcalls *CALCFC*; the constraint
/// values it stores are copied back.
impl @cobyla.BfReal for BfCobylaValue with calcfc(n, m, x, f, con, co) {
  let xa = make_array([x.length()], initial=Fix(0L))
  for i, v in x {
    aset1(xa, i, v.0) |> ignore
  }
  let len = con.length() - co
  let ca = make_array([len], initial=Fix(0L))
  for i in 0..<len {
    aset1(ca, i, con[co + i].0) |> ignore
  }
  let fval = bf_calcfc(Fix(n.to_int64()), Fix(m.to_int64()), xa, f.0, ca)
  for i in 0..<len {
    con[co + i] = BfCobylaValue(aref1(ca, i))
  }
  BfCobylaValue(fval)
}

///|
/// COBYLA always calls CALCFC to compute the function value and the
/// constraint equations.  CALCFC calls *CALCFC* to do the real computation
/// (whose function returns F; see cobyla_calcfc).
fn bf_calcfc(
  n : Value,
  m : Value,
  x : Value,
  _f : Value,
  con : Value,
) -> Value raise {
  funcall(symval(q_ear_calcfc), [n, m, x, con])
}

///|
/// The actual interface to COBYLA.  Take the inputs from maxima, massage
/// them into a suitable Lisp form, and call COBYLA to find the answer.
///
/// The keyword RHOEND has a supplied-p variable in the Lisp; the declared
/// signature has none, so an explicit rhoend = false counts as not given.
fn d_bf_fmin_cobyla(
  f : Value,
  vars : Value,
  init_x : Value,
  constraints? : Value = Nil,
  rhobeg? : Value = Flo(1.0),
  rhoend? : Value = Nil,
  iprint? : Value = Fix(0L),
  maxfun? : Value = Fix(1000L),
) -> Value raise {
  let pretty = cobyla__pretty_fname(q_d_bf_fmin_cobyla, Nil)
  cobyla__check_args(pretty, vars, init_x, iprint, maxfun)
  let rhoend = if rhoend is Nil {
    bf_sqrt(
      bf_expt(bf_bigfloat(Fix(10L)), num_neg(symval(q_d_fpprec))),
    )
  } else {
    rhoend
  }
  let normalized_constraints = cobyla__normalize_constraints(
    pretty, constraints,
  )
  let n = length(cdr(vars))
  let m = length(cdr(normalized_constraints))
  let x0 : Array[Value] = []
  for z in cdr(init_x).iter() {
    x0.push(bf_to(d_bfloat(z)))
  }
  if x0.length() != n {
    raise LispError::SimpleError(
      "There are " +
      x0.length().to_string() +
      " elements in the :INITIAL-CONTENTS, but the vector length is " +
      n.to_string() +
      ".",
    )
  }
  let x : Array[BfCobylaValue] = x0.map(v => BfCobylaValue(v))
  // Real work array for cobyla.
  let w : Array[BfCobylaValue] = Array::make(
    n * (3 * n + 2 * m + 11) + (4 * m + 6) + 6,
    BfCobylaValue(Fix(0L)),
  )
  // Integer work array for cobyla.
  let iact : FixedArray[Int] = FixedArray::make(m + 1, 0)
  let fv = coerce_bfloat_fun(f, list([vars]))
  let cv = coerce_bfloat_fun(normalized_constraints, list([vars]))
  // Compute the function and the constraints at the given xval.  The
  // function value is returned, and the constraint values are stored in
  // cval.
  let calcfc = lfunc("bf_fmin_cobyla-calcfc", args => {
    let xval = args[2]
    let cval = args[3]
    let xl = Collector::new()
    for v in as_array(xval).data {
      xl.add(maxima_to(v))
    }
    let x_list = xl.result()
    let f = bf_maybe_to(apply(fv, x_list))
    let c = mapcar(v => bf_maybe_to(v), cdr(apply(cv, x_list)))
    if !(floatp(f) || d_bfloatp(f).truthy() || numeric__bfp(f)) {
      merr(
        "At the point ~M:~%The objective function did not evaluate to a number: ~M",
        [cons(list1(q_mlist), x_list), f],
      )
      |> ignore
    }
    let bad_cons : Array[Int] = []
    let mut k = 1
    for cv in c.iter() {
      if !(floatp(cv) || d_bfloatp(cv).truthy() || numeric__bfp(cv)) {
        bad_cons.push(k)
      }
      k = k + 1
    }
    if bad_cons.length() > 0 {
      // List the constraints that did not evaluate to a number to make it
      // easier for the user to figure out which constraints were bad.
      mformat(
        list([t, Str("At the point ~M:~%"), cons(list1(q_mlist), x_list)]),
      )
      |> ignore
      let msg = with_output_to_string(msg => for index in bad_cons {
        mformat(
          list([
            msg,
            Str("Constraint ~M did not evaluate to a real: ~M~%"),
            Fix(index.to_int64()),
            nth(index, normalized_constraints),
          ]),
        )
        |> ignore
      })
      merror(Str(msg), Nil) |> ignore
    }
    // (replace cval c)
    let a = as_array(cval)
    let mut j = 0
    for v in c.iter() {
      if j >= a.data.length() {
        break
      }
      a.data[j] = v
      j = j + 1
    }
    f
  })
  let (neval, ierr) = with_special(q_ear_calcfc, calcfc, () => {
    share_f2cl__install_output()
    @cobyla.bf_cobyla(
      n,
      m,
      x,
      BfCobylaValue(bf_to(rhobeg)),
      BfCobylaValue(bf_to(rhoend)),
      to_int(iprint),
      to_int(maxfun),
      w,
      iact,
      0,
    )
  })
  // Should we put a check here if the number of function evaluations
  // equals maxfun?  When iprint is not 0, the output from COBYLA makes it
  // clear that something bad happened.
  let xl = Collector::new()
  let raw = Collector::new()
  for v in x {
    xl.add(maxima_to(v.0))
    raw.add(v.0)
  }
  let x_list = xl.result()
  // Return the optimum function value, the point that gives the optimum,
  // the value of the constraints, and the number of function evaluations.
  // For convenience.  Only the point and the number of evaluations is
  // really needed.  (The point holds COBYLA's values themselves.)
  make_mlist(
    list([
      cons(
        list1(q_mlist),
        mapcar2(
          (var_, val) => list3(list1(q_mequal), var_, val),
          cdr(vars),
          raw.result(),
        ),
      ),
      apply(fv, x_list),
      Fix(neval.to_int64()),
      Fix(ierr.to_int64()),
    ]),
  )
}

///|
fn init_share_bf__cobyla_interface() -> Unit raise {
  share_f2cl__install_output()
}
