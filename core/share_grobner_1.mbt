// Port of share/contrib/Grobner/grobner.lisp (part 1): monomials,
// monomial orders, priority queues, coefficient rings, terms, polynomials,
// the division algorithm, and the Buchberger / Gebauer-Moeller algorithms.
//
// Representation notes:
// - Monomials are vectors (`Vec`, element type fixnum) of `Fix` exponents.
// - Structures (ring, term, poly, pair, priority-queue) are `make_struct`
//   instances, since they live in Lisp lists and special variables.
// - Monomial orders return two values (greater-p, equal-p). They are stored
//   in `*monomial-order*` etc. as function values; the CL second value is
//   passed through the side channel `share_grobner__mv2` (see
//   `share_grobner__order_fn` / `share_grobner__call_order`).
// - The ring's EZGCD operation returns its three values as a Lisp list.

// ---------------------------------------------------------------------------
// Symbols without generated constants

///|
let share_grobner__q_kw_buchberger : Value = sym(":buchberger")

///|
let share_grobner__q_kw_parallel_buchberger : Value = sym(":parallel-buchberger")

///|
let share_grobner__q_kw_gebauer_moeller : Value = sym(":gebauer_moeller")

///|
let share_grobner__q_sugar : Value = sym("sugar")

///|
let share_grobner__q_kw_sugar : Value = sym(":sugar")

///|
let share_grobner__q_minimal_lcm : Value = sym("minimal-lcm")

///|
let share_grobner__q_kw_minimal_lcm : Value = sym(":minimal-lcm")

///|
let share_grobner__q_minimal_total_degree : Value = sym("minimal-total-degree")

///|
let share_grobner__q_kw_minimal_total_degree : Value = sym(
  ":minimal-total-degree",
)

///|
let share_grobner__q_minimal_length : Value = sym("minimal-length")

///|
let share_grobner__q_kw_minimal_length : Value = sym(":minimal-length")

// ---------------------------------------------------------------------------
// Multiple-value side channel for monomial orders

///|
let share_grobner__mv2 : Ref[Value] = { val: Nil }

///|
/// Wrap a two-valued monomial order as a Lisp function value. The second
/// value is left in `share_grobner__mv2`.
fn share_grobner__order_fn(
  name : String,
  f : (Value, Value, Value?, Value?) -> (Value, Value) raise,
) -> Value {
  lfunc(name, args => {
    let s = if args.length() > 2 { Some(args[2]) } else { None }
    let e = if args.length() > 3 { Some(args[3]) } else { None }
    let (a, b) = f(arg(args, 0), arg(args, 1), s, e)
    share_grobner__mv2.val = b
    a
  })
}

///|
/// `(funcall order ...)` keeping both values.
fn share_grobner__call_order(
  f : Value,
  args : Array[Value],
) -> (Value, Value) raise {
  share_grobner__mv2.val = Nil
  let a = funcall(f, args)
  (a, share_grobner__mv2.val)
}

///|
let share_grobner__lex_fn : Value = share_grobner__order_fn("lex>", (
  p,
  q,
  s,
  e,
) => lex_gt(p, q, start?=s, end?=e))

///|
let share_grobner__grlex_fn : Value = share_grobner__order_fn("grlex>", (
  p,
  q,
  s,
  e,
) => grlex_gt(p, q, start?=s, end?=e))

///|
let share_grobner__grevlex_fn : Value = share_grobner__order_fn(
  "grevlex>",
  (p, q, s, e) => grevlex_gt(p, q, start?=s, end?=e),
)

///|
let share_grobner__invlex_fn : Value = share_grobner__order_fn(
  "invlex>",
  (p, q, s, e) => invlex_gt(p, q, start?=s, end?=e),
)

///|
let share_grobner__elimination_order_1_fn : Value = share_grobner__order_fn(
  "elimination-order-1",
  (p, q, s, e) => elimination_order_1(p, q, start?=s, end?=e),
)

///|
let share_grobner__lt_fn : Value = lfunc("<", args => lbool(
  num_lt(arg(args, 0), arg(args, 1)),
))

///|
let share_grobner__le_fn : Value = lfunc("<=", args => lbool(
  !num_lt(arg(args, 1), arg(args, 0)),
))

///|
let share_grobner__identity_fn : Value = lfunc("identity", args => arg(args, 0))

///|
let share_grobner__sugar_pair_key_fn : Value = lfunc("sugar-pair-key", args => sugar_pair_key(
  arg(args, 0),
  arg(args, 1),
))

///|
let share_grobner__sugar_order_fn : Value = lfunc("sugar-order", args => sugar_order(
  arg(args, 0),
  arg(args, 1),
))

///|
let share_grobner__reverse_monomial_order_fn : Value = lfunc(
  "reverse-monomial-order",
  args => reverse_monomial_order(arg(args, 0), arg(args, 1)),
)

// ---------------------------------------------------------------------------
// Debugging output

///|
/// `(debug-cgb ctl args...)`
fn share_grobner__dbg(ctl : String, args : Array[Value]) -> Unit raise {
  if symval(q_d_poly_grobner_debug).truthy() {
    share_grobner__format_tio(ctl, args)
  }
}

///|
/// `(debug-cgb ctl args...)` with the arguments evaluated only when
/// debugging is on (DEBUG-CGB is a macro).
fn share_grobner__dbgl(
  ctl : String,
  args : () -> Array[Value] raise,
) -> Unit raise {
  if symval(q_d_poly_grobner_debug).truthy() {
    share_grobner__format_tio(ctl, args())
  }
}

///|
/// `(format *terminal-io* ctl args...)`. A leading `~&` is a fresh-line on
/// the stream (the runtime's FORMAT sees only its own output buffer).
fn share_grobner__format_tio(ctl : String, args : Array[Value]) -> Unit raise {
  let s = symval(terminal_io)
  let ctl = if ctl.has_prefix("~&") {
    fresh_line(stream=s) |> ignore
    ctl[2:].to_owned()
  } else {
    ctl
  }
  format(s, ctl, args) |> ignore
}

///|
/// macro `(debug-cgb &rest args)`: ARGS is the list (control-string . args).
fn debug_cgb(args : Value) -> Value raise {
  if symval(q_d_poly_grobner_debug).truthy() {
    let ctl = match car(args) {
      Str(s) => s
      x => princ_to_string(x)
    }
    share_grobner__format_tio(ctl, list_to_array(cdr(args)))
    Nil
  } else {
    Nil
  }
}

///|
/// macro `(grobner-makelist-1 expr var lo hi &optional step)`. The macro
/// evaluates EXPR with VAR bound to lo, lo+step, ..., hi; here EXPR is a
/// function of the iteration value (VAR is unused).
fn grobner_makelist_1(
  expr : Value,
  var_ : Value,
  lo : Value,
  hi : Value,
  step? : Value = Fix(1L),
) -> Value raise {
  ignore(var_)
  let c = Collector::new()
  let mut v = lo
  while !num_lt(hi, v) {
    c.add(funcall(expr, [v]))
    v = num_add(v, step)
  }
  c.result()
}

// ---------------------------------------------------------------------------
// Monomials

///|
fn share_grobner__md(m : Value) -> Array[Value] raise {
  match m {
    Vec(a) => a.data
    _ => raise LispError::SimpleError("The value \{m} is not of type MONOM")
  }
}

///|
fn share_grobner__ex(v : Value) -> Int64 raise {
  match v {
    Fix(n) => n
    _ => raise LispError::SimpleError("The value \{v} is not of type FIXNUM")
  }
}

///|
fn share_grobner__melt(d : Array[Value], i : Int) -> Int64 raise {
  if i < 0 || i >= d.length() {
    raise LispError::SimpleError("Invalid index \{i} for a monomial of length \{d.length()}")
  }
  share_grobner__ex(d[i])
}

///|
fn share_grobner__mk(d : Array[Value]) -> Value {
  Vec({ data: d, dims: [d.length()], fill: None, elt: "fixnum" })
}

///|
/// `(map-into (copy-seq m1) op m1 m2)`
fn share_grobner__mmap2(
  m1 : Value,
  m2 : Value,
  op : (Int64, Int64) -> Int64,
) -> Value raise {
  let d1 = share_grobner__md(m1)
  let d2 = share_grobner__md(m2)
  let r = d1.copy()
  let n = if d1.length() < d2.length() { d1.length() } else { d2.length() }
  for i in 0..<n {
    r[i] = Fix(op(share_grobner__ex(d1[i]), share_grobner__ex(d2[i])))
  }
  share_grobner__mk(r)
}

///|
/// `(every pred m1 m2)` over two exponent vectors.
fn share_grobner__every2(
  m1 : Value,
  m2 : Value,
  pred : (Int64, Int64) -> Bool,
) -> Value raise {
  let d1 = share_grobner__md(m1)
  let d2 = share_grobner__md(m2)
  let n = if d1.length() < d2.length() { d1.length() } else { d2.length() }
  for i in 0..<n {
    if !pred(share_grobner__ex(d1[i]), share_grobner__ex(d2[i])) {
      return Nil
    }
  }
  t
}

///|
/// `(every pred m1 m2 m3 m4)` over exponent vectors (M4 may repeat M3 for
/// the three-argument case).
fn share_grobner__every4(
  m1 : Value,
  m2 : Value,
  m3 : Value,
  m4 : Value,
  pred : (Int64, Int64, Int64, Int64) -> Bool,
) -> Value raise {
  let d1 = share_grobner__md(m1)
  let d2 = share_grobner__md(m2)
  let d3 = share_grobner__md(m3)
  let d4 = share_grobner__md(m4)
  let mut n = d1.length()
  if d2.length() < n {
    n = d2.length()
  }
  if d3.length() < n {
    n = d3.length()
  }
  if d4.length() < n {
    n = d4.length()
  }
  for i in 0..<n {
    if !pred(
        share_grobner__ex(d1[i]),
        share_grobner__ex(d2[i]),
        share_grobner__ex(d3[i]),
        share_grobner__ex(d4[i]),
      ) {
      return Nil
    }
  }
  t
}

///|
fn share_grobner__imax(a : Int64, b : Int64) -> Int64 {
  if a > b {
    a
  } else {
    b
  }
}

///|
fn share_grobner__imin(a : Int64, b : Int64) -> Int64 {
  if a < b {
    a
  } else {
    b
  }
}

///|
/// macro `(make-monom dim &key initial-contents initial-element)`
fn make_monom(
  dim : Value,
  initial_contents? : Value = Nil,
  initial_element? : Value = Fix(0L),
) -> Value raise {
  let n = to_int(dim)
  if initial_contents is Nil {
    share_grobner__mk(Array::make(n, initial_element))
  } else {
    let d = list_to_array(
      match initial_contents {
        Vec(_) => vector_to_list(initial_contents)
        _ => initial_contents
      },
    )
    if d.length() != n {
      raise LispError::SimpleError("make-monom: initial-contents has the wrong length")
    }
    share_grobner__mk(d)
  }
}

///|
/// macro `(monom-elt m index)`
fn monom_elt(m : Value, index : Value) -> Value raise {
  elt(m, to_int(index))
}

///|
fn monom_dimension(m : Value) -> Value raise {
  int(share_grobner__length_seq(m))
}

///|
fn share_grobner__length_seq(m : Value) -> Int raise {
  match m {
    Vec(_) => share_grobner__md(m).length()
    _ => length(m)
  }
}

///|
fn monom_total_degree(
  m : Value,
  start? : Value = Fix(0L),
  end? : Value,
) -> Value raise {
  let d = share_grobner__md(m)
  let e = match end {
    Some(e) => to_int(e)
    None => d.length()
  }
  let mut s = 0L
  for i in to_int(start)..<e {
    s += share_grobner__melt(d, i)
  }
  Fix(s)
}

///|
fn monom_sugar(m : Value) -> Value raise {
  monom_total_degree(m, start=Fix(0L), end=int(share_grobner__md(m).length()))
}

///|
fn monom_div(m1 : Value, m2 : Value) -> Value raise {
  share_grobner__mmap2(m1, m2, (x, y) => x - y)
}

///|
fn monom_mul(m1 : Value, m2 : Value) -> Value raise {
  share_grobner__mmap2(m1, m2, (x, y) => x + y)
}

///|
fn monom_divides_p(m1 : Value, m2 : Value) -> Value raise {
  share_grobner__every2(m1, m2, (x, y) => x <= y)
}

///|
fn monom_divides_monom_lcm_p(m1 : Value, m2 : Value, m3 : Value) -> Value raise {
  share_grobner__every4(m1, m2, m3, m3, (x, y, z, _) => x <=
    share_grobner__imax(y, z))
}

///|
fn monom_lcm_divides_monom_lcm_p(
  m1 : Value,
  m2 : Value,
  m3 : Value,
  m4 : Value,
) -> Value raise {
  share_grobner__every4(m1, m2, m3, m4, (x, y, z, w) => share_grobner__imax(x, y) <=
    share_grobner__imax(z, w))
}

///|
fn monom_lcm_equal_monom_lcm_p(
  m1 : Value,
  m2 : Value,
  m3 : Value,
  m4 : Value,
) -> Value raise {
  share_grobner__every4(m1, m2, m3, m4, (x, y, z, w) => share_grobner__imax(x, y) ==
    share_grobner__imax(z, w))
}

///|
fn monom_divisible_by_p(m1 : Value, m2 : Value) -> Value raise {
  share_grobner__every2(m1, m2, (x, y) => x >= y)
}

///|
fn monom_rel_prime_p(m1 : Value, m2 : Value) -> Value raise {
  share_grobner__every2(m1, m2, (x, y) => share_grobner__imin(x, y) == 0L)
}

///|
fn monom_equal_p(m1 : Value, m2 : Value) -> Value raise {
  share_grobner__every2(m1, m2, (x, y) => x == y)
}

///|
fn monom_lcm(m1 : Value, m2 : Value) -> Value raise {
  share_grobner__mmap2(m1, m2, share_grobner__imax)
}

///|
fn monom_gcd(m1 : Value, m2 : Value) -> Value raise {
  share_grobner__mmap2(m1, m2, share_grobner__imin)
}

///|
fn monom_depends_p(m : Value, k : Value) -> Value raise {
  lbool(share_grobner__melt(share_grobner__md(m), to_int(k)) > 0L)
}

///|
/// macro `(monom-map fun m &rest ml)`
fn monom_map(fun : Value, m : Value, ml : Value) -> Value raise {
  let d = share_grobner__md(m)
  let ds = [d]
  for x in ml.iter() {
    ds.push(share_grobner__md(x))
  }
  let mut n = d.length()
  for x in ds {
    if x.length() < n {
      n = x.length()
    }
  }
  let r = d.copy()
  for i in 0..<n {
    r[i] = funcall(fun, ds.map(x => x[i]))
  }
  share_grobner__mk(r)
}

///|
/// macro `(monom-append m1 m2)`
fn monom_append(m1 : Value, m2 : Value) -> Value raise {
  let r = share_grobner__md(m1).copy()
  for x in share_grobner__md(m2) {
    r.push(x)
  }
  share_grobner__mk(r)
}

///|
/// macro `(monom-contract k m)`
fn monom_contract(k : Value, m : Value) -> Value raise {
  let d = share_grobner__md(m)
  let s = to_int(k)
  if s > d.length() {
    raise LispError::SimpleError("monom-contract: bad start index \{s}")
  }
  share_grobner__mk(d[s:].to_owned())
}

///|
fn monom_exponents(m : Value) -> Value raise {
  list(share_grobner__md(m))
}

// ---------------------------------------------------------------------------
// Monomial orders

///|
/// Pure lexicographic order. Second value: P=Q.
fn lex_gt(
  p : Value,
  q : Value,
  start? : Value = Fix(0L),
  end? : Value,
) -> (Value, Value) raise {
  let pd = share_grobner__md(p)
  let qd = share_grobner__md(q)
  let e = match end {
    Some(e) => to_int(e)
    None => pd.length()
  }
  let mut i = to_int(start)
  while i < e {
    let a = share_grobner__melt(pd, i)
    let b = share_grobner__melt(qd, i)
    if a > b {
      return (t, Nil)
    } else if a < b {
      return (Nil, Nil)
    }
    i += 1
  }
  (Nil, t)
}

///|
/// Total degree order, ties broken by lexicographic.
fn grlex_gt(
  p : Value,
  q : Value,
  start? : Value = Fix(0L),
  end? : Value,
) -> (Value, Value) raise {
  let e = match end {
    Some(e) => e
    None => monom_dimension(p)
  }
  let d1 = share_grobner__ex(monom_total_degree(p, start~, end=e))
  let d2 = share_grobner__ex(monom_total_degree(q, start~, end=e))
  if d1 > d2 {
    (t, Nil)
  } else if d1 < d2 {
    (Nil, Nil)
  } else {
    lex_gt(p, q, start~, end=e)
  }
}

///|
/// Total degree, ties broken by reverse lexicographic.
fn grevlex_gt(
  p : Value,
  q : Value,
  start? : Value = Fix(0L),
  end? : Value,
) -> (Value, Value) raise {
  let e = match end {
    Some(e) => e
    None => monom_dimension(p)
  }
  let d1 = share_grobner__ex(monom_total_degree(p, start~, end=e))
  let d2 = share_grobner__ex(monom_total_degree(q, start~, end=e))
  if d1 > d2 {
    (t, Nil)
  } else if d1 < d2 {
    (Nil, Nil)
  } else {
    revlex_gt(p, q, start~, end=e)
  }
}

///|
/// Reverse lexicographic (not admissible; used to build other orders).
fn revlex_gt(
  p : Value,
  q : Value,
  start? : Value = Fix(0L),
  end? : Value,
) -> (Value, Value) raise {
  let pd = share_grobner__md(p)
  let qd = share_grobner__md(q)
  let e = match end {
    Some(e) => to_int(e)
    None => pd.length()
  }
  let s = to_int(start)
  let mut i = e - 1
  while i >= s {
    let a = share_grobner__melt(pd, i)
    let b = share_grobner__melt(qd, i)
    if a < b {
      return (t, Nil)
    } else if a > b {
      return (Nil, Nil)
    }
    i -= 1
  }
  (Nil, t)
}

///|
/// Inverse lexicographic order.
fn invlex_gt(
  p : Value,
  q : Value,
  start? : Value = Fix(0L),
  end? : Value,
) -> (Value, Value) raise {
  let pd = share_grobner__md(p)
  let qd = share_grobner__md(q)
  let e = match end {
    Some(e) => to_int(e)
    None => pd.length()
  }
  let s = to_int(start)
  let mut i = e - 1
  while i >= s {
    let a = share_grobner__melt(pd, i)
    let b = share_grobner__melt(qd, i)
    if a > b {
      return (t, Nil)
    } else if a < b {
      return (Nil, Nil)
    }
    i -= 1
  }
  (Nil, t)
}

///|
/// macro `(monomial-order x y)`: primary value of `*monomial-order*`.
fn monomial_order(x : Value, y : Value) -> Value raise {
  funcall(symval(q_ear_monomial_order), [x, y])
}

///|
/// `(monomial-order x y)` with both values.
fn share_grobner__morder(x : Value, y : Value) -> (Value, Value) raise {
  share_grobner__call_order(symval(q_ear_monomial_order), [x, y])
}

///|
fn reverse_monomial_order(x : Value, y : Value) -> Value raise {
  monomial_order(y, x)
}

///|
/// The K-th elimination order, built from `*primary-elimination-order*`
/// (first K variables) and `*secondary-elimination-order*` (the rest).
fn elimination_order(k : Value) -> Value raise {
  share_grobner__order_fn("elimination-order", fn(p, q, s, e) raise {
    let start = match s {
      Some(v) => v
      None => Fix(0L)
    }
    let end = match e {
      Some(v) => v
      None => monom_dimension(p)
    }
    let (primary, equal) = share_grobner__call_order(
      symval(q_ear_primary_elimination_order),
      [p, q, start, k],
    )
    if equal.truthy() {
      share_grobner__call_order(symval(q_ear_secondary_elimination_order), [
        p,
        q,
        k,
        end,
      ])
    } else {
      (primary, Nil)
    }
  })
}

///|
/// Equivalent to the function returned by `(elimination-order 1)`.
fn elimination_order_1(
  p : Value,
  q : Value,
  start? : Value = Fix(0L),
  end? : Value,
) -> (Value, Value) raise {
  let e = match end {
    Some(e) => e
    None => monom_dimension(p)
  }
  let s = to_int(start)
  let a = share_grobner__melt(share_grobner__md(p), s)
  let b = share_grobner__melt(share_grobner__md(q), s)
  if a > b {
    (t, Nil)
  } else if a < b {
    (Nil, Nil)
  } else {
    share_grobner__call_order(symval(q_ear_secondary_elimination_order), [
      p,
      q,
      int(s + 1),
      e,
    ])
  }
}

// ---------------------------------------------------------------------------
// Priority queues

///|
fn priority_queue_make_heap(element_type? : Value = q_fixnum) -> Value raise {
  let elt = if eq(element_type, q_fixnum) { "fixnum" } else { "t" }
  make_array(
    [to_int(symval(q_ear_priority_queue_allocation_size))],
    elt~,
    fill=1,
  )
}

///|
fn share_grobner__pq_heap(pq : Value) -> Value raise {
  struct_ref(pq, 0)
}

///|
fn share_grobner__pq_test(pq : Value) -> Value raise {
  struct_ref(pq, 1)
}

///|
fn make_priority_queue(
  element_type? : Value = q_fixnum,
  test_? : Value,
  element_key? : Value,
) -> Value raise {
  let tst = match test_ {
    Some(f) => f
    None => share_grobner__le_fn
  }
  let key = match element_key {
    Some(f) => f
    None => share_grobner__identity_fn
  }
  make_struct("priority-queue", [
    priority_queue_make_heap(element_type~),
    lfunc("priority-queue-test", args => funcall(tst, [
      funcall(key, [arg(args, 1)]),
      funcall(key, [arg(args, 0)]),
    ])),
  ])
}

///|
fn priority_queue_insert(pq : Value, item : Value) -> Value raise {
  priority_queue_heap_insert(
    share_grobner__pq_heap(pq),
    item,
    test_=share_grobner__pq_test(pq),
  )
}

///|
fn priority_queue_remove(pq : Value) -> Value raise {
  priority_queue_heap_remove(
    share_grobner__pq_heap(pq),
    test_=share_grobner__pq_test(pq),
  ).0
}

///|
fn priority_queue_empty_p(pq : Value) -> Value raise {
  priority_queue_heap_empty_p(share_grobner__pq_heap(pq))
}

///|
fn priority_queue_size(pq : Value) -> Value raise {
  int(fill_pointer(share_grobner__pq_heap(pq)))
}

///|
fn priority_queue_upheap(a : Value, k : Value, test_? : Value) -> Value raise {
  let tst = match test_ {
    Some(f) => f
    None => share_grobner__le_fn
  }
  let mut k = to_int(k)
  let v = aref1(a, k)
  if !(0 < k && k < fill_pointer(a)) {
    raise LispError::SimpleError("The assertion (< 0 K (FILL-POINTER A)) failed.")
  }
  while true {
    let parent = k >> 1
    if parent == 0 {
      break
    }
    if !funcall(tst, [aref1(a, parent), v]).truthy() {
      break
    }
    aset1(a, k, aref1(a, parent)) |> ignore
    k = parent
  }
  aset1(a, k, v) |> ignore
  a
}

///|
fn priority_queue_heap_insert(
  a : Value,
  item : Value,
  test_? : Value,
) -> Value raise {
  vector_push_extend(item, a) |> ignore
  priority_queue_upheap(a, int(fill_pointer(a) - 1), test_?)
}

///|
fn priority_queue_downheap(a : Value, k : Value, test_? : Value) -> Value raise {
  let tst = match test_ {
    Some(f) => f
    None => share_grobner__le_fn
  }
  let mut k = to_int(k)
  let v = aref1(a, k)
  let n = fill_pointer(a)
  while true {
    if !(k <= n >> 1) {
      break
    }
    let mut j = k << 1
    if j < n && !funcall(tst, [aref1(a, j + 1), aref1(a, j)]).truthy() {
      j += 1
    }
    if funcall(tst, [aref1(a, j), v]).truthy() {
      break
    }
    aset1(a, k, aref1(a, j)) |> ignore
    k = j
  }
  aset1(a, k, v) |> ignore
  a
}

///|
fn priority_queue_heap_remove(a : Value, test_? : Value) -> (Value, Value) raise {
  let v = aref1(a, 1)
  if fill_pointer(a) <= 1 {
    raise LispError::SimpleError("Empty queue.")
  }
  aset1(a, 1, vector_pop(a)) |> ignore
  priority_queue_downheap(a, Fix(1L), test_?) |> ignore
  (v, a)
}

///|
fn priority_queue_heap_empty_p(a : Value) -> Value raise {
  lbool(fill_pointer(a) <= 1)
}

// ---------------------------------------------------------------------------
// Coefficient rings: struct slots parse unit zerop add sub uminus mul div
// lcm ezgcd gcd.

///|
fn share_grobner__make_ring(fns : Array[Value]) -> Value {
  make_struct("ring", fns)
}

///|
fn share_grobner__rparse(ring : Value, x : Value) -> Value raise {
  funcall(struct_ref(ring, 0), [x])
}

///|
fn share_grobner__runit(ring : Value) -> Value raise {
  funcall(struct_ref(ring, 1), [])
}

///|
fn share_grobner__rzerop(ring : Value, x : Value) -> Bool raise {
  funcall(struct_ref(ring, 2), [x]).truthy()
}

///|
fn share_grobner__radd(ring : Value, x : Value, y : Value) -> Value raise {
  funcall(struct_ref(ring, 3), [x, y])
}

///|
fn share_grobner__rsub(ring : Value, x : Value, y : Value) -> Value raise {
  funcall(struct_ref(ring, 4), [x, y])
}

///|
fn share_grobner__ruminus(ring : Value, x : Value) -> Value raise {
  funcall(struct_ref(ring, 5), [x])
}

///|
fn share_grobner__rmul(ring : Value, x : Value, y : Value) -> Value raise {
  funcall(struct_ref(ring, 6), [x, y])
}

///|
fn share_grobner__rdiv(ring : Value, x : Value, y : Value) -> Value raise {
  funcall(struct_ref(ring, 7), [x, y])
}

///|
fn share_grobner__rlcm(ring : Value, x : Value, y : Value) -> Value raise {
  funcall(struct_ref(ring, 8), [x, y])
}

///|
/// The three values (gcd x/gcd y/gcd) of the ring's EZGCD.
fn share_grobner__rezgcd(
  ring : Value,
  x : Value,
  y : Value,
) -> (Value, Value, Value) raise {
  let l = funcall(struct_ref(ring, 9), [x, y])
  (car(l), cadr(l), caddr(l))
}

///|
fn share_grobner__rgcd(ring : Value) -> Value raise {
  struct_ref(ring, 10)
}

///|
/// `*ring-of-integers*`
fn share_grobner__ring_of_integers() -> Value {
  share_grobner__make_ring([
    share_grobner__identity_fn,
    lfunc("unit", _ => Fix(1L)),
    lfunc("zerop", args => lbool(zerop(arg(args, 0)))),
    lfunc("+", args => num_add(arg(args, 0), arg(args, 1))),
    lfunc("-", args => if args.length() == 1 {
      num_neg(arg(args, 0))
    } else {
      num_sub(arg(args, 0), arg(args, 1))
    }),
    lfunc("-", args => if args.length() == 1 {
      num_neg(arg(args, 0))
    } else {
      num_sub(arg(args, 0), arg(args, 1))
    }),
    lfunc("*", args => num_mul(arg(args, 0), arg(args, 1))),
    lfunc("/", args => num_div(arg(args, 0), arg(args, 1))),
    lfunc("lcm", args => num_lcm(arg(args, 0), arg(args, 1))),
    lfunc("ezgcd", args => {
      let x = arg(args, 0)
      let y = arg(args, 1)
      let c = num_gcd(x, y)
      list([c, num_div(x, c), num_div(y, c)])
    }),
    lfunc("gcd", args => num_gcd(arg(args, 0), arg(args, 1))),
  ])
}

///|
/// `*expression-ring*`: Maxima general expressions as coefficients.
fn share_grobner__expression_ring() -> Value {
  share_grobner__make_ring([
    lfunc("parse", args => {
      let mut expr = arg(args, 0)
      if symval(q_modulus).truthy() {
        expr = d_rat(expr, Nil)
      }
      expr
    }),
    lfunc("unit", _ => if symval(q_modulus).truthy() {
      d_rat(Fix(1L), Nil)
    } else {
      Fix(1L)
    }),
    lfunc("zerop", args => {
      let expr = arg(args, 0)
      // When is exactly a maxima expression equal to 0?
      if numberp(expr) {
        lbool(num_eq(expr, Fix(0L)))
      } else if atom(expr) {
        Nil
      } else if eq(caar(expr), q_mrat) {
        lbool(eql(d_ratdisrep(expr), Fix(0L)))
      } else {
        lbool(eql(sratsimp(expr), Fix(0L)))
      }
    }),
    lfunc("add", args => sratsimp(m_plus(list([arg(args, 0), arg(args, 1)])))),
    lfunc("sub", args => sratsimp(m_(arg(args, 0), a2=arg(args, 1)))),
    lfunc("uminus", args => m_(arg(args, 0))),
    lfunc("mul", args => m_star(list([arg(args, 0), arg(args, 1)]))),
    lfunc("div", args => sratsimp(m_sl_sl(arg(args, 0), a2=arg(args, 1)))),
    lfunc("lcm", args => {
      let x = arg(args, 0)
      let y = arg(args, 1)
      sratsimp(
        m_sl_sl(m_star(list([x, y])), a2=second(d_ezgcd(list([x, y])))),
      )
    }),
    lfunc("ezgcd", args => cdr(d_ezgcd(list([arg(args, 0), arg(args, 1)])))),
    lfunc("gcd", args => second(d_ezgcd(list([arg(args, 0), arg(args, 1)])))),
  ])
}

// ---------------------------------------------------------------------------
// Terms: struct slots monom coeff.

///|
fn share_grobner__make_term(monom : Value, coeff : Value) -> Value {
  make_struct("term", [monom, coeff])
}

///|
fn share_grobner__term_monom(x : Value) -> Value raise {
  struct_ref(x, 0)
}

///|
fn share_grobner__term_coeff(x : Value) -> Value raise {
  struct_ref(x, 1)
}

///|
fn make_term_variable(
  ring : Value,
  nvars : Value,
  pos : Value,
  power? : Value = Fix(1L),
  coeff? : Value,
) -> Value raise {
  let coeff = match coeff {
    Some(c) => c
    None => share_grobner__runit(ring)
  }
  let monom = make_monom(nvars, initial_element=Fix(0L))
  let d = share_grobner__md(monom)
  let i = to_int(pos)
  d[i] = Fix(share_grobner__melt(d, i) + share_grobner__ex(power))
  share_grobner__make_term(monom, coeff)
}

///|
fn term_sugar(term : Value) -> Value raise {
  monom_sugar(share_grobner__term_monom(term))
}

///|
fn termlist_sugar(p : Value) -> Value raise {
  let mut sugar = -1L
  for term in p.iter() {
    sugar = share_grobner__imax(sugar, share_grobner__ex(term_sugar(term)))
  }
  Fix(sugar)
}

// ---------------------------------------------------------------------------
// Low-level polynomial arithmetic on lists of terms

///|
/// macro `(termlist-lt p)`
fn termlist_lt(p : Value) -> Value raise {
  car(p)
}

///|
fn termlist_lm(p : Value) -> Value raise {
  share_grobner__term_monom(termlist_lt(p))
}

///|
fn termlist_lc(p : Value) -> Value raise {
  share_grobner__term_coeff(termlist_lt(p))
}

///|
/// Multiply scalar C by a polynomial P (works with divisors of 0).
fn scalar_times_termlist(ring : Value, c : Value, p : Value) -> Value raise {
  mapcan(
    term => {
      let c1 = share_grobner__rmul(ring, c, share_grobner__term_coeff(term))
      if share_grobner__rzerop(ring, c1) {
        Nil
      } else {
        list1(share_grobner__make_term(share_grobner__term_monom(term), c1))
      }
    },
    p,
  )
}

///|
/// (LIST TERM) where TERM = TERM1*TERM2, or NIL when the product is 0.
fn term_mul(ring : Value, term1 : Value, term2 : Value) -> Value raise {
  let c = share_grobner__rmul(
    ring,
    share_grobner__term_coeff(term1),
    share_grobner__term_coeff(term2),
  )
  if share_grobner__rzerop(ring, c) {
    Nil
  } else {
    list1(
      share_grobner__make_term(
        monom_mul(
          share_grobner__term_monom(term1),
          share_grobner__term_monom(term2),
        ),
        c,
      ),
    )
  }
}

///|
fn term_times_termlist(ring : Value, term : Value, f : Value) -> Value raise {
  mapcan(term_f => term_mul(ring, term, term_f), f)
}

///|
fn termlist_times_term(ring : Value, f : Value, term : Value) -> Value raise {
  mapcan(term_f => term_mul(ring, term_f, term), f)
}

///|
fn monom_times_term(m : Value, term : Value) -> Value raise {
  share_grobner__make_term(
    monom_mul(m, share_grobner__term_monom(term)),
    share_grobner__term_coeff(term),
  )
}

///|
fn monom_times_termlist(m : Value, f : Value) -> Value raise {
  if f is Nil {
    Nil
  } else {
    mapcar(x => monom_times_term(m, x), f)
  }
}

///|
fn termlist_uminus(ring : Value, f : Value) -> Value raise {
  mapcar(
    x => share_grobner__make_term(
      share_grobner__term_monom(x),
      share_grobner__ruminus(ring, share_grobner__term_coeff(x)),
    ),
    f,
  )
}

///|
fn termlist_add(ring : Value, p : Value, q : Value) -> Value raise {
  let mut p = p
  let mut q = q
  let mut r : Value = Nil
  while true {
    if p is Nil {
      return revappend(r, q)
    }
    if q is Nil {
      return revappend(r, p)
    }
    let (lm_greater, lm_equal) = share_grobner__morder(
      termlist_lm(p),
      termlist_lm(q),
    )
    if lm_equal.truthy() {
      let s = share_grobner__radd(ring, termlist_lc(p), termlist_lc(q))
      if !share_grobner__rzerop(ring, s) { // check for cancellation
        r = cons(share_grobner__make_term(termlist_lm(p), s), r)
      }
      p = cdr(p)
      q = cdr(q)
    } else if lm_greater.truthy() {
      r = cons(car(p), r)
      p = cdr(p)
    } else {
      r = cons(car(q), r)
      q = cdr(q)
    }
  }
  r
}

///|
fn termlist_sub(ring : Value, p : Value, q : Value) -> Value raise {
  let mut p = p
  let mut q = q
  let mut r : Value = Nil
  while true {
    if p is Nil {
      return revappend(r, termlist_uminus(ring, q))
    }
    if q is Nil {
      return revappend(r, p)
    }
    let (mgreater, mequal) = share_grobner__morder(
      termlist_lm(p),
      termlist_lm(q),
    )
    if mequal.truthy() {
      let s = share_grobner__rsub(ring, termlist_lc(p), termlist_lc(q))
      if !share_grobner__rzerop(ring, s) { // check for cancellation
        r = cons(share_grobner__make_term(termlist_lm(p), s), r)
      }
      p = cdr(p)
      q = cdr(q)
    } else if mgreater.truthy() {
      r = cons(car(p), r)
      p = cdr(p)
    } else {
      r = cons(
        share_grobner__make_term(
          termlist_lm(q),
          share_grobner__ruminus(ring, termlist_lc(q)),
        ),
        r,
      )
      q = cdr(q)
    }
  }
  r
}

///|
/// Multiplication of polynomials (non-destructive). If p=p0+p1 and
/// q=q0+q1 then pq=p0q0+p0q1+p1q.
fn termlist_mul(ring : Value, p : Value, q : Value) -> Value raise {
  if p is Nil || q is Nil {
    Nil
  } else if cdr(p) is Nil {
    term_times_termlist(ring, car(p), q)
  } else if cdr(q) is Nil {
    termlist_times_term(ring, p, car(q))
  } else {
    let head = term_mul(ring, termlist_lt(p), termlist_lt(q))
    let tail = termlist_add(
      ring,
      term_times_termlist(ring, car(p), cdr(q)),
      termlist_mul(ring, cdr(p), q),
    )
    if head is Nil {
      tail
    } else if tail is Nil {
      head
    } else {
      nconc(head, tail)
    }
  }
}

///|
fn termlist_unit(ring : Value, dimension : Value) -> Value raise {
  list1(
    share_grobner__make_term(
      make_monom(dimension, initial_element=Fix(0L)),
      share_grobner__runit(ring),
    ),
  )
}

///|
fn termlist_expt(ring : Value, poly : Value, n : Value) -> Value raise {
  let dim = monom_dimension(termlist_lm(poly))
  if minusp(n) {
    raise LispError::SimpleError("termlist-expt: Negative exponent.")
  }
  if poly is Nil {
    return if zerop(n) { termlist_unit(ring, dim) } else { Nil }
  }
  let n = share_grobner__ex(n)
  let mut k = 1L
  let mut q = poly
  let mut p = termlist_unit(ring, dim)
  while !(k > n) {
    let k1 = k << 1
    let q1 = termlist_mul(ring, q, q) // keep squaring
    let p1 = if (k & n) != 0L { termlist_mul(ring, p, q) } else { p }
    k = k1
    q = q1
    p = p1
  }
  p
}

///|
/// Eliminate first K variables from a polynomial P.
fn termlist_contract(p : Value, k? : Value = Fix(1L)) -> Value raise {
  mapcar(
    term => share_grobner__make_term(
      monom_contract(k, share_grobner__term_monom(term)),
      share_grobner__term_coeff(term),
    ),
    p,
  )
}

///|
/// Insert the powers M at the beginning of every monomial of P.
fn termlist_extend(p : Value, m? : Value) -> Value raise {
  let m = match m {
    Some(m) => m
    None => make_monom(Fix(1L), initial_element=Fix(0L))
  }
  mapcar(
    term => share_grobner__make_term(
      monom_append(m, share_grobner__term_monom(term)),
      share_grobner__term_coeff(term),
    ),
    p,
  )
}

///|
/// Add N variables to P by inserting zero powers in front of each monomial.
fn termlist_add_variables(p : Value, n : Value) -> Value raise {
  mapcar(
    term => share_grobner__make_term(
      monom_append(
        make_monom(n, initial_element=Fix(0L)),
        share_grobner__term_monom(term),
      ),
      share_grobner__term_coeff(term),
    ),
    p,
  )
}

// ---------------------------------------------------------------------------
// Polynomials: struct slots termlist sugar.

///|
let share_grobner__poly_counter : Ref[Int64] = { val: 0L }

///|
/// A POLY structure: slots termlist, sugar, and (port only) a serial
/// number identifying the instance, used for the identity-keyed table of
/// treated critical pairs.
fn share_grobner__new_poly(termlist : Value, sugar : Value) -> Value {
  share_grobner__poly_counter.val += 1L
  make_struct("poly", [termlist, sugar, Fix(share_grobner__poly_counter.val)])
}

///|
fn share_grobner__make_poly_from_termlist(
  termlist : Value,
  sugar? : Value,
) -> Value raise {
  let sugar = match sugar {
    Some(s) => s
    None => termlist_sugar(termlist)
  }
  share_grobner__new_poly(termlist, sugar)
}

///|
fn share_grobner__make_poly_zero() -> Value {
  share_grobner__new_poly(Nil, Fix(-1L))
}

///|
fn share_grobner__make_variable(
  ring : Value,
  nvars : Value,
  pos : Value,
  power? : Value = Fix(1L),
) -> Value raise {
  let termlist = list1(make_term_variable(ring, nvars, pos, power~))
  share_grobner__new_poly(termlist, power)
}

///|
fn share_grobner__poly_unit(ring : Value, dimension : Value) -> Value raise {
  share_grobner__new_poly(termlist_unit(ring, dimension), Fix(0L))
}

///|
fn share_grobner__poly_termlist(p : Value) -> Value raise {
  struct_ref(p, 0)
}

///|
fn share_grobner__set_poly_termlist(p : Value, v : Value) -> Value raise {
  struct_set(p, 0, v)
}

///|
fn share_grobner__poly_sugar(p : Value) -> Value raise {
  struct_ref(p, 1)
}

///|
fn share_grobner__set_poly_sugar(p : Value, v : Value) -> Value raise {
  struct_set(p, 1, v)
}

///|
fn share_grobner__isugar(p : Value) -> Int64 raise {
  share_grobner__ex(share_grobner__poly_sugar(p))
}

///|
/// macro: leading term
fn poly_lt(p : Value) -> Value raise {
  car(share_grobner__poly_termlist(p))
}

///|
/// macro: second term `(cadar (poly-termlist p))`
fn poly_second_lt(p : Value) -> Value raise {
  cadar(share_grobner__poly_termlist(p))
}

///|
fn poly_lm(p : Value) -> Value raise {
  share_grobner__term_monom(poly_lt(p))
}

///|
fn poly_second_lm(p : Value) -> Value raise {
  share_grobner__term_monom(poly_second_lt(p))
}

///|
fn poly_lc(p : Value) -> Value raise {
  share_grobner__term_coeff(poly_lt(p))
}

///|
fn poly_second_lc(p : Value) -> Value raise {
  share_grobner__term_coeff(poly_second_lt(p))
}

///|
fn poly_zerop(p : Value) -> Value raise {
  lbool(share_grobner__poly_termlist(p) is Nil)
}

///|
fn share_grobner__zerop(p : Value) -> Bool raise {
  share_grobner__poly_termlist(p) is Nil
}

///|
fn poly_length(p : Value) -> Value raise {
  int(length(share_grobner__poly_termlist(p)))
}

///|
fn scalar_times_poly(ring : Value, c : Value, p : Value) -> Value raise {
  share_grobner__make_poly_from_termlist(
    scalar_times_termlist(ring, c, share_grobner__poly_termlist(p)),
    sugar=share_grobner__poly_sugar(p),
  )
}

///|
fn monom_times_poly(m : Value, p : Value) -> Value raise {
  share_grobner__make_poly_from_termlist(
    monom_times_termlist(m, share_grobner__poly_termlist(p)),
    sugar=Fix(share_grobner__isugar(p) + share_grobner__ex(monom_sugar(m))),
  )
}

///|
fn term_times_poly(ring : Value, term : Value, p : Value) -> Value raise {
  share_grobner__make_poly_from_termlist(
    term_times_termlist(ring, term, share_grobner__poly_termlist(p)),
    sugar=Fix(share_grobner__isugar(p) + share_grobner__ex(term_sugar(term))),
  )
}

///|
fn poly_add(ring : Value, p : Value, q : Value) -> Value raise {
  share_grobner__make_poly_from_termlist(
    termlist_add(
      ring,
      share_grobner__poly_termlist(p),
      share_grobner__poly_termlist(q),
    ),
    sugar=Fix(
      share_grobner__imax(share_grobner__isugar(p), share_grobner__isugar(q)),
    ),
  )
}

///|
fn poly_sub(ring : Value, p : Value, q : Value) -> Value raise {
  share_grobner__make_poly_from_termlist(
    termlist_sub(
      ring,
      share_grobner__poly_termlist(p),
      share_grobner__poly_termlist(q),
    ),
    sugar=Fix(
      share_grobner__imax(share_grobner__isugar(p), share_grobner__isugar(q)),
    ),
  )
}

///|
fn poly_uminus(ring : Value, p : Value) -> Value raise {
  share_grobner__make_poly_from_termlist(
    termlist_uminus(ring, share_grobner__poly_termlist(p)),
    sugar=share_grobner__poly_sugar(p),
  )
}

///|
fn poly_mul(ring : Value, p : Value, q : Value) -> Value raise {
  share_grobner__make_poly_from_termlist(
    termlist_mul(
      ring,
      share_grobner__poly_termlist(p),
      share_grobner__poly_termlist(q),
    ),
    sugar=Fix(share_grobner__isugar(p) + share_grobner__isugar(q)),
  )
}

///|
fn poly_expt(ring : Value, p : Value, n : Value) -> Value raise {
  share_grobner__make_poly_from_termlist(
    termlist_expt(ring, share_grobner__poly_termlist(p), n),
    sugar=num_mul(n, share_grobner__poly_sugar(p)),
  )
}

///|
fn poly_append(plist : Value) -> Value raise {
  let tls = mapcar(share_grobner__poly_termlist, plist)
  let mut all : Value = Nil
  for x in reverse(tls).iter() {
    all = append(x, all)
  }
  let sugars = list_to_array(mapcar(share_grobner__poly_sugar, plist))
  if sugars.length() == 0 {
    raise LispError::SimpleError("invalid number of arguments: 0")
  }
  let mut m = sugars[0]
  for s in sugars {
    m = num_max(m, s)
  }
  share_grobner__make_poly_from_termlist(all, sugar=m)
}

///|
fn poly_nreverse(p : Value) -> Value raise {
  share_grobner__set_poly_termlist(
    p,
    nreverse(share_grobner__poly_termlist(p)),
  )
  |> ignore
  p
}

///|
fn poly_contract(p : Value, k? : Value = Fix(1L)) -> Value raise {
  share_grobner__make_poly_from_termlist(
    termlist_contract(share_grobner__poly_termlist(p), k~),
    sugar=share_grobner__poly_sugar(p),
  )
}

///|
fn poly_extend(p : Value, m? : Value) -> Value raise {
  let m = match m {
    Some(m) => m
    None => make_monom(Fix(1L), initial_element=Fix(0L))
  }
  share_grobner__make_poly_from_termlist(
    termlist_extend(share_grobner__poly_termlist(p), m~),
    sugar=Fix(share_grobner__isugar(p) + share_grobner__ex(monom_sugar(m))),
  )
}

///|
fn poly_add_variables(p : Value, k : Value) -> Value raise {
  share_grobner__set_poly_termlist(
    p,
    termlist_add_variables(share_grobner__poly_termlist(p), k),
  )
  |> ignore
  p
}

///|
fn poly_list_add_variables(plist : Value, k : Value) -> Value raise {
  mapcar(p => poly_add_variables(p, k), plist)
}

///|
/// Calculate [U1*P1,U2*P2,...,UK*PK], where PLIST=[P1,P2,...,PK].
fn poly_standard_extension(plist : Value) -> Value raise {
  let k = length(plist)
  let plist = poly_list_add_variables(plist, int(k))
  for i in 0..<k {
    let g = nth(i, plist)
    for x in share_grobner__poly_termlist(g).iter() {
      let d = share_grobner__md(share_grobner__term_monom(x))
      d[i] = Fix(share_grobner__melt(d, i) + 1L)
    }
    share_grobner__set_poly_sugar(g, Fix(share_grobner__isugar(g) + 1L))
    |> ignore
  }
  plist
}

///|
/// Calculate [F, U1*P1-1,U2*P2-1,...,UK*PK-1], where PLIST=[P1,P2,...,PK].
fn saturation_extension(ring : Value, f : Value, plist : Value) -> Value raise {
  let k = length(plist)
  let d = monom_dimension(poly_lm(car(plist)))
  let f = poly_list_add_variables(f, int(k))
  let plist = mapcar(
    x => {
      share_grobner__set_poly_termlist(
        x,
        nconc(
          share_grobner__poly_termlist(x),
          list1(
            share_grobner__make_term(
              make_monom(d, initial_element=Fix(0L)),
              share_grobner__ruminus(ring, share_grobner__runit(ring)),
            ),
          ),
        ),
      )
      |> ignore
      x
    },
    poly_standard_extension(plist),
  )
  append(f, plist)
}

///|
/// Calculate [F, U1*P1+U2*P2+...+UK*PK-1], where PLIST=[P1,P2,...,PK].
fn polysaturation_extension(
  ring : Value,
  f : Value,
  plist : Value,
) -> Value raise {
  let k = length(plist)
  let d = k + share_grobner__length_seq(poly_lm(car(plist)))
  let f = poly_list_add_variables(f, int(k))
  let plist = poly_append(poly_standard_extension(plist))
  setf_cdr(
    last(share_grobner__poly_termlist(plist)),
    list1(
      share_grobner__make_term(
        make_monom(int(d), initial_element=Fix(0L)),
        share_grobner__ruminus(ring, share_grobner__runit(ring)),
      ),
    ),
  )
  |> ignore
  append(f, list1(plist))
}

///|
fn saturation_extension_1(ring : Value, f : Value, p : Value) -> Value raise {
  polysaturation_extension(ring, f, list1(p))
}

// ---------------------------------------------------------------------------
// Evaluation of polynomial (prefix) expressions

///|
/// Coerce an element of the coefficient ring to a constant polynomial.
fn coerce_coeff(ring : Value, expr : Value, vars : Value) -> Value raise {
  share_grobner__make_poly_from_termlist(
    list1(
      share_grobner__make_term(
        make_monom(int(length(vars)), initial_element=Fix(0L)),
        share_grobner__rparse(ring, expr),
      ),
    ),
    sugar=Fix(0L),
  )
}

///|
fn share_grobner__position_equalp(x : Value, l : Value) -> Int {
  let mut i = 0
  for y in l.iter() {
    if equalp(x, y) {
      return i
    }
    i += 1
  }
  -1
}

///|
fn share_grobner__reduce(
  f : (Value, Value) -> Value raise,
  l : Value,
) -> Value raise {
  match l {
    Nil => raise LispError::SimpleError("reduce: empty sequence with no initial value")
    _ => {
      let mut acc = car(l)
      for x in cdr(l).iter() {
        acc = f(acc, x)
      }
      acc
    }
  }
}

///|
fn poly_eval(
  ring : Value,
  expr : Value,
  vars : Value,
  list_marker? : Value = q_op_lb,
) -> Value raise {
  let p_eval = fn(a : Value) -> Value raise { poly_eval(ring, a, vars) }
  let p_eval_list = fn(args : Value) -> Value raise { mapcar(p_eval, args) }
  let p_add = fn(x : Value, y : Value) -> Value raise { poly_add(ring, x, y) }
  if eql(expr, Fix(0L)) {
    share_grobner__make_poly_zero()
  } else if share_grobner__position_equalp(expr, vars) >= 0 {
    let pos = share_grobner__position_equalp(expr, vars)
    share_grobner__make_variable(ring, int(length(vars)), int(pos))
  } else if atom(expr) {
    coerce_coeff(ring, expr, vars)
  } else if eq(car(expr), list_marker) {
    cons(list_marker, p_eval_list(cdr(expr)))
  } else {
    let op = car(expr)
    if eq(op, q_op_plus) {
      share_grobner__reduce(p_add, p_eval_list(cdr(expr)))
    } else if eq(op, q_op_) {
      match length(expr) {
        1 => share_grobner__make_poly_zero()
        2 => poly_uminus(ring, p_eval(cadr(expr)))
        3 => poly_sub(ring, p_eval(cadr(expr)), p_eval(caddr(expr)))
        _ =>
          poly_sub(
            ring,
            p_eval(cadr(expr)),
            share_grobner__reduce(p_add, p_eval_list(cddr(expr))),
          )
      }
    } else if eq(op, q_op_star) {
      if cddr(expr) is Nil { // unary
        p_eval(cdr(expr))
      } else {
        share_grobner__reduce(
          (p, q) => poly_mul(ring, p, q),
          p_eval_list(cdr(expr)),
        )
      }
    } else if eq(op, q_expt) {
      if share_grobner__position_equalp(cadr(expr), vars) >= 0 {
        // Special handling of (expt var pow)
        let pos = share_grobner__position_equalp(cadr(expr), vars)
        share_grobner__make_variable(
          ring,
          int(length(vars)),
          int(pos),
          power=caddr(expr),
        )
      } else if !(integerp(caddr(expr)) && plusp(caddr(expr))) {
        // Negative power means division in coefficient ring
        // Non-integer power means non-polynomial coefficient
        coerce_coeff(ring, expr, vars)
      } else {
        poly_expt(ring, p_eval(cadr(expr)), caddr(expr))
      }
    } else {
      coerce_coeff(ring, expr, vars)
    }
  }
}

// ---------------------------------------------------------------------------
// Grobner basis: S-polynomials, primitive parts

///|
/// The S-polynomial of polynomials F and G.
fn spoly(ring : Value, f : Value, g : Value) -> Value raise {
  let lcm = monom_lcm(poly_lm(f), poly_lm(g))
  let mf = monom_div(lcm, poly_lm(f))
  let mg = monom_div(lcm, poly_lm(g))
  let (_, cf, cg) = share_grobner__rezgcd(ring, poly_lc(f), poly_lc(g))
  poly_sub(
    ring,
    scalar_times_poly(ring, cg, monom_times_poly(mf, f)),
    scalar_times_poly(ring, cf, monom_times_poly(mg, g)),
  )
}

///|
/// Divide P by the gcd of its coefficients; second value the gcd.
fn poly_primitive_part(ring : Value, p : Value) -> (Value, Value) raise {
  if share_grobner__zerop(p) {
    (p, Fix(1L))
  } else {
    let c = poly_content(ring, p)
    (
      share_grobner__make_poly_from_termlist(
        mapcar(
          x => share_grobner__make_term(
            share_grobner__term_monom(x),
            share_grobner__rdiv(ring, share_grobner__term_coeff(x), c),
          ),
          share_grobner__poly_termlist(p),
        ),
        sugar=share_grobner__poly_sugar(p),
      ),
      c,
    )
  }
}

///|
/// Greatest common divisor of the coefficients of P.
fn poly_content(ring : Value, p : Value) -> Value raise {
  let gcd = share_grobner__rgcd(ring)
  let mut acc = poly_lc(p)
  for term in cdr(share_grobner__poly_termlist(p)).iter() {
    acc = funcall(gcd, [acc, share_grobner__term_coeff(term)])
  }
  acc
}

// ---------------------------------------------------------------------------
// The division algorithm

///|
/// C2*F-C1*M*G, where F and G are polynomials and M is a monomial; the
/// leading terms are assumed to cancel.
fn grobner_op(
  ring : Value,
  c1 : Value,
  c2 : Value,
  m : Value,
  f : Value,
  g : Value,
) -> Value raise {
  poly_sub(
    ring,
    scalar_times_poly(ring, c2, f),
    scalar_times_poly(ring, c1, monom_times_poly(m, g)),
  )
}

///|
/// Move lt(p) to the remainder r (both mutated).
fn share_grobner__move_lt(p : Value, r : Value) -> Unit raise {
  share_grobner__set_poly_termlist(
    r,
    cons(poly_lt(p), share_grobner__poly_termlist(r)),
  )
  |> ignore
  share_grobner__set_poly_sugar(
    r,
    Fix(
      share_grobner__imax(
        share_grobner__isugar(r),
        share_grobner__ex(term_sugar(poly_lt(p))),
      ),
    ),
  )
  |> ignore
  share_grobner__set_poly_termlist(p, cdr(share_grobner__poly_termlist(p)))
  |> ignore
}

///|
/// Pseudo-divide F by the polynomial list FL. Values: quotients A,
/// remainder R, scalar C and the number of reductions, with
/// C*F = sum A[i]*FL[i] + R.
fn poly_pseudo_divide(
  ring : Value,
  f : Value,
  fl : Value,
) -> (Value, Value, Value, Value) raise {
  let mut r = share_grobner__make_poly_zero()
  let mut c = share_grobner__runit(ring)
  let zero = share_grobner__make_poly_zero()
  let ac = Collector::new()
  for _ in 0..<length(fl) {
    ac.add(zero)
  }
  let a = ac.result()
  let mut division_count = 0L
  let mut p = f
  while !share_grobner__zerop(p) {
    let mut fl1 = fl // scan list of divisors
    let mut b = a
    while true {
      if fl1 is Nil { // no division occurred
        share_grobner__move_lt(p, r)
        break
      }
      if monom_divides_p(poly_lm(car(fl1)), poly_lm(p)).truthy() { // division occurred
        division_count += 1L
        let (_, c1, c2) = share_grobner__rezgcd(
          ring,
          poly_lc(car(fl1)),
          poly_lc(p),
        )
        let m = monom_div(poly_lm(p), poly_lm(car(fl1)))
        // Multiply the equation c*f=sum ai*fi+r+p by c1.
        let mut x = a
        while x is Cons(_) {
          rplaca(x, scalar_times_poly(ring, c1, car(x))) |> ignore
          x = cdr(x)
        }
        r = scalar_times_poly(ring, c1, r)
        c = share_grobner__rmul(ring, c, c1)
        p = grobner_op(ring, c2, c1, m, p, car(fl1))
        let qb = car(b)
        share_grobner__set_poly_termlist(
          qb,
          cons(
            share_grobner__make_term(m, c2),
            share_grobner__poly_termlist(qb),
          ),
        )
        |> ignore
        break
      }
      fl1 = cdr(fl1)
      b = cdr(b)
    }
  }
  share_grobner__dbg("~&~3T~d reduction~:p", [Fix(division_count)])
  if share_grobner__zerop(r) {
    share_grobner__dbg(" ---> 0", [])
  }
  (mapcar(poly_nreverse, a), poly_nreverse(r), c, Fix(division_count))
}

///|
/// Divide F by G, assuming exact division is possible; the quotient.
fn poly_exact_divide(ring : Value, f : Value, g : Value) -> Value raise {
  let (quot, rem, _, _) = poly_pseudo_divide(ring, f, list1(g))
  if !share_grobner__zerop(rem) {
    raise LispError::SimpleError("Exact division failed.")
  }
  car(quot)
}

// ---------------------------------------------------------------------------
// The normal form

///|
fn normal_form_step(
  ring : Value,
  fl : Value,
  p : Value,
  r : Value,
  c : Value,
  division_count : Value,
) -> (Value, Value, Value, Value) raise {
  let lmp = poly_lm(p)
  let g = find_if(g => monom_divisible_by_p(lmp, poly_lm(g)).truthy(), fl)
  let mut p = p
  let mut r = r
  let mut c = c
  let mut division_count = division_count
  if g.truthy() { // division possible
    division_count = num_add(division_count, Fix(1L))
    let (_, cg, cp) = share_grobner__rezgcd(ring, poly_lc(g), poly_lc(p))
    let m = monom_div(poly_lm(p), poly_lm(g))
    // Multiply the equation c*f=sum ai*fi+r+p by cg.
    r = scalar_times_poly(ring, cg, r)
    c = share_grobner__rmul(ring, c, cg)
    p = grobner_op(ring, cp, cg, m, p, g)
    share_grobner__dbg("/", [])
  } else { // no division possible
    share_grobner__move_lt(p, r)
    share_grobner__dbg("+", [])
  }
  (p, r, c, division_count)
}

///|
/// Loop invariant: c*f0=sum ai*fi+r+f, where f0 is the initial value of f.
fn normal_form(
  ring : Value,
  f : Value,
  fl : Value,
  top_reduction_only? : Value,
) -> (Value, Value, Value) raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  let mut f = f
  let mut r = share_grobner__make_poly_zero()
  let mut c = share_grobner__runit(ring)
  let mut division_count : Value = Fix(0L)
  while !(
      share_grobner__zerop(f) ||
      (top_reduction_only.truthy() && !share_grobner__zerop(r))
    ) {
    let (f1, r1, c1, d1) = normal_form_step(ring, fl, f, r, c, division_count)
    f = f1
    r = r1
    c = c1
    division_count = d1
  }
  share_grobner__dbg("~&~3T~d reduction~:p", [division_count])
  if share_grobner__zerop(r) {
    share_grobner__dbg(" ---> 0", [])
  }
  share_grobner__set_poly_termlist(
    f,
    nreconc(share_grobner__poly_termlist(r), share_grobner__poly_termlist(f)),
  )
  |> ignore
  (f, c, division_count)
}

///|
/// T if G is a Grobner basis by the Buchberger criterion: for every two
/// polynomials h1 and h2 in G, S(h1,h2) reduces to 0 modulo G.
fn buchberger_criterion(ring : Value, g : Value) -> Value raise {
  let n = length(g)
  let c = Collector::new()
  for i in 0..=(n - 2) {
    for j in (i + 1)..=(n - 1) {
      c.add(
        normal_form(
          ring,
          spoly(ring, elt(g, i), elt(g, j)),
          g,
          top_reduction_only=Nil,
        ).0,
      )
    }
  }
  lbool(every(share_grobner__zerop, c.result()))
}

///|
/// Test whether G is a Grobner basis and F is contained in G.
fn grobner_test(ring : Value, g : Value, f : Value) -> Value raise {
  share_grobner__dbg("~&GROBNER CHECK: ", [])
  let stat1 = buchberger_criterion(ring, g)
  let c = Collector::new()
  for i in 0..=(length(f) - 1) {
    c.add(
      normal_form(ring, copy_tree(elt(f, i)), g, top_reduction_only=Nil).0,
    )
  }
  let stat2 = every(share_grobner__zerop, c.result())
  with_special(q_d_poly_grobner_debug, Nil, () => {
    if !stat1.truthy() {
      raise LispError::SimpleError("Buchberger criterion failed.")
    }
    if !stat2 {
      raise LispError::SimpleError("Original polys not in ideal spanned by Grobner.")
    }
  })
  share_grobner__dbg("~&GROBNER CHECK END", [])
  t
}

// ---------------------------------------------------------------------------
// Pairs and the pair queue: struct slots first second sugar division-data.

///|
/// (S . LCM) where S is the sugar of the S-polynomial of P and Q and LCM is
/// LCM(LM(P),LM(Q)).
fn sugar_pair_key(p : Value, q : Value) -> Value raise {
  let lcm = monom_lcm(poly_lm(p), poly_lm(q))
  let d = share_grobner__ex(monom_sugar(lcm))
  cons(
    Fix(
      share_grobner__imax(
        d - share_grobner__ex(monom_sugar(poly_lm(p))) + share_grobner__isugar(p),
        d - share_grobner__ex(monom_sugar(poly_lm(q))) + share_grobner__isugar(q),
      ),
    ),
    lcm,
  )
}

///|
fn share_grobner__make_pair(first : Value, second : Value) -> Value raise {
  let sugar = car(sugar_pair_key(first, second))
  make_struct("pair", [first, second, sugar, Nil])
}

///|
fn share_grobner__pair_first(p : Value) -> Value raise {
  struct_ref(p, 0)
}

///|
fn share_grobner__pair_second(p : Value) -> Value raise {
  struct_ref(p, 1)
}

///|
fn share_grobner__pair_sugar(p : Value) -> Value raise {
  struct_ref(p, 2)
}

///|
/// Pair order based on sugar, ties broken by normal strategy.
fn sugar_order(x : Value, y : Value) -> Value raise {
  lbool(
    num_lt(car(x), car(y)) ||
    (
      num_eq(car(x), car(y)) &&
      num_lt(monom_total_degree(cdr(x)), monom_total_degree(cdr(y)))
    ),
  )
}

///|
/// A priority queue for critical pairs.
fn make_pair_queue() -> Value raise {
  make_priority_queue(
    element_type=q_pair,
    element_key=lfunc("pair-key", args => {
      let pair = arg(args, 0)
      funcall(symval(q_ear_pair_key_function), [
        share_grobner__pair_first(pair),
        share_grobner__pair_second(pair),
      ])
    }),
    test_=symval(q_ear_pair_order),
  )
}

///|
/// Initialize the queue PQ with the critical pairs of F; polynomials 0 to
/// START-1 already form a partial Grobner basis.
fn pair_queue_initialize(pq : Value, f : Value, start : Value) -> Value raise {
  let start = to_int(start)
  let s = length(f) - 1
  let c = Collector::new()
  for i in 0..=(start - 1) {
    for j in start..=s {
      c.add(share_grobner__make_pair(elt(f, i), elt(f, j)))
    }
  }
  for i in start..=(s - 1) {
    for j in (i + 1)..=s {
      c.add(share_grobner__make_pair(elt(f, i), elt(f, j)))
    }
  }
  for pair in c.result().iter() {
    priority_queue_insert(pq, pair) |> ignore
  }
  pq
}

///|
fn pair_queue_insert(b : Value, pair : Value) -> Value raise {
  priority_queue_insert(b, pair)
}

///|
fn pair_queue_remove(b : Value) -> Value raise {
  priority_queue_remove(b)
}

///|
fn pair_queue_size(b : Value) -> Value raise {
  priority_queue_size(b)
}

///|
fn pair_queue_empty_p(b : Value) -> Value raise {
  priority_queue_empty_p(b)
}

///|
fn share_grobner__qempty(b : Value) -> Bool raise {
  pair_queue_empty_p(b).truthy()
}

// ---------------------------------------------------------------------------
// Buchberger algorithm

///|
/// The key of the pair (F G) in the table of treated pairs. The Lisp uses
/// an EQUAL hash table keyed by (LIST F G), i.e. by the identity of the two
/// structures; the port keys an EQL table by an injective integer encoding
/// of their serial numbers (the runtime cannot hash structures).
fn share_grobner__done_key(f : Value, g : Value) -> Value raise {
  let a = share_grobner__ex(struct_ref(f, 2))
  let b = share_grobner__ex(struct_ref(g, 2))
  Fix(((a << 32) | b) * -7046029254386353131L)
}

///|
/// Mark the pairs of F[0..START-1] as done.
fn share_grobner__init_done(f : Value, start : Int) -> Value raise {
  let b_done = make_hash_table(kind=Eql)
  for i in 0..<(start - 1) {
    for j in (i + 1)..<start {
      sethash(share_grobner__done_key(elt(f, i), elt(f, j)), b_done, t)
      |> ignore
    }
  }
  b_done
}

///|
/// The Buchberger algorithm: a Grobner basis of the ideal generated by F.
/// Polynomials 0 to START-1 are assumed to be a Grobner basis already. All
/// polynomials in F are assumed non-zero.
fn buchberger(
  ring : Value,
  f : Value,
  start : Value,
  top_reduction_only? : Value,
) -> Value raise {
  let top_reduction_only = match top_reduction_only {
    Some(v) => v
    None => symval(q_d_poly_top_reduction_only)
  }
  if f is Nil {
    return f // cut startup costs
  }
  share_grobner__dbg("~&GROBNER BASIS - BUCHBERGER ALGORITHM", [])
  if plusp(start) {
    share_grobner__dbg("~&INCREMENTAL:~d done", [start])
  }
  // Initialize critical pairs
  let b = pair_queue_initialize(make_pair_queue(), f, start)
  let b_done = share_grobner__init_done(f, to_int(start))
  let mut f = f
  while !share_grobner__qempty(b) {
    let pair = pair_queue_remove(b)
    if criterion_1(pair).truthy() {
      ()
    } else if criterion_2(pair, b_done, f).truthy() {
      ()
    } else {
      let mut sp = normal_form(
        ring,
        spoly(
          ring,
          share_grobner__pair_first(pair),
          share_grobner__pair_second(pair),
        ),
        f,
        top_reduction_only~,
      ).0
      if share_grobner__zerop(sp) {
        ()
      } else {
        sp = poly_primitive_part(ring, sp).0
        f = nconc(f, list1(sp))
        // Add new critical pairs
        for h in f.iter() {
          pair_queue_insert(b, share_grobner__make_pair(h, sp)) |> ignore
        }
        share_grobner__dbgl(
          "~&Sugar: ~d Polynomials: ~d; Pairs left: ~d; Pairs done: ~d;",
          () => [
            share_grobner__pair_sugar(pair),
            int(length(f)),
            pair_queue_size(b),
            int(hash_table_count(b_done)),
          ],
        )
      }
    }
    sethash(
      share_grobner__done_key(
        share_grobner__pair_first(pair),
        share_grobner__pair_second(pair),
      ),
      b_done,
      t,
    )
    |> ignore
  }
  share_grobner__dbg("~&GROBNER END", [])
  f
}

///|
/// The Buchberger algorithm with normal forms computed incrementally,
/// sugar degree by sugar degree.
fn parallel_buchberger(
  ring : Value,
  f : Value,
  start : Value,
  top_reduction_only? : Value,
) -> Value raise {
  ignore(top_reduction_only)
  if f is Nil {
    return f // cut startup costs
  }
  share_grobner__dbg("~&GROBNER BASIS - PARALLEL-BUCHBERGER ALGORITHM", [])
  if plusp(start) {
    share_grobner__dbg("~&INCREMENTAL:~d done", [start])
  }
  // Initialize critical pairs
  let b = pair_queue_initialize(make_pair_queue(), f, start)
  let b_done = share_grobner__init_done(f, to_int(start))
  let mut f = f
  while !share_grobner__qempty(b) {
    let pair = pair_queue_remove(b)
    if struct_ref(pair, 3) is Nil {
      struct_set(
        pair,
        3,
        list([
          spoly(
            ring,
            share_grobner__pair_first(pair),
            share_grobner__pair_second(pair),
          ),
          share_grobner__make_poly_zero(),
          share_grobner__runit(ring),
          Fix(0L),
        ]),
      )
      |> ignore
    }
    if criterion_1(pair).truthy() {
      ()
    } else if criterion_2(pair, b_done, f).truthy() {
      ()
    } else {
      let dd = struct_ref(pair, 3)
      let mut p = nth(0, dd)
      let mut sp = nth(1, dd)
      let mut c = nth(2, dd)
      let mut division_count = nth(3, dd)
      if share_grobner__zerop(p) { // normal form completed
        share_grobner__dbg("~&~3T~d reduction~:p", [division_count])
        if share_grobner__zerop(sp) {
          share_grobner__dbg(" ---> 0", [])
        } else {
          sp = poly_nreverse(sp)
          sp = poly_primitive_part(ring, sp).0
          f = nconc(f, list1(sp))
          // Add new critical pairs
          for h in f.iter() {
            pair_queue_insert(b, share_grobner__make_pair(h, sp)) |> ignore
          }
          share_grobner__dbgl(
            "~&Sugar: ~d Polynomials: ~d; Pairs left: ~d; Pairs done: ~d;",
            () => [
              share_grobner__pair_sugar(pair),
              int(length(f)),
              pair_queue_size(b),
              int(hash_table_count(b_done)),
            ],
          )
        }
        sethash(
          share_grobner__done_key(
            share_grobner__pair_first(pair),
            share_grobner__pair_second(pair),
          ),
          b_done,
          t,
        )
        |> ignore
      } else { // normal form not complete
        while true {
          let stop = if num_lt(
              share_grobner__pair_sugar(pair),
              share_grobner__poly_sugar(sp),
            ) {
            share_grobner__dbg("(~a)?", [share_grobner__poly_sugar(sp)])
            true
          } else if share_grobner__zerop(p) {
            share_grobner__dbg(".", [])
            true
          } else {
            false
          }
          if stop {
            rplaca(dd, p) |> ignore
            rplaca(cdr(dd), sp) |> ignore
            rplaca(cddr(dd), c) |> ignore
            rplaca(cdddr(dd), division_count) |> ignore
            struct_set(pair, 2, share_grobner__poly_sugar(sp)) |> ignore
            pair_queue_insert(b, pair) |> ignore
            break
          }
          let (p1, sp1, c1, d1) = normal_form_step(
            ring,
            f,
            p,
            sp,
            c,
            division_count,
          )
          p = p1
          sp = sp1
          c = c1
          division_count = d1
        }
      }
    }
  }
  share_grobner__dbg("~&GROBNER END", [])
  f
}

// ---------------------------------------------------------------------------
// Grobner criteria

///|
/// T if the leading monomials of the two polynomials of PAIR are relatively
/// prime (the first Buchberger criterion).
fn criterion_1(pair : Value) -> Value raise {
  let f = share_grobner__pair_first(pair)
  let g = share_grobner__pair_second(pair)
  if monom_rel_prime_p(poly_lm(f), poly_lm(g)).truthy() {
    share_grobner__dbg(":1", [])
    return t
  }
  Nil
}

///|
/// T if the leading monomial of some element P of PARTIAL-BASIS divides
/// the LCM of the leading monomials of the polynomials of PAIR, and P
/// paired with each of them has already been treated (is in B-DONE).
fn criterion_2(pair : Value, b_done : Value, partial_basis : Value) -> Value raise {
  let f = share_grobner__pair_first(pair)
  let g = share_grobner__pair_second(pair)
  // 0 = :before, 1 = :in-the-middle, 2 = :after. Pairs (I J) have I before
  // J in PARTIAL-BASIS.
  let mut place = 0
  for h in partial_basis.iter() {
    if eq(h, f) {
      place = 1
    } else if eq(h, g) {
      place = 2
    } else if monom_divides_monom_lcm_p(poly_lm(h), poly_lm(f), poly_lm(g)).truthy() &&
      gethash(
        if place == 0 {
          share_grobner__done_key(h, f)
        } else {
          share_grobner__done_key(f, h)
        },
        b_done,
      ).truthy() &&
      gethash(
        if place == 2 {
          share_grobner__done_key(g, h)
        } else {
          share_grobner__done_key(h, g)
        },
        b_done,
      ).truthy() {
      share_grobner__dbg(":2", [])
      return t
    }
  }
  Nil
}

// ---------------------------------------------------------------------------
// The algorithm of Gebauer and Moeller (Becker-Weispfenning, p. 232)

///|
/// Grobner basis by the algorithm of Gebauer and Moeller (BUCHBERGERNEW2 in
/// Becker-Weispfenning). All polynomials in F are assumed non-zero.
fn gebauer_moeller(
  ring : Value,
  f : Value,
  start : Value,
  top_reduction_only? : Value,
) -> Value raise {
  ignore(top_reduction_only)
  if f is Nil {
    return Nil
  } else if cdr(f) is Nil {
    return list1(poly_primitive_part(ring, car(f)).0)
  }
  share_grobner__dbg("~&GROBNER BASIS - GEBAUER MOELLER ALGORITHM", [])
  if plusp(start) {
    share_grobner__dbg("~&INCREMENTAL:~d done", [start])
  }
  let mut b = make_pair_queue()
  let mut g = subseq(f, 0, end=to_int(start))
  let mut f1 = subseq(f, to_int(start))
  while f1 is Cons(_) {
    let x = car(f1)
    f1 = cdr(f1)
    let (g2, b2) = gebauer_moeller_update(g, b, poly_primitive_part(ring, x).0)
    g = g2
    b = b2
  }
  while !share_grobner__qempty(b) {
    let pair = pair_queue_remove(b)
    let g1 = share_grobner__pair_first(pair)
    let g2 = share_grobner__pair_second(pair)
    let mut h = normal_form(
      ring,
      spoly(ring, g1, g2),
      g,
      top_reduction_only=Nil, // Always fully reduce!
    ).0
    if !share_grobner__zerop(h) {
      h = poly_primitive_part(ring, h).0
      let (gn, bn) = gebauer_moeller_update(g, b, h)
      g = gn
      b = bn
      share_grobner__dbgl("~&Sugar: ~d Polynomials: ~d; Pairs left: ~d~%", () => [
        share_grobner__pair_sugar(pair),
        int(length(g)),
        pair_queue_size(b),
      ])
    }
  }
  share_grobner__dbg("~&GROBNER END", [])
  g
}

///|
/// The auxiliary UPDATE algorithm of Gebauer-Moeller: G is a list of
/// polynomials, B the critical pairs and H a new polynomial.
fn gebauer_moeller_update(
  g : Value,
  b : Value,
  h : Value,
) -> (Value, Value) raise {
  let b_new = make_pair_queue()
  let mut c = g
  let mut d : Value = Nil
  while c is Cons(_) {
    let g1 = car(c)
    c = cdr(c)
    let crit = fn(g2 : Value) -> Bool raise {
      monom_lcm_divides_monom_lcm_p(
        poly_lm(h),
        poly_lm(g2),
        poly_lm(h),
        poly_lm(g1),
      ).truthy()
    }
    if monom_rel_prime_p(poly_lm(h), poly_lm(g1)).truthy() ||
      (!some(crit, c) && !some(crit, d)) {
      d = cons(g1, d)
    }
  }
  let mut e : Value = Nil
  while d is Cons(_) {
    let g1 = car(d)
    d = cdr(d)
    if !monom_rel_prime_p(poly_lm(h), poly_lm(g1)).truthy() {
      e = cons(g1, e)
    }
  }
  while !share_grobner__qempty(b) {
    let pair = pair_queue_remove(b)
    let g1 = share_grobner__pair_first(pair)
    let g2 = share_grobner__pair_second(pair)
    if !monom_divides_monom_lcm_p(poly_lm(h), poly_lm(g1), poly_lm(g2)).truthy() ||
      monom_lcm_equal_monom_lcm_p(
        poly_lm(g1),
        poly_lm(h),
        poly_lm(g1),
        poly_lm(g2),
      ).truthy() ||
      monom_lcm_equal_monom_lcm_p(
        poly_lm(h),
        poly_lm(g2),
        poly_lm(g1),
        poly_lm(g2),
      ).truthy() {
      pair_queue_insert(b_new, share_grobner__make_pair(g1, g2)) |> ignore
    }
  }
  for g3 in e.iter() {
    pair_queue_insert(b_new, share_grobner__make_pair(h, g3)) |> ignore
  }
  let mut g_new : Value = Nil
  let mut gg = g
  while gg is Cons(_) {
    let g1 = car(gg)
    gg = cdr(gg)
    if !monom_divides_p(poly_lm(h), poly_lm(g1)).truthy() {
      g_new = cons(g1, g_new)
    }
  }
  g_new = cons(h, g_new)
  (g_new, b_new)
}
