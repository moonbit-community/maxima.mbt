// The bigfloat-package COBYLA instantiated with plain doubles must follow
// the double-precision translation step by step: same iterates, same
// results, bit for bit.  (The BIGFLOAT package's generic arithmetic on two
// doubles is CL's.)

///|
let bf_test_problem : Ref[String] = { val: "" }

///|
fn bf_test_fc(p : String, x : (Int) -> Double, con : (Int, Double) -> Unit) -> Double {
  match p {
    "quad" => 10.0 * ((x(0) + 1.0) * (x(0) + 1.0)) + x(1) * x(1)
    "circle" => {
      con(0, 1.0 - x(0) * x(0) - x(1) * x(1))
      x(0) * x(1)
    }
    "parab" => {
      con(0, x(1) - x(0) * x(0))
      con(1, 1.0 - x(0) * x(0) - x(1) * x(1))
      -x(0) - x(1)
    }
    "rosen-suzuki" => {
      let x1 = x(0)
      let x2 = x(1)
      let x3 = x(2)
      let x4 = x(3)
      con(0, 8.0 - x1 * x1 - x2 * x2 - x3 * x3 - x4 * x4 - x1 + x2 - x3 + x4)
      con(1, 10.0 - x1 * x1 - 2.0 * (x2 * x2) - x3 * x3 - 2.0 * (x4 * x4) + x1 + x4)
      con(2, 5.0 - 2.0 * (x1 * x1) - x2 * x2 - x3 * x3 - 2.0 * x1 + x2 + x4)
      x1 * x1 + x2 * x2 + 2.0 * (x3 * x3) + x4 * x4 - 5.0 * x1 - 5.0 * x2 - 21.0 * x3 +
      7.0 * x4
    }
    _ => abort(p)
  }
}

///|
impl BfReal for Double with from_double(d) {
  d
}

///|
impl BfReal for Double with from_int(i) {
  i.to_double()
}

///|
impl BfReal for Double with add(a, b) {
  a + b
}

///|
impl BfReal for Double with sub(a, b) {
  a - b
}

///|
impl BfReal for Double with mul(a, b) {
  a * b
}

///|
impl BfReal for Double with div(a, b) {
  a / b
}

///|
impl BfReal for Double with neg(a) {
  -a
}

///|
impl BfReal for Double with expt(a, b) {
  // (expt x 2) only
  guard b == 2.0
  a * a
}

///|
impl BfReal for Double with lt(a, b) {
  a < b
}

///|
impl BfReal for Double with gt(a, b) {
  a > b
}

///|
impl BfReal for Double with le(a, b) {
  a <= b
}

///|
impl BfReal for Double with ge(a, b) {
  a >= b
}

///|
impl BfReal for Double with eq(a, b) {
  a == b
}

///|
impl BfReal for Double with max(a, b) {
  d_max(a, b)
}

///|
impl BfReal for Double with min(a, b) {
  d_min(a, b)
}

///|
impl BfReal for Double with abs(a) {
  d_abs(a)
}

///|
impl BfReal for Double with sqrt(a) {
  f_sqrt(a)
}

///|
impl BfReal for Double with coerce_bigfloat(a) {
  a
}

///|
impl BfReal for Double with format_directive(a, d) {
  // the double-precision code's directive
  let sb = StringBuilder::new()
  let saved = @f2cl.output_hook.val
  @f2cl.output_hook.val = s => sb.write_string(s)
  fformat(6, [Dir(d.replace(old="E/bigfloat:format-e/", new="EE"))], [AD(a)])
  @f2cl.output_hook.val = saved
  sb.to_string()
}

///|
impl BfReal for Double with calcfc(_n, _m, x, _f, con, co) {
  bf_test_fc(bf_test_problem.val, k => x[k], (k, v) => con[co + k] = v)
}

///|
fn bf_test_bits(xs : Iter[Double]) -> String {
  let sb = StringBuilder::new()
  for x in xs {
    sb.write_string(" " + x.reinterpret_as_int64().to_string())
  }
  sb.to_string()
}

///|
fn bf_test_run(
  p : String,
  m : Int,
  x0 : Array[Double],
  rhobeg : Double,
  rhoend : Double,
  iprint : Int,
  maxfun : Int,
) -> (String, String) raise {
  bf_test_problem.val = p
  let n = x0.length()
  let size = n * (3 * n + 2 * m + 11) + 4 * m + 6 + 6
  let out = StringBuilder::new()
  let saved = @f2cl.output_hook.val
  @f2cl.output_hook.val = s => out.write_string(s)
  // double precision
  let x = FixedArray::from_array(x0)
  let w = FixedArray::make(size, 0.0)
  let iact = FixedArray::make(m + 1, 0)
  calcfc_hook.val = fn(_n, _m, x, _f, con, co) {
    bf_test_fc(p, k => x[k], (k, v) => con[co + k] = v)
  }
  let r1 = cobyla(n, m, x, rhobeg, rhoend, iprint, maxfun, w, iact, 0)
  let s1 = "\{r1} \{bf_test_bits(x.iter())} \{bf_test_bits(w.iter())} \{out.to_string()}"
  out.reset()
  // the bigfloat-package code on doubles
  let xb = x0.copy()
  let wb = Array::make(size, 0.0)
  let iactb = FixedArray::make(m + 1, 0)
  let r2 = bf_cobyla(n, m, xb, rhobeg, rhoend, iprint, maxfun, wb, iactb, 0)
  let s2 = "\{r2} \{bf_test_bits(xb.iter())} \{bf_test_bits(wb.iter())} \{out.to_string()}"
  @f2cl.output_hook.val = saved
  (s1, s2)
}

///|
test "bigfloat-package COBYLA on doubles = double COBYLA" {
  for c in [
    ("quad", 0, [1.0, 1.0]),
    ("circle", 1, [1.0, 1.0]),
    ("parab", 2, [1.0, 1.0]),
    ("rosen-suzuki", 3, [1.0, 1.0, 1.0, 1.0]),
  ] {
    for iprint in [0, 1, 2, 3] {
      let (s1, s2) = bf_test_run(c.0, c.1, c.2, 0.5, 1.0e-6, iprint, 2000)
      assert_eq(s2, s1)
    }
    let (s1, s2) = bf_test_run(c.0, c.1, c.2, 0.5, 1.0e-8, 1, 15)
    assert_eq(s2, s1)
  }
}
