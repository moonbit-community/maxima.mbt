// Port of src/plasma.lisp: the Plasma Dispersion Function NZETA(Z).
//
// This function is related to the complex error function by
//
//    NZETA(Z) = %I*SQRT(%PI)*EXP(-Z^2)*(1-ERF(-%I*Z))
//
// NZETA(Z) returns the complex value of the Plasma Dispersion Function for
// complex Z. NZETAR(Z) returns REALPART(NZETA(Z)). NZETAI(Z) returns
// IMAGPART(NZETA(Z)).

///|
fn z_function(x : Value, y : Value) -> Value raise {
  let x0 = to_double(x)
  let y0 = to_double(y)
  let xs = if 0.0 > x0 { -1.0 } else { 1.0 }
  let ys = if 0.0 > y0 { -1.0 } else { 1.0 }
  let mut capn = 0
  let mut nu = 0
  let mut h = 0.0
  let mut h2 = 0.0
  let mut lamb = 0.0
  let mut r1 = 0.0
  let mut r2 = 0.0
  let mut s = 0.0
  let mut s1 = 0.0
  let mut s2 = 0.0
  let mut t1 = 0.0
  let mut t2 = 0.0
  let mut c = 0.0
  let x = x0.abs()
  let y = y0.abs()
  if 4.29 > y && 5.33 > x {
    s = (1.0 + -0.23310023 * y) * (1.0 + -0.035198873 * x * x).sqrt()
    h = 1.6 * s
    h2 = 2.0 * h
    capn = 6 + (23.0 * s).floor().to_int()
    nu = 9 + (21.0 * s).floor().to_int()
  } else {
    h = 0.0
    capn = 0
    nu = 8
  }
  if h > 0.0 {
    lamb = @math.pow(h2, capn.to_double())
  }
  let bool = h == 0.0 || lamb == 0.0
  let mut n = nu
  while !(0 > n) {
    t1 = h + (n + 1).to_double() * r1 + y
    t2 = x - (n + 1).to_double() * r2
    c = 0.5 / (t1 * t1 + t2 * t2)
    r1 = c * t1
    r2 = c * t2
    if h > 0.0 && !(capn < n) {
      t1 = s1 + lamb
      s1 = r1 * t1 - r2 * s2
      s2 = r1 * s2 + r2 * t1
      lamb = lamb / h2
    }
    n = n - 1
  }
  let mut im = if y == 0.0 {
    1.77245384 * @math.exp(-(x * x))
  } else {
    2.0 * (if bool { r1 } else { s1 })
  }
  let mut re = -2.0 * (if bool { r2 } else { s2 })
  if ys > 0.0 {
    re = re * xs
  } else {
    r1 = 3.5449077 * @math.exp(y * y - x * x)
    r2 = 2.0 * x * y
    re = (re - r1 * @math.sin(r2)) * xs
    im = r1 * @math.cos(r2) - im
  }
  mk_simp(q_mlist, [Flo(re), Flo(im)])
}

///|
fn d_nzeta(z : Value) -> Value raise {
  let x = d_realpart(z)
  let y = d_imagpart(z)
  if numberp(x) && numberp(y) {
    let w = z_function(lfloat(x), lfloat(y))
    simplify(mk(q_mplus, [second(w), simplify(mk(q_mtimes, [q_d__pcti, third(w)]))]))
  } else {
    mk_simp(q_d_nzeta, [z])
  }
}

///|
fn d_nzetar(z : Value) -> Value raise {
  let x = d_realpart(z)
  let y = d_imagpart(z)
  if numberp(x) && numberp(y) {
    second(z_function(lfloat(x), lfloat(y)))
  } else {
    mk_simp(q_d_nzetar, [z])
  }
}

///|
fn d_nzetai(z : Value) -> Value raise {
  let x = d_realpart(z)
  let y = d_imagpart(z)
  if numberp(x) && numberp(y) {
    third(z_function(lfloat(x), lfloat(y)))
  } else {
    mk_simp(q_d_nzetai, [z])
  }
}
