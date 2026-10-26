// Port of share/contrib/lll.lisp: the LLL lattice reduction algorithm and
// its use for finding integer relations and recognizing algebraic numbers.
//
// The Lisp file also defines DOT, a vector dot product, which replaces the
// global DOT of amatrix.lisp when lll.lisp is loaded. The port keeps it as
// the private helper `share_lll__dot` (installing it in DOT's function cell
// would break amatrix).

///|
let share_lll__q_sol : Value = sym("*sol*")

///|
/// (make-array (list n) :initial-contents l): the contents must have the
/// array's length.
fn share_lll__vector_of(n : Int, l : Value) -> Value raise {
  if length(l) != n {
    raise LispError::SimpleError(
      "There are " + length(l).to_string() +
      " elements in the :INITIAL-CONTENTS, but the vector length is " +
      n.to_string() +
      ".",
    )
  }
  vector(list_to_array(l))
}

///|
fn d_latticereduce(l : Value) -> Value raise {
  // L is maxima list of maxima lists
  if !listp(l) ||
    length(l) < 2 ||
    !equal(
      reduce((a, b) => num_max(a, b), mapcar(x => int(length(x)), cdr(l))),
      reduce((a, b) => num_min(a, b), mapcar(x => int(length(x)), cdr(l))),
    ) {
    merror(Str("Latticereduce needs a list lists as input"), Nil) |> ignore
  }
  let vs = mapcar(x => cdr(x), cdr(l))
  let n = length(vs)
  let mut v = make_array([n])
  for i in 0..<n {
    aset1(v, i, share_lll__vector_of(n, nth(i, vs))) |> ignore
  }
  v = lll(v)
  cons(
    list1(q_mlist),
    mapcar(u => cons(list1(q_mlist), vector_to_list(u)), vector_to_list(v)),
  )
}

///|
fn d_integerrelations(l : Value) -> Value raise {
  let res = integerrelations(cdr(l))
  cons(list1(q_mlist), car(res))
}

///|
fn d_floatrelations(l : Value) -> Value raise {
  let res = floatrelations(cdr(l))
  cons(list1(q_mlist), car(res))
}

///|
fn d_recognize(x : Value) -> Value raise {
  convert2algnum(x)
}

// linear algebra helpers

///|
fn norm2(a : Value) -> Value raise {
  let mut s = int(0)
  for i in 0..<length(a) {
    s = num_add(s, num_mul(aref1(a, i), aref1(a, i)))
  }
  s
}

///|
fn vadd(a : Value, b : Value) -> Value raise {
  if length(a) != length(b) {
    raise LispError::SimpleError("vadd: length must coincide")
  }
  let n = length(a)
  let res = make_array([n])
  for i in 0..<n {
    aset1(res, i, num_add(aref1(a, i), aref1(b, i))) |> ignore
  }
  res
}

///|
fn vsub(a : Value, b : Value) -> Value raise {
  if length(a) != length(b) {
    raise LispError::SimpleError("vadd: length must coincide")
  }
  let n = length(a)
  let res = make_array([n])
  for i in 0..<n {
    aset1(res, i, num_sub(aref1(a, i), aref1(b, i))) |> ignore
  }
  res
}

///|
fn smul(s : Value, a : Value) -> Value raise {
  let n = length(a)
  let res = make_array([n])
  for i in 0..<n {
    aset1(res, i, num_mul(s, aref1(a, i))) |> ignore
  }
  res
}

///|
/// DOT of lll.lisp.
fn share_lll__dot(a : Value, b : Value) -> Value raise {
  if length(a) != length(b) {
    raise LispError::SimpleError("vadd: length must coincide")
  }
  let mut s = int(0)
  for i in 0..<length(a) {
    s = num_add(s, num_mul(aref1(a, i), aref1(b, i)))
  }
  s
}

///|
/// Returns the Gram-Schmidt orthogonal basis of F, updates MU.
fn gso(f : Value, mu : Value) -> Value raise {
  let n = length(f)
  let g = make_array([n])
  for j in 0..<n {
    aset1(g, j, aref1(f, j)) |> ignore
  }
  for j in 0..<n {
    for k in 0..<j {
      if num_gt(norm2(aref1(g, k)), int(0)) {
        aset(
          mu,
          [j, k],
          num_div(
            share_lll__dot(aref1(f, j), aref1(g, k)),
            share_lll__dot(aref1(g, k), aref1(g, k)),
          ),
        )
        |> ignore
        aset1(
          g,
          j,
          vsub(aref1(g, j), smul(aref(mu, [j, k]), aref1(g, k))),
        )
        |> ignore
      }
    }
  }
  g
}

///|
/// F is a vector of n vectors.
fn lll(f : Value) -> Value raise {
  let n = length(f)
  let g = make_array([n])
  let mut i = 1
  let mu = make_array([n, n], initial=int(0))
  for j in 0..<n {
    aset1(g, j, aref1(f, j)) |> ignore
    aset(mu, [j, j], int(1)) |> ignore
  }
  let mut gg = gso(g, mu)
  while !(i >= n) {
    for j = i - 1; j >= 0; j = j - 1 {
      aset1(
        g,
        i,
        vsub(aref1(g, i), smul(nint(aref(mu, [i, j])), aref1(g, j))),
      )
      |> ignore
      gg = gso(g, mu)
    }
    if i > 0 &&
      num_gt(
        norm2(aref1(gg, i - 1)),
        num_mul(int(2), norm2(aref1(gg, i))),
      ) {
      let temp = aref1(g, i - 1)
      aset1(g, i - 1, aref1(g, i)) |> ignore
      aset1(g, i, temp) |> ignore
      gg = gso(g, mu)
      i = i - 1
    } else {
      i = i + 1
    }
  }
  g
}

///|
fn nint(q : Value) -> Value raise {
  floor1(num_add(q, num_div(int(1), int(2))))
}

///|
fn share_lll__vec2(a : Int, b : Int) -> Value {
  vector([int(a), int(b)])
}

///|
fn test1() -> Value raise {
  lll(vector([share_lll__vec2(12, 2), share_lll__vec2(13, 4)]))
}

///|
fn test2() -> Value raise {
  lll(vector([share_lll__vec2(12, 2), share_lll__vec2(1, 2)]))
}

///|
fn test3() -> Value raise {
  lll(vector([share_lll__vec2(1, 2), share_lll__vec2(12, 2)]))
}

///|
fn test4() -> Value raise {
  lll(vector([share_lll__vec2(1, 2), share_lll__vec2(9, -4)]))
}

///|
/// L is a list of integers; returns (rel def) such that the dot product
/// def of rel and L is small.
fn integerrelations(l : Value) -> Value raise {
  let n = length(l)
  let mut optdef = int(0)
  let mut optres : Value = Nil
  let f = make_array([n + 1])
  aset1(f, 0, make_array([n + 1], initial=int(0))) |> ignore
  for i in 1..=n {
    let z = make_array([n + 1], initial=int(0))
    aset1(z, 0, nth(i - 1, l)) |> ignore
    aset1(z, i, int(1)) |> ignore
    aset1(f, i, z) |> ignore
  }
  let g = lll(f)
  // most-positive-fixnum
  optdef = Fix(4611686018427387903L)
  for k in 1..=n {
    let mut def = int(0)
    let mut res : Value = Nil
    for i = n; i >= 1; i = i - 1 {
      res = cons(aref1(aref1(g, k), i), res)
      def = num_add(def, num_mul(nth(i - 1, l), aref1(aref1(g, k), i)))
    }
    if num_lt(num_abs(def), num_abs(optdef)) {
      optdef = def
      optres = res
    }
  }
  list([optres, optdef])
}

///|
fn test5() -> Value raise {
  print(Str("Should give ((3 -7 4) 0)")) |> ignore
  integerrelations(
    list([
      Fix(5707963267L),
      Fix(4142135623L),
      Fix(2967764890L),
    ]),
  )
}

///|
fn nkomma(a : Value) -> Value raise {
  num_sub(a, floor1(a))
}

///|
/// X is a list of floats or doubles.
fn floatrelations(x : Value, digits? : Value = Fix(10L)) -> Value raise {
  let nkommastellen = (x : Value) => {
    // x ist float
    let mut s = 0
    while !num_lt(
        num_abs(nkomma(num_mul(x, expt(Flo(10.0), int(s))))),
        expt(Flo(0.1), digits),
      ) {
      s = s + 1
    }
    int(s)
  }
  let digs = mapcar(nkommastellen, x)
  let expo = reduce((a, b) => num_max(a, b), digs)
  let xx = mapcar(u => floor1(num_mul(u, expt(Flo(10.0), expo))), x)
  let rel = integerrelations(xx)
  list([car(rel), num_div(cadr(rel), expt(Flo(10.0), expo))])
}

///|
fn test6() -> Value raise {
  floatrelations(list([Flo(0.5707963267), Flo(0.4142135623), Flo(0.296776489)]))
}

///|
fn mkdif(a : Value, b : Value) -> Value raise {
  list([list1(q_mplus), a, list([list1(q_mminus), b])])
}

///|
fn mksum(a : Value, b : Value) -> Value raise {
  list([list1(q_mplus), a, b])
}

///|
fn mkprod(a : Value, b : Value) -> Value raise {
  list([list1(q_mtimes), a, b])
}

///|
fn mkexpt(a : Value, b : Value) -> Value raise {
  list([list1(q_mexpt), a, b])
}

///|
fn mkeq(a : Value, b : Value) -> Value raise {
  list([list1(q_mequal), a, b])
}

///|
fn max2str(expr : Value) -> Value raise {
  mfuncall(q_d_string, list1(expr))
}

///|
/// X is a float or double.
fn convert2algnum(x : Value, digits? : Value = Fix(10L)) -> Value raise {
  let nn = 6 // maximal search degree
  let mut opt : Value = Nil
  let mut mini : Value = Flo(0.0)
  let var_ = d_gensym(x=Str("v"))
  for n in 2..=nn {
    if opt.truthy() {
      break
    }
    let xs = Collector::new()
    for i in 0..=n {
      xs.add(expt(x, int(i)))
    }
    let res = floatrelations(xs.result(), digits~)
    let def = cadr(res)
    if num_lt(num_abs(def), expt(Flo(10.0), num_neg(digits))) {
      let mut pol = int(0)
      for i in 0..=n {
        pol = mksum(pol, mkprod(nth(i, car(res)), mkexpt(var_, int(i))))
      }
      let mut sol = meval(d_solve(mkeq(pol, int(0)), varl=var_))
      if cdr(sol).truthy() {
        // a solution has been found
        set(share_lll__q_sol, sol) |> ignore
        sol = mapcar(s => third(s), cdr(sol))
        sol = mapcar(
          u => {
            let _ = d_realpart(u)
            let i = d_float(d_imagpart(u))
            if equal(i, int(0)) || equal(i, Flo(0.0)) {
              list([u, num_abs(num_sub(x, d_float(u)))])
            } else {
              list([u, Flo(@double.max_value)])
            }
          },
          sol,
        )
        mini = Flo(@double.max_value)
        for p in sol.iter() {
          if num_lt(second(p), mini) {
            opt = car(p)
            mini = second(p)
          }
        }
      }
    }
  }
  opt
}

///|
fn test7() -> Value raise {
  // fails
  convert2algnum(Flo(1.414213562373))
}

///|
fn test8() -> Value raise {
  // works
  convert2algnum(Flo(2.0 + 3.0 * 1.414213562373))
}

///|
fn test9() -> Value raise {
  // fails
  convert2algnum(Flo(1.0 + 2.0.sqrt() + 3.0.sqrt()))
}
