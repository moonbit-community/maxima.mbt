// Port of share/nelder_mead/neldermead.lisp (package NELDERMEAD): the
// Nelder-Mead simplex method, with the grid-restrained variant (GRNM) of
// Burmen, Puhan and Tuma.
//
// The CLOS classes are Lisp structures: NM-SIMPLEX (x fx pmap data),
// CACHED-SIMPLEX-DATA (pseudopivot q-factor side-vectors r-factor dv dmin
// best-before-reshape) and GRID (z delta). The methods, which are not in
// the generated contract, are private functions (neldermead__*).

// ---------------------------------------------------------------------
// Classes

///|
fn neldermead__make_simplex(x : Value, fx : Value, pmap : Value) -> Value {
  make_struct("nm-simplex", [x, fx, pmap, Nil])
}

///|
fn neldermead__x(s : Value) -> Value raise {
  neldermead__check(s, "nm-simplex")
  struct_ref(s, 0)
}

///|
fn neldermead__fx(s : Value) -> Value raise {
  neldermead__check(s, "nm-simplex")
  struct_ref(s, 1)
}

///|
fn neldermead__pmap(s : Value) -> Value raise {
  neldermead__check(s, "nm-simplex")
  struct_ref(s, 2)
}

///|
fn neldermead__data(s : Value) -> Value raise {
  neldermead__check(s, "nm-simplex")
  struct_ref(s, 3)
}

///|
fn neldermead__set_data(s : Value, d : Value) -> Unit raise {
  struct_set(s, 3, d) |> ignore
}

///|
/// The slots of CACHED-SIMPLEX-DATA.
const NM_PSEUDOPIVOT : Int = 0

///|
const NM_Q_FACTOR : Int = 1

///|
const NM_SIDE_VECTORS : Int = 2

///|
const NM_R_FACTOR : Int = 3

///|
const NM_DV : Int = 4

///|
const NM_DMIN : Int = 5

///|
fn neldermead__make_cached(dv : Value, dmin : Value, bbr : Value) -> Value {
  make_struct("cached-simplex-data", [Nil, Nil, Nil, Nil, dv, dmin, bbr])
}

///|
/// A slot accessor applied to an object of the wrong class (CLOS: no
/// applicable method).
fn neldermead__check(x : Value, cls : String) -> Unit raise {
  if !struct_typep(x, cls) {
    lisp_error(
      "There is no applicable method for the generic function when called with arguments (" +
      prin1_to_string(x) +
      ").",
    )
    |> ignore
  }
}

///|
fn neldermead__slot(d : Value, i : Int) -> Value raise {
  neldermead__check(d, "cached-simplex-data")
  struct_ref(d, i)
}

///|
fn neldermead__make_grid(z : Value, delta : Value) -> Value {
  make_struct("grid", [z, delta])
}

///|
fn neldermead__grid_z(g : Value) -> Value raise {
  neldermead__check(g, "grid")
  struct_ref(g, 0)
}

///|
fn neldermead__delta(g : Value) -> Value raise {
  neldermead__check(g, "grid")
  struct_ref(g, 1)
}

// ---------------------------------------------------------------------
// Simplex methods

///|
fn neldermead__xk(s : Value, k : Int) -> Value raise {
  aref1(neldermead__x(s), to_int(aref1(neldermead__pmap(s), k)))
}

///|
fn neldermead__set_xk(s : Value, k : Int, nv : Value) -> Unit raise {
  aset1(neldermead__x(s), to_int(aref1(neldermead__pmap(s), k)), nv) |> ignore
}

///|
fn neldermead__fk(s : Value, k : Int) -> Value raise {
  aref1(neldermead__fx(s), to_int(aref1(neldermead__pmap(s), k)))
}

///|
/// A store into a DOUBLE-FLOAT array.
fn neldermead__dbl(v : Value) -> Value raise {
  match v {
    Flo(_) => v
    _ => raise type_error(v, "DOUBLE-FLOAT")
  }
}

///|
fn neldermead__set_fk(s : Value, k : Int, nv : Value) -> Unit raise {
  aset1(
    neldermead__fx(s),
    to_int(aref1(neldermead__pmap(s), k)),
    neldermead__dbl(nv),
  )
  |> ignore
}

///|
/// SBCL's (unstable) SORT of a vector: an in-place heapsort.
fn neldermead__heapsort(
  vec : Value,
  pred : (Value, Value) -> Bool raise,
  key : (Value) -> Value raise,
) -> Unit raise {
  let n = length(vec)
  // 1-based element access
  let elt = (i : Int) => aref1(vec, i - 1)
  let set_elt = (i : Int, v : Value) => aset1(vec, i - 1, v) |> ignore
  let heapify = (i0 : Int, max : Int) => {
    let mut i = i0
    while true {
      let l = 2 * i
      if l > max {
        break
      }
      let ikey = key(elt(i))
      let lkey = key(elt(l))
      let mut largest = i
      let mut largest_key = ikey
      if pred(ikey, lkey) {
        largest = l
        largest_key = lkey
      }
      let r = l + 1
      if r <= max && pred(largest_key, key(elt(r))) {
        largest = r
      }
      if largest == i {
        break
      }
      let tmp = elt(i)
      set_elt(i, elt(largest))
      set_elt(largest, tmp)
      i = largest
    }
  }
  let mut i = n / 2
  while i >= 1 {
    heapify(i, n)
    i = i - 1
  }
  let mut i = n
  while i > 1 {
    let tmp = elt(1)
    set_elt(1, elt(i))
    set_elt(i, tmp)
    heapify(1, i - 1)
    i = i - 1
  }
}

///|
fn neldermead__sort_simplex(s : Value) -> Value raise {
  let fx = neldermead__fx(s)
  neldermead__heapsort(neldermead__pmap(s), (a, b) => num_lt(a, b), k => aref1(
    fx,
    to_int(k),
  ))
  s
}

///|
fn neldermead__dimension(s : Value) -> Int raise {
  length(neldermead__pmap(s)) - 1
}

///|
/// PRINT-OBJECT of an NM-SIMPLEX.
fn neldermead__print_simplex(s : Value) -> String raise {
  let sb = StringBuilder::new()
  sb.write_string("#<NM-SIMPLEX")
  let level = symval(q_ear_verbose_level)
  if eql(level, Fix(2L)) {
    let fx = neldermead__fx(s)
    let pmap = neldermead__pmap(s)
    let fmt = "~12,3,3E"
    let n = length(pmap)
    for i in 0..<n {
      sb.write_char('\n')
      if fx.truthy() {
        sb.write_string(format_to_string(fmt, [neldermead__fk(s, i)]))
      } else {
        sb.write_string(" -- ")
      }
      sb.write_string(" :")
      for j in 0..<(n - 1) {
        sb.write_string(
          format_to_string(fmt, [aref1(neldermead__xk(s, i), j)]),
        )
      }
    }
  } else if eql(level, Fix(1L)) {
    sb.write_string(
      format_to_string(" D=~A Best=~A ", [
        int(neldermead__dimension(s)),
        if neldermead__fx(s).truthy() {
          format(Nil, "~16,7,3E", [neldermead__fk(s, 0)])
        } else {
          Str("--")
        },
      ]),
    )
  }
  sb.write_string(">")
  sb.to_string()
}

///|
/// simple additive simplex generator
fn neldermead_initial_simplex(
  x0 : Value,
  displace? : Value = Flo(0.1),
) -> Value raise {
  let n = length(x0)
  let x = make_array([n + 1])
  let pmap = make_array([n + 1], initial=Fix(0L))
  aset1(x, 0, x0) |> ignore
  aset1(pmap, 0, Fix(0L)) |> ignore
  for k in 0..<n {
    let xk = copy_seq(x0)
    let d = if numberp(displace) { displace } else { aref1(displace, k) }
    aset1(xk, k, num_add(aref1(xk, k), d)) |> ignore
    aset1(x, k + 1, xk) |> ignore
    aset1(pmap, k + 1, int(k + 1)) |> ignore
  }
  neldermead__make_simplex(x, Nil, pmap)
}

///|
/// The simplex generator from the article, more or less.
fn neldermead_default_initial_simplex(x0 : Value) -> Value raise {
  let n = length(x0)
  let d = make_array([n])
  for i in 0..<n {
    let v = to_double(aref1(x0, i))
    aset1(d, i, num_max(Flo(0.00025), Flo((v * 0.05).abs()))) |> ignore
  }
  neldermead_initial_simplex(x0, displace=d)
}

///|
fn neldermead__maybe_fill_simplex(s : Value, f : Value) -> Value raise {
  if neldermead__fx(s).truthy() {
    return s
  }
  let n = length(neldermead__x(s))
  let fx = make_array([n], initial=Flo(0.0))
  for i in 0..<n {
    aset1(fx, i, neldermead__dbl(funcall(f, [neldermead__xk(s, i)]))) |> ignore
  }
  struct_set(s, 1, fx) |> ignore
  s
}

///|
/// substitutes the worst point with x/fx. Assumes simplex is sorted.
fn neldermead__improve(s : Value, x : Value, fx : Value) -> Value raise {
  let last = length(x)
  neldermead__set_xk(s, last, x)
  neldermead__set_fk(s, last, fx)
  neldermead__set_data(s, Nil)
  neldermead__sort_simplex(s)
}

///|
fn neldermead__cached_slot(
  s : Value,
  slot : Int,
  computer : () -> Value raise,
) -> Value raise {
  let d = neldermead__data(s)
  if d.truthy() && neldermead__slot(d, slot).truthy() {
    return neldermead__slot(d, slot)
  }
  if d is Nil {
    neldermead__set_data(s, neldermead__make_cached(Nil, Nil, Nil))
  }
  let v = computer()
  struct_set(neldermead__data(s), slot, v) |> ignore
  v
}

///|
fn neldermead__pseudopivot(s : Value) -> Value raise {
  neldermead__cached_slot(s, NM_PSEUDOPIVOT, () => {
    let n = length(neldermead__pmap(s)) - 1
    let mut xbar = make_array([n], initial=Flo(0.0))
    for i in 0..<n {
      xbar = neldermead_v_plusw_starc(
        xbar,
        neldermead__xk(s, i + 1),
        Flo(1.0 / n.to_double()),
      )
    }
    xbar
  })
}

///|
fn neldermead__side_vectors(s : Value) -> Value raise {
  neldermead__cached_slot(s, NM_SIDE_VECTORS, () => {
    let n = length(neldermead__pmap(s)) - 1
    let sv = make_array([n])
    for i in 0..<n {
      aset1(
        sv,
        i,
        neldermead_v_plusw_starc(
          neldermead__xk(s, i + 1),
          neldermead__xk(s, 0),
          Fix(-1L),
        ),
      )
      |> ignore
    }
    sv
  })
}

///|
fn neldermead_simplex_qr_thing(sidev : Value) -> (Value, Value, Value) raise {
  let n = length(sidev)
  let norms = make_array([n], initial=Flo(0.0))
  let pmap = make_array([n], initial=Fix(0L))
  let mat = make_array([n, n], initial=Flo(0.0))
  for i in 0..<n {
    aset1(pmap, i, int(i)) |> ignore
    aset1(norms, i, neldermead_norm(aref1(sidev, i))) |> ignore
  }
  neldermead__heapsort(pmap, (a, b) => num_gt(a, b), k => aref1(norms, to_int(k)))
  for i in 0..<n {
    for j in 0..<n {
      aset(mat, [i, j], aref1(aref1(sidev, to_int(aref1(pmap, j))), i)) |> ignore
    }
  }
  let (r, q) = neldermead_qr_factorization(mat)
  (q, r, pmap)
}

///|
fn neldermead_qrthing_closure(s : Value, n : Value) -> Value raise {
  lfunc("qrthing-closure", _ => neldermead__qrthing(s, to_int(n)))
}

///|
fn neldermead__qrthing(s : Value, n : Int) -> Value raise {
  let (q, r, p) = neldermead_simplex_qr_thing(neldermead__side_vectors(s))
  struct_set(neldermead__data(s), NM_Q_FACTOR, q) |> ignore
  struct_set(neldermead__data(s), NM_R_FACTOR, r) |> ignore
  [q, r, p][n]
}

///|
fn neldermead__q_factor(s : Value) -> Value raise {
  neldermead__cached_slot(s, NM_Q_FACTOR, () => neldermead__qrthing(s, 0))
}

///|
fn neldermead__r_factor(s : Value) -> Value raise {
  neldermead__cached_slot(s, NM_R_FACTOR, () => neldermead__qrthing(s, 1))
}

///|
fn neldermead__print(s : Value) -> Unit raise {
  format(t, "~A~%", [Str(neldermead__print_simplex(s))]) |> ignore
}

///|
/// A Nelder-Mead iteration.
fn neldermead_nm_iteration(
  simplex : Value,
  f : Value,
  verbose? : Value = Nil,
  gamma_reflect? : Value = Flo(1.0),
  gamma_expand? : Value = Flo(2.0),
  gamma_outer_contraction? : Value = Flo(0.5),
  gamma_inner_contraction? : Value = Flo(-0.5),
  gamma_shrink? : Value = Flo(0.5),
) -> Value raise {
  let n = length(neldermead__x(simplex)) - 1
  let mut x_cb = make_array([n], initial=Flo(0.0))
  let mut x_cb_x_n = make_array([n], initial=Flo(0.0))
  let newpoint = (gamma : Value) => {
    let np = neldermead_v_plusw_starc(x_cb, x_cb_x_n, gamma)
    (np, funcall(f, [np]))
  }
  let accept = (xx : Value, ff : Value) => neldermead__improve(simplex, xx, ff)
    |> ignore
  let shrink = () => {
    let x0 = neldermead__xk(simplex, 0)
    for i in 1..=n {
      let newx = neldermead_v_plusw_starc(
        neldermead_v_starc(x0, Flo(1.0 - to_double(gamma_shrink))),
        neldermead__xk(simplex, i),
        gamma_shrink,
      )
      let newf = funcall(f, [newx])
      neldermead__set_xk(simplex, i, newx)
      neldermead__set_fk(simplex, i, newf)
      neldermead__sort_simplex(simplex) |> ignore
    }
  }
  // compute centroid
  for i in 0..<n {
    x_cb = neldermead_v_plusw_starc(
      x_cb,
      neldermead__xk(simplex, i),
      Flo(1.0 / n.to_double()),
    )
  }
  x_cb_x_n = neldermead_v_plusw_starc(x_cb, neldermead__xk(simplex, n), Flo(-1.0))
  let fk = (k : Int) => neldermead__fk(simplex, k)
  // 2. Reflect
  let (xr, fr) = newpoint(gamma_reflect)
  if num_le(fk(0), fr) && num_lt(fr, fk(n - 1)) {
    accept(xr, fr)
  } else if num_lt(fr, fk(0)) {
    // 3. expand
    let (xe, fe) = newpoint(gamma_expand)
    if num_lt(fe, fr) {
      accept(xe, fe)
    } else {
      accept(xr, fr)
    }
  } else if num_le(fk(n - 1), fr) {
    // 4. contract or shrink
    if num_lt(fr, fk(n)) {
      // outer contraction
      let (xc, fc) = newpoint(gamma_outer_contraction)
      // 1D shrink is equivalent to acceptance of this point
      if n == 2 || num_le(fc, fr) {
        accept(xc, fc)
      } else {
        shrink()
      }
    } else {
      // inner contraction
      let (xcc, fcc) = newpoint(gamma_inner_contraction)
      if num_lt(fcc, fk(n)) {
        accept(xcc, fcc)
      } else {
        shrink()
      }
    }
  } else {
    shrink()
  }
  if verbose.truthy() {
    neldermead__print(simplex)
  }
  simplex
}

///|
/// The test returns true if the volume of the paralelepiped spanned by the
/// vertices of the simplex is smaller than that of an n-cube of side cside.
fn neldermead_pp_volume_test(cside : Value) -> Value raise {
  lfunc("pp-volume-test", args => {
    let simplex = arg(args, 0)
    let mat = neldermead__r_factor(simplex)
    let mut det : Value = Flo(1.0)
    let dim = neldermead__dimension(simplex)
    for i in 0..<dim {
      det = num_mul(det, aref(mat, [i, i]))
    }
    lbool(num_lt(num_abs(det), expt(cside, int(dim))))
  })
}

///|
fn neldermead__nm_optimize_mv(
  objective_function : Value,
  initial_guess : Value,
  max_function_calls : Value,
  convergence_p : Value,
  verbose : Value,
) -> (Value, Value, Value, Value) raise {
  let simplex = if struct_typep(initial_guess, "nm-simplex") {
    initial_guess
  } else {
    neldermead_default_initial_simplex(initial_guess)
  }
  let mut fvcount = 0
  let rigged_f = lfunc("rigged-f", args => {
    fvcount = fvcount + 1
    funcall(objective_function, [arg(args, 0)])
  })
  let converged_p = (s : Value) => funcall(convergence_p, [s]).truthy() ||
    num_gt(int(fvcount), max_function_calls)
  if verbose.truthy() {
    format(t, "Initial simplex: ~%~A~%---~%", [
      Str(neldermead__print_simplex(simplex)),
    ])
    |> ignore
  }
  neldermead__maybe_fill_simplex(simplex, rigged_f) |> ignore
  while !converged_p(simplex) {
    neldermead_nm_iteration(simplex, rigged_f, verbose~) |> ignore
  }
  (
    neldermead__xk(simplex, 0),
    neldermead__fk(simplex, 0),
    simplex,
    int(fvcount),
  )
}

///|
/// NM-OPTIMIZE returns the values (xk 0), (fk 0), the simplex and the
/// number of function evaluations; this is the primary value
/// (neldermead__nm_optimize_mv returns them all).
fn neldermead_nm_optimize(
  objective_function : Value,
  initial_guess : Value,
  max_function_calls? : Value = Fix(100000L),
  convergence_p? : Value,
  verbose? : Value = Nil,
) -> Value raise {
  let cp = match convergence_p {
    Some(c) => c
    None => neldermead_burmen_et_al_convergence_test()
  }
  neldermead__nm_optimize_mv(
    objective_function, initial_guess, max_function_calls, cp, verbose,
  ).0
}

///|
fn neldermead__restrict(grid : Value, point : Value) -> Value raise {
  let new = copy_seq(point)
  let n = length(point)
  let delta = neldermead__delta(grid)
  let z = neldermead__grid_z(grid)
  for i in 0..<n {
    let di = to_double(aref1(delta, i))
    let zi = to_double(aref1(z, i))
    let q = ((to_double(aref1(new, i)) - zi) / di + 0.5).floor()
    aset1(new, i, Flo(di * q + zi)) |> ignore
  }
  new
}

///|
fn neldermead__maybe_reshape(
  s : Value,
  g : Value,
  ff : Value,
  force : Bool,
) -> Bool raise {
  let n = length(neldermead__side_vectors(s))
  let biglambda = to_double(symval(q_ear_biglambda))
  let smalllambda = to_double(symval(q_ear_smalllambda))
  let mut reshaped_p = false
  let degenerate_p = () => {
    let r = neldermead__r_factor(s)
    let mut ax : Double? = None
    for i in 0..<n {
      let v = to_double(aref(r, [i, i])).abs()
      ax = match ax {
        None => Some(v)
        Some(a) => Some(if v < a { v } else { a })
      }
    }
    let rhs = to_double(symval(q_ear_psi)) *
      to_double(neldermead_norm(neldermead__delta(g))) *
      n.to_double().sqrt() /
      2.0
    match ax {
      Some(a) => a < rhs
      None => raise type_error(Nil, "REAL")
    }
  }
  if force || degenerate_p() {
    reshaped_p = true
    let r = neldermead__r_factor(s)
    let q = neldermead__q_factor(s)
    let mut det = 1.0
    let dv = make_array([n + 1])
    let mut dmin_norm : Double? = None
    let mut dmin : Value = Nil
    let delta_norm = to_double(neldermead_norm(neldermead__delta(g)))
    aset1(dv, 0, neldermead__xk(s, 0)) |> ignore
    for i in 0..<n {
      let di = make_array([n], initial=Flo(0.0))
      let rii = to_double(aref(r, [i, i]))
      let sgn = if rii >= 0.0 { 1.0 } else { -1.0 }
      let abs_rii = rii.abs()
      let quot = n.to_double().sqrt() * delta_norm * 0.5
      let minc = { let b = biglambda * quot; if b < abs_rii { b } else { abs_rii } }
      let maxc = { let a = smalllambda * quot; if minc > a { minc } else { a } }
      let dfkt = sgn * maxc
      det = det * abs_rii
      for j in 0..<n {
        aset1(di, j, Flo(dfkt * to_double(aref(q, [j, i])))) |> ignore
      }
      match dmin_norm {
        Some(d) if !(dfkt.abs() < d) => ()
        _ => {
          dmin_norm = Some(dfkt.abs())
          dmin = di
        }
      }
      aset1(dv, i + 1, di) |> ignore
      let nxi = neldermead__restrict(
        g,
        neldermead_v_plusw_starc(neldermead__xk(s, 0), di, Flo(1.0)),
      )
      let fxi = funcall(ff, [nxi])
      neldermead__set_xk(s, i + 1, nxi)
      neldermead__set_fk(s, i + 1, fxi)
    }
    // Looks like a very extreme situation, but can actually happen.
    if det == 0.0 {
      set(q_ear_breakdown, t) |> ignore
    }
    // Most cached data is invalid, but better keep the reshape data, which
    // might be needed for shrinking the simplex.
    neldermead__set_data(
      s,
      neldermead__make_cached(dv, dmin, neldermead__fk(s, 0)),
    )
    neldermead__sort_simplex(s) |> ignore
  }
  reshaped_p
}

///|
/// Nelder Mead iteration variant from Burmen et al. Does not shrink,
/// "failing" instead. Acceptance criteria for the contraction points are
/// stricter. Iterates are restricted to a grid.
fn neldermead_nm_iteration_burmen_et_al(
  simplex : Value,
  f : Value,
  grid : Value,
  verbose? : Value = Nil,
  gamma_reflect? : Value = Flo(1.0),
  gamma_expand? : Value = Flo(2.0),
  gamma_outer_contraction? : Value = Flo(0.5),
  gamma_inner_contraction? : Value = Flo(-0.5),
) -> (Value, Value) raise {
  let n = length(neldermead__x(simplex)) - 1
  let mut failure = true
  let mut x_cb = make_array([n], initial=Flo(0.0))
  let mut x_cb_x_n = make_array([n], initial=Flo(0.0))
  let newpoint = (gamma : Value) => {
    let np = neldermead__restrict(
      grid,
      neldermead_v_plusw_starc(x_cb, x_cb_x_n, gamma),
    )
    (np, funcall(f, [np]))
  }
  let accept = (xx : Value, ff : Value) => {
    neldermead__improve(simplex, xx, ff) |> ignore
    failure = false
  }
  // compute centroid
  for i in 0..<n {
    x_cb = neldermead_v_plusw_starc(
      x_cb,
      neldermead__xk(simplex, i),
      Flo(1.0 / n.to_double()),
    )
  }
  x_cb_x_n = neldermead_v_plusw_starc(x_cb, neldermead__xk(simplex, n), Flo(-1.0))
  let fk = (k : Int) => neldermead__fk(simplex, k)
  // 2. Reflect
  let (xr, fr) = newpoint(gamma_reflect)
  if num_le(fk(0), fr) && num_lt(fr, fk(n - 1)) {
    accept(xr, fr)
  } else if num_lt(fr, fk(0)) {
    // 3. expand
    let (xe, fe) = newpoint(gamma_expand)
    if num_lt(fe, fr) {
      accept(xe, fe)
    } else {
      accept(xr, fr)
    }
  } else if num_le(fk(n - 1), fr) {
    // 4. contract or fail
    if num_lt(fr, fk(n)) {
      // outer contraction
      let (xc, fc) = newpoint(gamma_outer_contraction)
      if num_le(fc, fk(n - 1)) {
        accept(xc, fc)
      }
    } else {
      // inner contraction
      let (xcc, fcc) = newpoint(gamma_inner_contraction)
      if num_lt(fcc, fk(n - 1)) {
        accept(xcc, fcc)
      }
    }
  }
  neldermead__sort_simplex(simplex) |> ignore
  if verbose.truthy() {
    neldermead__print(simplex)
  }
  (simplex, lbool(failure))
}

///|
/// `(loop for x across v maximizing (abs x))`
fn neldermead__max_abs(v : Value) -> Double? raise {
  let mut m : Double? = None
  for i in 0..<length(v) {
    let a = to_double(aref1(v, i)).abs()
    m = match m {
      None => Some(a)
      Some(b) => Some(if a > b { a } else { b })
    }
  }
  m
}

///|
/// Convergence test used in the article
fn neldermead_burmen_et_al_convergence_test(
  tol_x? : Value = Flo(1.0e-08),
  tol_f? : Value = Flo(1.0e-15),
  rel? : Value = Flo(1.0e-15),
) -> Value raise {
  lfunc("burmen-et-al-convergence-test", args => {
    let s = arg(args, 0)
    let sv = neldermead__side_vectors(s)
    let fdiff = num_abs(
      num_sub(neldermead__fk(s, 0), neldermead__fk(s, neldermead__dimension(s))),
    )
    let mut vijmax : Double? = None
    for i in 0..<length(sv) {
      match neldermead__max_abs(aref1(sv, i)) {
        Some(a) =>
          vijmax = match vijmax {
            None => Some(a)
            Some(b) => Some(if a > b { a } else { b })
          }
        None => raise type_error(Nil, "REAL")
      }
    }
    let ximax = match neldermead__max_abs(neldermead__xk(s, 0)) {
      Some(a) => a
      None => raise type_error(Nil, "REAL")
    }
    let vijmax = match vijmax {
      Some(a) => a
      None => raise type_error(Nil, "REAL")
    }
    lbool(
      num_lt(fdiff, num_max(tol_f, num_mul(rel, neldermead__fk(s, 0)))) &&
      num_lt(Flo(vijmax), num_max(tol_x, num_mul(rel, Flo(ximax)))),
    )
  })
}

///|
fn neldermead_regrid(g : Value, x1 : Value, dmin : Value, fkt : Value) -> Value raise {
  let dmin = neldermead_v_starc(dmin, fkt)
  let n = length(dmin)
  let dmin_norm = to_double(neldermead_norm(dmin))
  let delta = neldermead__delta(g)
  let newd = copy_seq(delta)
  struct_set(g, 0, x1) |> ignore
  let sl = to_double(symval(q_ear_smalllambda))
  let tau_r = to_double(symval(q_ear_tau_r))
  let tau_a = to_double(symval(q_ear_tau_a))
  let nd = n.to_double()
  let dmax = (a : Double, b : Double) => if b > a { b } else { a }
  let dmin2 = (a : Double, b : Double) => if b < a { b } else { a }
  for i in 0..<n {
    let a = to_double(aref1(dmin, i)).abs() / (sl * 250.0 * nd)
    let b = dmin_norm / (sl * 250.0 * nd.pow(3.0 / 2.0))
    let v = dmax(
      dmax(dmin2(dmax(a, b), to_double(aref1(delta, i))), tau_r * to_double(aref1(x1, i))),
      tau_a,
    )
    aset1(newd, i, Flo(v)) |> ignore
  }
  struct_set(g, 1, newd) |> ignore
  newd
}

///|
/// `(sqrt n)` of a positive integer: a SINGLE-FLOAT.
fn neldermead__sqrt_single(n : Int) -> Double {
  Float::from_double(n.to_double().sqrt()).to_double()
}

///|
fn neldermead_deep_shrink(
  f : Value,
  s : Value,
  g : Value,
  gamma_s : Value,
  convergence_p : Value,
  verbose : Value,
) -> Value raise {
  let bbr = neldermead__fk(s, 0)
  if neldermead__slot(neldermead__data(s), NM_DV) is Nil {
    neldermead__maybe_reshape(s, g, f, true) |> ignore
  }
  let dv = neldermead__slot(neldermead__data(s), NM_DV)
  let n = neldermead__dimension(s)
  let dmin = neldermead__slot(neldermead__data(s), NM_DMIN)
  let dmin_norm = to_double(neldermead_norm(dmin))
  let mut converged_p : Value = Nil
  let mut l = 1
  // This does the same as in the article
  while true {
    if num_lt(neldermead__fk(s, 0), bbr) {
      break
    }
    converged_p = funcall(convergence_p, [s])
    if converged_p.truthy() {
      break
    }
    let p = expt(gamma_s, int(l / 2))
    let fkt = num_mul(p, expt(Fix(-1L), int(l)))
    if verbose.truthy() {
      format(t, "Shrinking by factor: ~A~%", [fkt]) |> ignore
    }
    if num_eq(Flo(0.0), fkt) {
      // You've got no simplex anymore
      set(q_ear_breakdown, t) |> ignore
    }
    let lhs = to_double(fkt).abs() * dmin_norm
    let rhs = to_double(symval(q_ear_smalllambda)) / 2.0 *
      neldermead__sqrt_single(n) *
      to_double(neldermead_norm(neldermead__delta(g)))
    if lhs < rhs {
      neldermead_regrid(g, neldermead__xk(s, 0), dmin, fkt) |> ignore
    }
    neldermead__set_xk(s, 0, aref1(dv, 0))
    neldermead__set_fk(s, 0, bbr)
    for k in 1..<length(neldermead__x(s)) {
      neldermead__set_xk(
        s,
        k,
        neldermead__restrict(
          g,
          neldermead_v_plusw_starc(aref1(dv, 0), aref1(dv, k), fkt),
        ),
      )
      neldermead__set_fk(s, k, funcall(f, [neldermead__xk(s, k)]))
    }
    neldermead__sort_simplex(s) |> ignore
    l = l + 1
  }
  neldermead__set_data(s, Nil)
  converged_p
}

///|
fn neldermead__grnm_optimize_mv(
  objective_function : Value,
  initial_guess : Value,
  max_function_calls : Value,
  convergence_p : Value,
  verbose : Value,
) -> (Value, Value, Value, Value) raise {
  let mut simplex = if struct_typep(initial_guess, "nm-simplex") {
    initial_guess
  } else {
    neldermead_default_initial_simplex(initial_guess)
  }
  let mut fvcount = 0
  let gamma_s : Value = Flo(0.5)
  let bd = bind(q_ear_breakdown, Nil)
  defer unbind(bd)
  let rigged_f = lfunc("rigged-f", args => {
    fvcount = fvcount + 1
    funcall(objective_function, [arg(args, 0)])
  })
  let converged_p_fn = (s : Value) => funcall(convergence_p, [s]).truthy() ||
    symval(q_ear_breakdown).truthy() ||
    (max_function_calls.truthy() && num_gt(int(fvcount), max_function_calls))
  let converged_p = lfunc("converged-p", args => lbool(
    converged_p_fn(arg(args, 0)),
  ))
  if verbose.truthy() {
    format(t, "Initial simplex: ~%~A~%---~%", [
      Str(neldermead__print_simplex(simplex)),
    ])
    |> ignore
  }
  neldermead__maybe_fill_simplex(simplex, rigged_f) |> ignore
  let dim = neldermead__dimension(simplex)
  let mut mind : Value = Nil
  for i in 1..=dim {
    let d = neldermead_norm(
      neldermead_v_plusw_starc(
        neldermead__xk(simplex, 0),
        neldermead__xk(simplex, i),
        Flo(-1.0),
      ),
    )
    if mind is Nil || num_lt(d, mind) {
      mind = d
    }
  }
  let grid = neldermead__make_grid(
    neldermead__xk(simplex, 0),
    make_array([dim], initial=num_div(mind, Flo(10.0))),
  )
  // states of the PROG: 0 iterate, 1 deep-shrink, 2 end
  let mut state = 0
  while state != 2 {
    if state == 0 {
      // 1.
      let (s1, failure) = neldermead_nm_iteration_burmen_et_al(
        simplex,
        rigged_f,
        grid,
        verbose~,
      )
      simplex = s1
      // Small variation. We test for convergence here too. Depending on
      // the convergence criterion, this might be spurious, so we have to
      // reshape, etc.
      if !(failure.truthy() || converged_p_fn(simplex)) {
        continue
      }
      // 2.
      let fbest = neldermead__fk(simplex, 0)
      let pbest = aref1(neldermead__pmap(simplex), 0)
      neldermead__maybe_reshape(simplex, grid, rigged_f, false) |> ignore
      // 4. Here we look at the pseudo expand point
      let pep = neldermead__pseudopivot(simplex)
      let xx = neldermead_v_plusw_starc(
        pep,
        neldermead_v_plusw_starc(pep, neldermead__xk(simplex, 0), Flo(-1.0)),
        Flo(1.0),
      )
      let fpep = funcall(rigged_f, [xx])
      if num_le(fbest, num_min(neldermead__fk(simplex, 0), fpep)) {
        state = 1
      } else if num_lt(fpep, fbest) {
        // The pseudo-expand point is supposed to substitute the old (xk
        // 0), which might have changed *position* during reshape, because
        // of the simplex being sorted.
        // Step 5.
        aset1(neldermead__x(simplex), to_int(pbest), xx) |> ignore
        aset1(neldermead__fx(simplex), to_int(pbest), neldermead__dbl(fpep))
        |> ignore
        neldermead__set_data(simplex, Nil)
        neldermead__sort_simplex(simplex) |> ignore
        // Step 6.
        state = 0
      } else {
        state = 1
      }
    } else {
      // deep-shrink
      if neldermead_deep_shrink(
          rigged_f, simplex, grid, gamma_s, converged_p, verbose,
        ).truthy() {
        state = 2
      } else {
        state = 0
      }
    }
  }
  (
    neldermead__xk(simplex, 0),
    neldermead__fk(simplex, 0),
    simplex,
    int(fvcount),
  )
}

///|
/// GRNM-OPTIMIZE returns the values (xk 0), (fk 0), the simplex and the
/// number of function evaluations; this is the primary value
/// (neldermead__grnm_optimize_mv returns them all).
fn neldermead_grnm_optimize(
  objective_function : Value,
  initial_guess : Value,
  max_function_calls? : Value = Nil,
  convergence_p? : Value,
  verbose? : Value = Nil,
) -> Value raise {
  let cp = match convergence_p {
    Some(c) => c
    None => neldermead_burmen_et_al_convergence_test()
  }
  neldermead__grnm_optimize_mv(
    objective_function, initial_guess, max_function_calls, cp, verbose,
  ).0
}

// Some sample functions to play around.

///|
fn neldermead_standard_quadratic(v : Value) -> Value raise {
  let mut s : Value = Fix(0L)
  for i in 0..<length(v) {
    s = num_add(s, expt(aref1(v, i), Fix(2L)))
  }
  s
}

///|
fn neldermead_rosenbrock(v : Value) -> Value raise {
  let x = aref1(v, 0)
  let y = aref1(v, 1)
  num_add(
    expt(num_sub(Fix(1L), x), Fix(2L)),
    num_mul(Fix(100L), expt(num_sub(y, expt(x, Fix(2L))), Fix(2L))),
  )
}

///|
/// Top-level forms of neldermead.lisp: the DEFPARAMETERs with computed
/// values (some parameters, see Burmen et al for further details).
fn init_share_neldermead() -> Unit raise {
  // CL DOUBLE-FLOAT-EPSILON: the smallest e with (/= (+ 1 e) 1)
  let eps = 1.1102230246251568e-16
  set(q_ear_biglambda, Flo(0.5 / eps)) |> ignore
  set(q_ear_tau_r, Flo(2.0 * eps)) |> ignore
  // (expt least-positive-double-float (/ 1.0d0 3.0d0))
  set(q_ear_tau_a, Flo(4.9406564584124654e-324.pow(1.0 / 3.0))) |> ignore
}
