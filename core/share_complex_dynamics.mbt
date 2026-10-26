// Port of share/dynamics/complex_dynamics.lisp: functions julia,
// mandelbrot and rk (Jaime E. Villate).
//
// The iterations of mandelbrot and julia follow CL's numeric contagion:
// the grid coordinates are rationals when the ranges are given as integers,
// and (float x) of a rational is a single-float, so those iterations run in
// single precision.

///|
/// A CL real number as it takes part in the iterations: a rational, a
/// single-float or a double-float.
priv enum CDNum {
  CDRat(Value)
  CDSingle(Float)
  CDDouble(Double)
}

///|
fn complex_dynamics__of(v : Value) -> CDNum raise {
  match v {
    Flo(d) => CDDouble(d)
    Fix(_) | Big(_) | Ratio(_, _) => CDRat(v)
    _ =>
      raise LispError::SimpleError(
        "The value\n  " + prin1_to_string(v) + "\nis not of type\n  NUMBER",
      )
  }
}

///|
fn complex_dynamics__to_double(a : CDNum) -> Double raise {
  match a {
    CDRat(v) => to_double(v)
    CDSingle(f) => f.to_double()
    CDDouble(d) => d
  }
}

///|
fn complex_dynamics__to_single(a : CDNum) -> Float raise {
  match a {
    CDRat(v) => Float::from_double(to_double(v))
    CDSingle(f) => f
    CDDouble(d) => Float::from_double(d)
  }
}

///|
/// (float x)
fn complex_dynamics__float(a : CDNum) -> CDNum raise {
  match a {
    CDRat(_) => CDSingle(complex_dynamics__to_single(a))
    _ => a
  }
}

///|
/// A binary CL arithmetic operation with float contagion.
fn complex_dynamics__op(
  a : CDNum,
  b : CDNum,
  rat : (Value, Value) -> Value raise LispError,
  single : (Float, Float) -> Float,
  double : (Double, Double) -> Double,
) -> CDNum raise {
  match (a, b) {
    (CDDouble(_), _) | (_, CDDouble(_)) =>
      CDDouble(
        double(complex_dynamics__to_double(a), complex_dynamics__to_double(b)),
      )
    (CDSingle(_), _) | (_, CDSingle(_)) =>
      CDSingle(
        single(complex_dynamics__to_single(a), complex_dynamics__to_single(b)),
      )
    (CDRat(x), CDRat(y)) => CDRat(rat(x, y))
  }
}

///|
fn complex_dynamics__add(a : CDNum, b : CDNum) -> CDNum raise {
  complex_dynamics__op(a, b, num_add, (x, y) => x + y, (x, y) => x + y)
}

///|
fn complex_dynamics__sub(a : CDNum, b : CDNum) -> CDNum raise {
  complex_dynamics__op(a, b, num_sub, (x, y) => x - y, (x, y) => x - y)
}

///|
fn complex_dynamics__mul(a : CDNum, b : CDNum) -> CDNum raise {
  complex_dynamics__op(a, b, num_mul, (x, y) => x * y, (x, y) => x * y)
}

///|
/// (> a 4)
fn complex_dynamics__gt4(a : CDNum) -> Bool raise {
  match a {
    CDRat(v) => num_gt(v, Fix(4L))
    CDSingle(f) => f > Float::from_double(4.0)
    CDDouble(d) => d > 4.0
  }
}

///|
/// The common part of $MANDELBROT and $JULIA: the plot options, the grid
/// and the gnuplot-plot object.  ITERATE computes the number of iterations
/// for the grid point (x, y) and writes its line.
fn complex_dynamics__plot(
  extra_options : Value,
  iterate : (Value, Value, Value, Value) -> Unit raise,
) -> Value raise {
  let mut options = copy_tree(symval(q_ear_plot_options))
  let put = (k : Value, v : Value) => options = plot__putf(options, k, v)
  put(q_d_type, Str("plot2d"))
  if !getf(options, q_d_x).truthy() {
    put(q_d_x, list2(Fix(-2L), Fix(2L)))
  }
  if !getf(options, q_d_y).truthy() {
    put(q_d_y, list2(Fix(-2L), Fix(2L)))
  }
  if !getf(options, q_d_iterations).truthy() {
    put(q_d_iterations, Fix(9L))
  }
  if !getf(options, q_d_xlabel).truthy() {
    put(q_d_xlabel, Str("x"))
  }
  if !getf(options, q_d_ylabel).truthy() {
    put(q_d_ylabel, Str("y"))
  }
  if !memq(q_d_color_bar, options).truthy() {
    put(q_d_color_bar, t)
  }
  put(
    q_d_palette,
    lread(
      "(((mlist) $gradient $magenta $violet $blue $cyan $green $yellow $orange $red $brown $black))",
    ),
  )
  // Parses the options given in the command line
  options = plot_options_parser(extra_options, options)
  if !getf(options, q_d_yx_ratio).truthy() {
    put(q_d_same_xy, t)
  }
  let xmin = car(getf(options, q_d_x))
  let xmax = cadr(getf(options, q_d_x))
  let ymin = car(getf(options, q_d_y))
  let ymax = cadr(getf(options, q_d_y))
  let m = getf(options, q_d_iterations)
  let nx = {
    let v = car(getf(options, q_d_grid))
    if v.truthy() { v } else { Fix(30L) }
  }
  let ny = {
    let v = cadr(getf(options, q_d_grid))
    if v.truthy() { v } else { Fix(30L) }
  }
  let dx = num_div(rationalize(num_sub(xmax, xmin)), nx) // x incr. per pixel
  let dy = num_div(rationalize(num_sub(ymax, ymin)), ny) // y incr. per pixel
  // Creates the object that will be passed to the external graphic program
  let plot = plot__make_instance(GnuplotPlot)
  if eq(getf(options, q_d_plot_format), q_d_gnuplot_pipes) {
    plot.pipe = true
  } else {
    put(q_d_plot_format, q_d_gnuplot)
  }
  let output_file = plot__plot_preamble(plot, options)
  let st = make_string_output_stream()
  format(st, "set palette ~a~%", [
    gnuplot_palette(cdr(first(getf(options, q_d_palette)))),
  ])
  |> ignore
  format(st, "unset key~%", []) |> ignore
  format(st, "plot '-' with image~%", []) |> ignore
  // iterates through all grid points
  for i in 0..<to_int(ny) {
    let y = num_add(num_add(ymin, num_div(dy, Fix(2L))), num_mul(int(i), dy))
    for j in 0..<to_int(nx) {
      let x = num_add(num_add(xmin, num_div(dx, Fix(2L))), num_mul(int(j), dx))
      iterate(st, x, y, m)
    }
  }
  format(st, "e~%", []) |> ignore
  plot.data = plot.data + get_output_stream_string(st)
  plot__plot_shipout(plot, options, output_file~)
}

///|
/// Function $mandelbrot displays the Mandelbrot set on the region:
/// xmin < x <xmax, ymin < y <ymax.
fn d_mandelbrot(extra_options : Value) -> Value raise {
  complex_dynamics__plot(extra_options, (st, x, y, m) => {
    let fx = complex_dynamics__float(complex_dynamics__of(x))
    let fy = complex_dynamics__float(complex_dynamics__of(y))
    let mut a = CDRat(Fix(0L))
    let mut b = CDRat(Fix(0L))
    let mut num = m
    for l in 0..<to_int(m) {
      let c = complex_dynamics__mul(a, a)
      let d = complex_dynamics__mul(b, b)
      let e = complex_dynamics__mul(
        complex_dynamics__mul(CDRat(Fix(2L)), a),
        b,
      )
      if complex_dynamics__gt4(complex_dynamics__add(c, d)) {
        num = int(l)
        break
      }
      a = complex_dynamics__add(fx, complex_dynamics__sub(c, d))
      b = complex_dynamics__add(fy, e)
    }
    format(st, "~f ~f ~d~%", [x, y, num]) |> ignore
  })
}

///|
/// Function $julia(x,y) displays the Julia set for the point (x,y) of the
/// complex plane, on the region: xmin < x <xmax, ymin < y <ymax.
fn d_julia(x : Value, y : Value, extra_options : Value) -> Value raise {
  complex_dynamics__plot(extra_options, (st, a0, b0, m) => {
    let cx = complex_dynamics__of(x)
    let cy = complex_dynamics__of(y)
    let mut a = complex_dynamics__float(complex_dynamics__of(a0))
    let mut b = complex_dynamics__float(complex_dynamics__of(b0))
    let mut num = m
    for l in 0..<to_int(m) {
      let c = complex_dynamics__mul(a, a)
      let d = complex_dynamics__mul(b, b)
      let e = complex_dynamics__mul(
        complex_dynamics__mul(CDRat(Fix(2L)), a),
        b,
      )
      if complex_dynamics__gt4(complex_dynamics__add(c, d)) {
        num = int(l)
        break
      }
      a = complex_dynamics__add(cx, complex_dynamics__sub(c, d))
      b = complex_dynamics__add(cy, e)
    }
    format(st, "~f ~f ~d~%", [a0, b0, num]) |> ignore
  })
}

///|
/// (map 'list #'+ l1 l2)
fn complex_dynamics__map_add(l1 : Value, l2 : Value) -> Value raise {
  plotcolors__map2((a, b) => num_add(a, b), l1, l2)
}

///|
/// One Runge-Kutta step of size H from R = (t x1 x2 ...): the new values
/// of the variables (the time is computed by the caller).
fn complex_dynamics__rk_step(fun : Value, r : Value, h : Value) -> Value raise {
  let half = num_div(h, Fix(2L))
  let ap = (r : Value) => mapcar(f => apply(f, r), fun)
  let k1 = ap(r)
  let r1 = cons(
    num_add(car(r), half),
    complex_dynamics__map_add(cdr(r), mapcar(x => num_mul(half, x), k1)),
  )
  let k2 = ap(r1)
  let r2 = cons(
    num_add(car(r), half),
    complex_dynamics__map_add(cdr(r), mapcar(x => num_mul(half, x), k2)),
  )
  let k3 = ap(r2)
  let r3 = cons(
    num_add(car(r), h),
    complex_dynamics__map_add(cdr(r), mapcar(x => num_mul(h, x), k3)),
  )
  let k4 = ap(r3)
  let sixth : Value = Ratio(1N, 6N)
  let third : Value = Ratio(1N, 3N)
  let u = plotcolors__map2(
    (a, b) => num_add(a, b),
    plotcolors__map2(
      (a, b) => num_add(a, b),
      plotcolors__map2(
        (a, b) => num_add(a, b),
        mapcar(x => num_mul(sixth, x), k1),
        mapcar(x => num_mul(third, x), k2),
      ),
      mapcar(x => num_mul(third, x), k3),
    ),
    mapcar(x => num_mul(sixth, x), k4),
  )
  complex_dynamics__map_add(cdr(r), mapcar(x => num_mul(h, x), u))
}

///|
/// Function $rk implements the 4th order Runge-Kutta numerical method.
///  exprs:   an expression or maxima list with n expressions
///  vars:    name of (or list of names of) the independent variable(s)
///  initial: initial value for the variable (or list of initial values)
///  domain:  maxima list with four elements (name of the independent
///           variable, its initial and final values and its increment)
fn d_rk(exprs : Value, vars : Value, initial : Value, domain : Value) -> Value raise {
  let it = mapcar(x => coerce_float(x), cddr(domain))
  let exprs = if d_listp(exprs).truthy() {
    exprs
  } else {
    list2(list1(q_mlist), exprs)
  }
  let initial = if d_listp(initial).truthy() {
    initial
  } else {
    list2(list1(q_mlist), initial)
  }
  let vars = if d_listp(vars).truthy() {
    vars
  } else {
    list2(list1(q_mlist), vars)
  }
  for var_ in cdr(vars).iter() {
    if !symbolp(var_) {
      merr("rk: variable name expected; found: ~M", [var_]) |> ignore
    }
  }
  if !symbolp(cadr(domain)) {
    merr("rk: variable name expected; found: ~M", [cadr(domain)]) |> ignore
  }
  let vars = append(list2(list1(q_mlist), cadr(domain)), cdr(vars))
  let mut r = cons(car(it), mapcar(x => coerce_float(x), cdr(initial)))
  let fun = mapcar(x => coerce_float_fun(x, list1(vars)), cdr(exprs))
  let d = num_div(num_sub(cadr(it), car(it)), caddr(it))
  let mut traj = list1(cons(list1(q_mlist), r))
  let mut m = 1
  while !num_gt(int(m), d) {
    // (ignore-errors ...): an error leaves r as it was
    match errset(() => {
      let xs = complex_dynamics__rk_step(fun, r, caddr(it))
      cons(num_add(car(it), num_mul(int(m), caddr(it))), xs)
    }) {
      Some(nr) => {
        r = nr
        traj = cons(cons(list1(q_mlist), r), traj)
      }
      None => ()
    }
    m = m + 1
  }
  if num_lt(car(r), cadr(it)) {
    let s = num_sub(cadr(it), car(r))
    match errset(() => cons(cadr(it), complex_dynamics__rk_step(fun, r, s))) {
      Some(nr) => {
        r = nr
        traj = cons(cons(list1(q_mlist), r), traj)
      }
      None => ()
    }
  }
  cons(list1(q_mlist), nreverse(traj))
}
