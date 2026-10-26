// Port of src/plot.lisp (part 1): plot objects, plot options, mesh
// utilities, transformations and COERCE-FLOAT-FUN.
//
// Each plot is described by an object whose class depends on the graphic
// program used to visualize it (option "plot_format"): gnuplot-plot,
// xmaxima-plot and geomview-plot.  The CLOS classes and the generic
// functions PLOT-PREAMBLE, PLOT2D-COMMAND, PLOT3D-COMMAND and PLOT-SHIPOUT
// are a MoonBit struct and dispatching functions here; the methods are in
// gnuplot_def.mbt, xmaxima_def.mbt and geomview_def.mbt.

///|
priv enum PlotClass {
  GnuplotPlot
  XmaximaPlot
  GeomviewPlot
}

///|
/// An instance of one of the plot classes, with its slots DATA and PIPE.
priv struct PlotObj {
  cls : PlotClass
  mut data : String
  mut pipe : Bool
}

///|
/// (make-instance class)
fn plot__make_instance(cls : PlotClass) -> PlotObj {
  { cls, data: "", pipe: false }
}

///|
/// Generic function PLOT-PREAMBLE: plots the preamble for a plot.
fn plot__plot_preamble(plot : PlotObj, options : Value) -> Value raise {
  match plot.cls {
    GnuplotPlot => gnuplot_def__plot_preamble(plot, options)
    XmaximaPlot => xmaxima_def__plot_preamble(plot, options)
    GeomviewPlot => geomview_def__plot_preamble(plot, options)
  }
}

///|
/// Generic function PLOT2D-COMMAND: writes the command that creates a plot.
fn plot__plot2d_command(
  plot : PlotObj,
  fun : Value,
  options : Value,
  range : Value,
) -> Unit raise {
  match plot.cls {
    GnuplotPlot => gnuplot_def__plot2d_command(plot, fun, options, range)
    XmaximaPlot => xmaxima_def__plot2d_command(plot, fun, options, range)
    GeomviewPlot =>
      raise LispError::SimpleError(
        "There is no applicable method for the generic function PLOT2D-COMMAND when called with arguments of class GEOMVIEW-PLOT",
      )
  }
}

///|
/// Generic function PLOT3D-COMMAND: writes the command that creates a plot.
fn plot__plot3d_command(
  plot : PlotObj,
  functions : Value,
  options : Value,
  titles : Value,
) -> Unit raise {
  match plot.cls {
    GnuplotPlot => gnuplot_def__plot3d_command(plot, functions, options, titles)
    XmaximaPlot => xmaxima_def__plot3d_command(plot, functions, options, titles)
    GeomviewPlot =>
      geomview_def__plot3d_command(plot, functions, options, titles)
  }
}

///|
/// Generic function PLOT-SHIPOUT: sends the plot commands to the graphic
/// program.
fn plot__plot_shipout(
  plot : PlotObj,
  options : Value,
  output_file? : Value = Nil,
) -> Value raise {
  match plot.cls {
    GnuplotPlot => gnuplot_def__plot_shipout(plot, options, output_file)
    XmaximaPlot => xmaxima_def__plot_shipout(plot, options, output_file)
    GeomviewPlot => geomview_def__plot_shipout(plot, options, output_file)
  }
}

// ---------------------------------------------------------------------------
// Property-list places

///|
/// (setf (getf plist key) val): destructive when KEY is present; otherwise
/// the new pair is consed in front.  Returns the (possibly new) plist.
fn plot__putf(plist : Value, key : Value, val : Value) -> Value {
  let mut p = plist
  while p is Cons(_) {
    if eq(car(p), key) {
      rplaca(cdr(p), val) |> ignore
      return plist
    }
    p = cddr(p)
  }
  cons(key, cons(val, plist))
}

///|
/// (remf plist key): the (possibly new) plist and whether KEY was found.
fn plot__remf(plist : Value, key : Value) -> (Value, Bool) {
  if !(plist is Cons(_)) {
    return (plist, false)
  }
  if eq(car(plist), key) {
    return (cddr(plist), true)
  }
  let mut prev = cdr(plist)
  let mut p = cddr(plist)
  while p is Cons(_) {
    if eq(car(p), key) {
      rplacd(prev, cddr(p)) |> ignore
      return (plist, true)
    }
    prev = cdr(p)
    p = cddr(p)
  }
  (plist, false)
}

///|
/// A Lisp predicate function object wrapping F.
fn plot__pred(name : String, f : (Value) -> Bool raise) -> Value {
  lfunc(name, args => lbool(f(arg(args, 0))))
}

///|
/// CL's #'STRING used as a predicate: true for strings, symbols and
/// characters, a type error for anything else.
fn plot__string_designator(x : Value) -> Value raise {
  match x {
    Str(_) | Sym(_) | Nil | Char(_) => string(x)
    _ =>
      raise LispError::SimpleError(
        prin1_to_string(x) + " is not a string designator.",
      )
  }
}

///|
/// (pathname-directory file) is not NIL: the name has a directory part.
fn plot__has_directory(file : Value) -> Bool {
  lstring(file).contains("/")
}

// ---------------------------------------------------------------------------
// Convenience functions used to check values of plot arguments and options

///|
/// For function defmvar :setting-predicate.  Checks that the argument is a
/// string.  The second value is the message to use when the argument is not
/// a string.
fn string_predicate(val : Value) -> (Value, Value) raise {
  (lbool(stringp(val)), Str("must be a string"))
}

///|
fn d_join(x : Value, y : Value) -> Value raise {
  if d_listp(x).truthy() && d_listp(y).truthy() {
    let acc = Collector::new()
    let mut a = cdr(x)
    let mut b = cdr(y)
    while a is Cons(_) && b is Cons(_) {
      acc.add(car(a))
      acc.add(car(b))
      a = cdr(a)
      b = cdr(b)
    }
    cons(list1(q_mlist), acc.result())
  } else {
    merr("join: both arguments must be lists.", [])
  }
}

///|
/// $plot_realpart option is false by default but *plot-realpart* is true
/// because coerce-float-fun is used outside of plot package too.
fn maybe_realpart(x : Value) -> Value raise {
  if symval(q_ear_plot_realpart).truthy() {
    d_realpart(x)
  } else {
    let ri = trisplit(x)
    let re = car(ri)
    let im = cdr(ri)
    if zerop1(im).truthy() {
      re
    } else {
      Nil
    }
  }
}

// ---------------------------------------------------------------------------
// PLOT OPTIONS PARSING

///|
fn d_get_plot_option(name? : Value = Nil, n? : Value = Nil) -> Value raise {
  let mut options : Value = Nil
  // Converts the options property list into a Maxima list
  let mut l = copy_tree(symval(q_ear_plot_options))
  while l is Cons(_) {
    let key = first(l)
    let value = second(l)
    if value is Cons(_) {
      options = cons(cons(list1(q_mlist), cons(key, value)), options)
    } else {
      options = cons(list3(list1(q_mlist), key, value), options)
    }
    l = cddr(l)
  }
  let options = cons(list1(q_mlist), nreverse(options))
  if name.truthy() {
    let value = find_if(v => eql(second(v), name), cdr(options))
    if n.truthy() {
      nth(to_int(n), value)
    } else {
      value
    }
  } else {
    options
  }
}

///|
fn quote_strings(opt : Value) -> Value raise {
  if atom(opt) {
    if stringp(opt) {
      format(Nil, "~s", [opt])
    } else {
      opt
    }
  } else {
    cons(quote_strings(car(opt)), quote_strings(cdr(opt)))
  }
}

///|
fn get_plot_option_string(option : Value, index? : Value = Fix(1L)) -> Value raise {
  let val = d_get_plot_option(name=option, n=Fix(2L))
  let val_list = if d_listp(val).truthy() { cdr(val) } else { list1(val) }
  ensure_string(
    nth(to_int(num_mod(num_sub(index, Fix(1L)), int(length(val_list)))), val_list),
  )
}

///|
fn d_set_plot_option(value : Value) -> Value raise {
  set(
    q_ear_plot_options,
    plot_options_parser(value, symval(q_ear_plot_options)),
  )
  |> ignore
  d_get_plot_option()
}

///|
/// The quoted default options of $RESET_PLOT_OPTIONS: one literal list,
/// shared (and modified by set_plot_option) as in the Lisp code.
let plot__default_options : Ref[Value] = Ref(Nil)

///|
/// Sets the default plotting options.
fn d_reset_plot_options() -> Value raise {
  if plot__default_options.val is Nil {
    plot__default_options.val = lread(
      "($grid (30 30) $color ($blue $red $green $magenta $black $cyan) $gnuplot_term $default $mesh_lines_color \"dimgray\" $palette $default $gnuplot_preamble \"\" $background_color \"white\" $point_type ($bullet mbox $triangle $plus $times $asterisk) $adapt_depth 5 $nticks 29 $axes t $run_viewer t $plot_format $gnuplot_pipes)",
    )
  }
  set(q_ear_plot_options, plot__default_options.val) |> ignore
  t
}

///|
/// Removes option "name" from current plotting options
fn d_remove_plot_option(name : Value) -> Value raise {
  let (pl, found) = plot__remf(symval(q_ear_plot_options), name)
  set(q_ear_plot_options, pl) |> ignore
  lbool(found)
}

///|
fn get_gnuplot_term(term : Value) -> Value raise {
  let sterm = string_downcase(lstring(ensure_string(term)))
  let pos = string_search(" ", sterm)
  if pos >= 0 {
    subseq(Str(sterm), 0, end=pos)
  } else {
    Str(sterm)
  }
}

// end of PLOT OPTIONS parsing functions

///|
fn print_pt1(f : Value, str : Value) -> Value raise {
  if floatp(f) {
    format(str, "~,,,,,,'eg ", [f])
  } else {
    format(str, "~a ", [symval(q_ear_missing_data_indicator)])
  }
}

///|
/// macro z-pt: (aref ar (+ 2 (* i 3)))
fn z_pt(ar : Value, i : Value) -> Value raise {
  aref1(ar, 2 + to_int(i) * 3)
}

///|
/// macro y-pt: (aref ar (1+ (* i 3)))
fn y_pt(ar : Value, i : Value) -> Value raise {
  aref1(ar, 1 + to_int(i) * 3)
}

///|
/// macro x-pt: (aref ar (* i 3))
fn x_pt(ar : Value, i : Value) -> Value raise {
  aref1(ar, to_int(i) * 3)
}

///|
/// macro rot: (aref m (+ i (* 3 j)))
fn rot(m : Value, i : Value, j : Value) -> Value raise {
  aref1(m, to_int(i) + 3 * to_int(j))
}

///|
/// macro print-pt: (print-pt1 f $pstream)
fn print_pt(f : Value) -> Value raise {
  print_pt1(f, symval(q_d_pstream))
}

///|
/// macro make-polygon: (list '($polygon) a b)
fn make_polygon(a : Value, b : Value) -> Value raise {
  list3(list1(q_d_polygon), a, b)
}

///|
/// (vertices-matrix points nxint nyint). Given a vector 'points' and two
/// integers nxint and nyint, it returns a matrix in which each row has the
/// indices of the points for a given value of y in the mesh, or T if the
/// value of z doesn't exist at the corresponding mesh point.  'points' is a
/// sequence x0 y0 y0 x1 y1 z1 ... with the coordinates of all the points in
/// the mesh; the indices in the returned matrix are the positions of the
/// corresponding points in the list of valid points (excluding those whose z
/// coordinate is not a number).
fn vertices_matrix(points : Value, nxint : Value, nyint : Value) -> Value raise {
  let nx = to_int(nxint)
  let ny = to_int(nyint)
  let mut vertices : Value = Nil
  let mut k = 0
  for j in 0..=ny {
    let mut row : Value = Nil
    let r = 3 * j * (nx + 1)
    let mut i = 0
    while i <= 3 * nx {
      let mut pt : Value = Nil
      for n in 0..<3 {
        pt = cons(elt(points, r + i + n), pt)
      }
      if length(remove(t, pt)) == 3 {
        row = cons(int(k), row)
        k = k + 1
      } else {
        row = cons(t, row)
      }
      i = i + 3
    }
    vertices = cons(reverse(row), vertices)
  }
  reverse(vertices)
}

///|
/// (polygons matrix). Creates a list of polygons for rectangular mesh
/// defined by 'matrix'.  Each sublist in matrix has non-negative integers,
/// or T, identifying the points in each row of the mesh.  The list returned
/// will have sublists of 3 or 4 elements that label the vertices of a
/// triangle or a quadrilateral.
fn polygons(matrix : Value) -> Value raise {
  let mut pols : Value = Nil
  let rows = length(matrix)
  let cols = length(first(matrix))
  for j in 0..<(rows - 1) {
    for i in 0..<(cols - 1) {
      let mut pol : Value = Nil
      pol = cons(nth(i, nth(j + 1, matrix)), pol)
      pol = cons(nth(i + 1, nth(j + 1, matrix)), pol)
      pol = cons(nth(i + 1, nth(j, matrix)), pol)
      pol = cons(nth(i, nth(j, matrix)), pol)
      pol = remove(t, pol)
      if length(pol) > 2 {
        pols = cons(pol, pols)
      }
    }
  }
  reverse(pols)
}

///|
/// The flonum declarations of DRAW3D and friends: SBCL signals a type error
/// when a non-float is bound to a variable declared FLONUM.
fn plot__check_flonum(v : Value, name : String) -> Unit raise {
  if !(v is Flo(_)) {
    raise LispError::SimpleError(
      "The value\n  " +
      prin1_to_string(v) +
      "\nis not of type\n  DOUBLE-FLOAT\nwhen binding " +
      name,
    )
  }
}

///|
fn draw3d(
  f : Value,
  minx : Value,
  maxx : Value,
  miny : Value,
  maxy : Value,
  nxint : Value,
  nyint : Value,
) -> (Value, Value) raise {
  let epsx = num_div(num_sub(maxx, minx), nxint)
  plot__check_flonum(epsx, "EPSX")
  let epsy = num_div(num_sub(maxy, miny), nyint)
  plot__check_flonum(epsy, "EPSY")
  let nx = to_int(nxint)
  let ny = to_int(nyint)
  let points = make_array([3 * (nx + 1) * (ny + 1)], fill=0)
  let mut z_count = 0
  for j in 0..=ny {
    let y = num_add(miny, num_mul(int(j), epsy))
    for i in 0..=nx {
      let x = num_add(minx, num_mul(int(i), epsx))
      let z = funcall(f, [x, y])
      vector_push_extend(x, points) |> ignore
      vector_push_extend(y, points) |> ignore
      vector_push_extend(z, points) |> ignore
      if floatp(z) {
        z_count = z_count + 1
      }
    }
  }
  if z_count < 1 {
    merr("plot3d: nothing to plot.~%", []) |> ignore
  }
  (points, int(z_count))
}

///|
/// make-grid-vertices
/// Creates an array that describes a rectangular grid with nx intervals in
/// the x direction and ny intervals in the y direction.  Such grid is then
/// formed by nx*ny rectangles.  Each rectangle is defined by four points and
/// a value of zero, which will be later replaced by the z value
/// corresponding to that rectangle.
///
/// Thus, each sequence of 5 integers in the resulting array describe a
/// rectangle in the grid. For instance, 0 3 4 1 0 corresponds to the the
/// rectangle with vertices at the points with indices 0 3 4 and 1.  The
/// points on the top row of the grid have indices: 0 1 2 ... nx and the
/// points in the j'th row from the top (counting from 0) are: j j+1 j+2 ...
/// j+nx.  The order of the points given for each rectangle gives the correct
/// sequence when the boundary of the rectangle is traversed in the
/// clockwise direction.
fn make_grid_vertices(nx : Value, ny : Value) -> Value raise {
  let nxv = to_int(nx)
  let nyv = to_int(ny)
  let len = 5 * nxv * nyv
  let tem = make_array([15 + len], initial=Fix(0L), fill=len)
  let mut m = nxv
  let nxpt = nxv + 1
  let mut i = 0
  let mut k = 0
  while k < len {
    aset1(tem, k, int(i)) |> ignore
    k = k + 1
    aset1(tem, k, int(nxpt + i)) |> ignore
    k = k + 1
    i = i + 1
    aset1(tem, k, int(nxpt + i)) |> ignore
    k = k + 1
    aset1(tem, k, int(i)) |> ignore
    k = k + 1
    aset1(tem, k, Fix(0L)) |> ignore // place for max
    m = m - 1
    if m == 0 {
      m = nxv
      i = i + 1
    }
    k = k + 1
  }
  tem
}

///|
/// $rotation1
/// The argument phi is elevation and th is azimuth. This function returns
/// the matrix of a rotation in the positive direction (from x to y) along
/// the z axis, with an angle equal to the azimuth, followed by a negative
/// rotation (from x to z) along the new y axis, with an angle equal to the
/// elevation. Even though it is declared as a Maxima function, it can not
/// be called with symbolic arguments; only numeric arguments.
fn d_rotation1(phi : Value, th : Value) -> Value raise {
  let sinph = lsin(phi)
  let cosph = lcos(phi)
  let sinth = lsin(th)
  let costh = lcos(th)
  list4(
    list2(q_d_matrix, q_simp),
    list([
      list2(q_mlist, q_simp),
      num_mul(cosph, costh),
      num_mul(num_mul(Flo(-1.0), cosph), sinth),
      sinph,
    ]),
    list([list2(q_mlist, q_simp), sinth, costh, Flo(0.0)]),
    list([
      list2(q_mlist, q_simp),
      num_neg(num_mul(sinph, costh)),
      num_mul(sinph, sinth),
      cosph,
    ]),
  )
}

///|
fn d_get_range(pts : Value, k : Value) -> Value raise {
  let mut max : Value = Flo(-1.7976931348623157e308)
  let mut min : Value = Flo(1.7976931348623157e308)
  let mut i = to_int(k)
  let n = length(pts)
  while i < n {
    let z = aref1(pts, i)
    if num_lt(z, min) {
      min = z
    }
    if num_gt(z, max) {
      max = z
    }
    i = i + 3
  }
  list3(min, max, num_sub(max, min))
}

///|
/// (assert (typep pts '(vector t)))
fn plot__assert_vector(pts : Value) -> Unit raise {
  if !vectorp(pts) {
    raise LispError::SimpleError(
      "The assertion (TYPEP PTS '(VECTOR T)) failed.",
    )
  }
}

///|
fn d_polar_to_xy(pts : Value) -> Value raise {
  plot__assert_vector(pts)
  let n = length(pts)
  let mut i = 0
  while i < n {
    let r = elt(pts, i)
    let th = elt(pts, i + 1)
    aset1(pts, i, num_mul(r, lcos(th))) |> ignore
    aset1(pts, i + 1, num_mul(r, lsin(th))) |> ignore
    i = i + 3
  }
  Nil
}

///|
/// Transformation from spherical coordinates to rectangular coordinates, to
/// be used in plot3d. Example of its use:
/// plot3d (expr, [th, 0, %pi], [ph, 0, 2*%pi], [transform_xy, spherical_to_xyz])
/// where expr gives the value of r in terms of the inclination (th) and
/// azimuth (ph).
fn d_spherical_to_xyz(pts : Value) -> Value raise {
  plot__assert_vector(pts)
  let n = length(pts)
  let mut i = 0
  while i < n {
    if floatp(elt(pts, i + 2)) {
      let th = elt(pts, i)
      let ph = elt(pts, i + 1)
      let r = elt(pts, i + 2)
      aset1(pts, i, num_mul(num_mul(r, lsin(th)), lcos(ph))) |> ignore
      aset1(pts, i + 1, num_mul(num_mul(r, lsin(th)), lsin(ph))) |> ignore
      aset1(pts, i + 2, num_mul(r, lcos(th))) |> ignore
    } else {
      aset1(pts, i, t) |> ignore
      aset1(pts, i + 1, t) |> ignore
    }
    i = i + 3
  }
  Nil
}

///|
/// return a function suitable for the transform function in plot3d.  FX,
/// FY, and FZ are functions of three arguments.  This function needs to be
/// fixed for the case when coerce-float-fun returns T instead of a
/// floating-point value.
fn d_make_transform(lvars : Value, fx : Value, fy : Value, fz : Value) -> Value raise {
  let fx = coerce_float_fun(fx, list2(lvars, Str("make_transform")))
  let fy = coerce_float_fun(fy, list2(lvars, Str("make_transform")))
  let fz = coerce_float_fun(fz, list2(lvars, Str("make_transform")))
  let sym_ = gensym(prefix="transform")
  defun(sym_, args => {
    let pts = arg(args, 0)
    let n = length(pts)
    let mut i = 0
    while i < n {
      let x1 = elt(pts, i)
      let x2 = elt(pts, i + 1)
      let x3 = elt(pts, i + 2)
      plot__check_flonum(x1, "X1")
      plot__check_flonum(x2, "X2")
      plot__check_flonum(x3, "X3")
      aset1(pts, i, funcall(fx, [x1, x2, x3])) |> ignore
      aset1(pts, i + 1, funcall(fy, [x1, x2, x3])) |> ignore
      aset1(pts, i + 2, funcall(fz, [x1, x2, x3])) |> ignore
      i = i + 3
    }
    Nil
  })
  sym_
}

///|
fn p_coerce_float_fun_check_args(actuals : Value, nargs : Value) -> Value raise {
  if !num_eq(int(length(actuals)), nargs) {
    raise LispError::SimpleError(
      "invalid number of arguments: " + length(actuals).to_string(),
    )
  }
  Nil
}

///|
/// (funcall float-fun x) for float-fun $float or $bfloat.
fn plot__float_fun(float_fun : Value, x : Value) -> Value raise {
  if eq(float_fun, q_d_float) {
    d_float(x)
  } else if eq(float_fun, q_d_bfloat) {
    d_bfloat(x)
  } else {
    funcall(float_fun, [x])
  }
}

///|
/// Return value is a Lisp function which evaluates EXPR to a float.
/// COERCE-FLOAT-FUN always returns a function and never returns a symbol,
/// even if EXPR is a symbol.
///
/// Following cases are recognized:
/// EXPR is a symbol
///   name of a Lisp function
///   name of a Maxima function
///   name of a DEFMSPEC function
///   name of a Maxima macro
///   a string which is the name of a Maxima operator (e.g., "!")
///   name of a simplifying function
/// EXPR is a Maxima lambda expression
/// EXPR is a general Maxima expression
///
/// %COERCE-FLOAT-FUN is the main internal routine for this.
/// COERCE-FLOAT-FUN is the user interface for creating a function that
/// returns floats.  COERCE-BFLOAT-FUN is the same, except bfloats are
/// returned.
fn p_coerce_float_fun(float_fun : Value, expr : Value, rest_ : Value) -> Value raise {
  let (lvars, fname) : (Value, Value) = match length(rest_) {
    0 => (Nil, Str("coerce-float-fun"))
    1 => (first(rest_), Str("coerce-float-fun"))
    2 => (first(rest_), second(rest_))
    _ => {
      merr("coerce-float-fun: too many arguments given.", []) |> ignore
      (Nil, Nil)
    }
  }
  if stringp(expr) && getopr0(expr).truthy() {
    // expr is a string which names an operator
    // (e.g. "!" "+" or a user-defined operator)
    let a = if lvars.truthy() { lvars } else { list2(list1(q_mlist), gensym()) }
    return p_coerce_float_fun(
      float_fun,
      list3(list1(q_d_apply), getopr0(expr), a),
      list2(a, fname),
    )
  }
  if symbolp(expr) &&
    !member(expr, lvars).truthy() &&
    !d_constantp(expr).truthy() {
    if fboundp(expr) {
      let args = if lvars.truthy() { cdr(lvars) } else { list1(gensym()) }
      return coerce_lisp_function_or_lisp_lambda(args, expr, float_fun~)
    }
    // expr is name of a Maxima function defined by := or define
    if mget(expr, q_mexpr).truthy() {
      let mexpr = mget(expr, q_mexpr)
      let args = cdr(second(mexpr))
      return coerce_maxima_function_or_maxima_lambda(args, expr, float_fun~)
    }
    if
      // expr is the name of a function defined by defmspec
      get(expr, q_mfexpr_star).truthy() ||
      // expr is the name of a Maxima macro defined by ::=
      mget(expr, q_mmacro).truthy() ||
      // expr is the name of a simplifying function, and the simplification
      // property is associated with the noun form
      get(d_nounify(expr), q_operators).truthy() ||
      // expr is the name of a simplifying function, and the simplification
      // property is associated with the verb form
      get(d_verbify(expr), q_operators).truthy() {
      let a = if lvars.truthy() { lvars } else { list2(list1(q_mlist), gensym()) }
      return p_coerce_float_fun(
        float_fun,
        list3(list1(q_d_apply), expr, a),
        list2(a, fname),
      )
    }
    return merror(Str("~a: unknown function: ~M"), list2(fname, expr))
  }
  if expr is Cons(_) && eq(caar(expr), q_lambda) {
    let args = cdr(second(expr))
    return coerce_maxima_function_or_maxima_lambda(args, expr, float_fun~)
  }
  let vars = cdr(
    if lvars.truthy() {
      lvars
    } else {
      d_sort(with_special(q_d_listconstvars, Nil, () => d_listofvars(expr)))
    },
  )
  let subscripted = remove_if(v => atom(v), vars)
  let symbols = remove_if(v => !atom(v), vars)
  let nargs = int(length(vars))
  // We don't want to set $numer to T when coercing to a bigfloat.  By doing
  // so, things like log(400)^400 get converted to double-floats, which
  // causes a double-float overflow.  But the whole point of coercing to
  // bfloat is to use bfloats, not doubles.
  let numer = lbool(!eq(float_fun, q_d_bfloat))
  // Catch any errors from evaluating the function.  We're assuming that if
  // an error is caught, the result is not a number.  We also assume that
  // for such errors, it's because the function is not defined there, not
  // because of some other maxima error.
  let evaluate = () => with_specials(
    [(q_d_ratprint, Nil), (q_d_numer, numer), (q_ear_nounsflag, t)],
    () => {
      let result = errcatch(
        lfunc("coerce-float-fun-evaluate", _ => plot__float_fun(
          float_fun,
          maybe_realpart(meval(expr)),
        )),
      )
      if result.truthy() {
        car(result)
      } else {
        t
      }
    },
  )
  if subscripted is Nil {
    lfunc("coerce-float-fun", actuals => {
      let actuals = list(actuals)
      p_coerce_float_fun_check_args(actuals, nargs) |> ignore
      progv(vars, actuals, evaluate)
    })
  } else {
    // A subscripted variable is not a symbol and cannot be bound, so it is
    // MSET around the call and its old value put back.
    lfunc("coerce-float-fun", actuals => {
      let actuals = list(actuals)
      p_coerce_float_fun_check_args(actuals, nargs) |> ignore
      let saved = mapcar(v => meval(v), subscripted)
      let vals = Collector::new()
      let mut vs = vars
      let mut as_ = actuals
      while vs is Cons(_) && as_ is Cons(_) {
        let v = car(vs)
        if atom(v) {
          vals.add(car(as_))
        } else {
          mset(v, car(as_)) |> ignore
        }
        vs = cdr(vs)
        as_ = cdr(as_)
      }
      // The restore has to run even when the evaluation exits non-locally,
      // or the caller's variable is left holding whatever this happened to
      // be probing at.
      defer {
        let mut s = saved
        for v in subscripted.iter() {
          mset(v, car(s)) |> ignore
          s = cdr(s)
        }
      }
      progv(symbols, vals.result(), evaluate)
    })
  }
}

///|
/// coerce-float-fun must be given an expression and one or two other
/// optional arguments: a Maxima list of variables on which that expression
/// depends and string that will identify the name of the responsible
/// function when reporting errors.
fn coerce_float_fun(expr : Value, rest_ : Value) -> Value raise {
  let (lvars, fname) = plot__coerce_args("coerce-float-fun", rest_)
  p_coerce_float_fun(q_d_float, expr, list2(lvars, fname))
}

///|
/// coerce-bfloat-fun must be given an expression and one or two other
/// optional arguments: a Maxima list of variables on which that expression
/// depends and string that will identify the name of the responsible
/// function when reporting errors.
fn coerce_bfloat_fun(expr : Value, rest_ : Value) -> Value raise {
  let (lvars, fname) = plot__coerce_args("coerce-bfloat-fun", rest_)
  p_coerce_float_fun(q_d_bfloat, expr, list2(lvars, fname))
}

///|
/// The argument checks of COERCE-FLOAT-FUN and COERCE-BFLOAT-FUN.
fn plot__coerce_args(who : String, rest_ : Value) -> (Value, Value) raise {
  match length(rest_) {
    0 => (Nil, Str(who))
    1 =>
      if stringp(first(rest_)) {
        (Nil, first(rest_))
      } else if d_listp(first(rest_)).truthy() {
        (first(rest_), Str("coerce-float-fun"))
      } else {
        merr(who + ": expecting a Maxima list, found: ~M", [first(rest_)])
        |> ignore
        (Nil, Nil)
      }
    2 => {
      let lvars = if d_listp(first(rest_)).truthy() {
        first(rest_)
      } else {
        merr(who + ": expecting a Maxima list, found: ~M", [first(rest_)])
      }
      let fname = if stringp(second(rest_)) {
        second(rest_)
      } else {
        merr(who + ": expecting a string, found: ~M", [second(rest_)])
      }
      (lvars, fname)
    }
    _ => {
      merr(who + ": two many arguments given.", []) |> ignore
      (Nil, Nil)
    }
  }
}

///|
/// A function of exactly NARGS arguments (a compiled LAMBDA with that many
/// required parameters): other argument counts are an error.
fn plot__check_lambda_args(actuals : Array[Value], nargs : Int) -> Unit raise {
  if actuals.length() != nargs {
    raise LispError::SimpleError(
      "invalid number of arguments: " + actuals.length().to_string(),
    )
  }
}

///|
fn coerce_maxima_function_or_maxima_lambda(
  args : Value,
  expr : Value,
  float_fun? : Value = q_d_float,
) -> Value raise {
  let nargs = length(args)
  lfunc("coerce-maxima-function", actuals => {
    plot__check_lambda_args(actuals, nargs)
    with_specials(
      [(q_d_ratprint, Nil), (q_d_numer, t), (q_ear_nounsflag, t)],
      () => {
        // Just always try to convert the result with float-fun, which
        // handles things like $%pi.  See also BUG
        // https://sourceforge.net/p/maxima/bugs/1795/
        let result = errcatch(
          lfunc("coerce-maxima-function-evaluate", _ => plot__float_fun(
            float_fun,
            maybe_realpart(mapply(expr, list(actuals), t)),
          )),
        )
        if result.truthy() {
          car(result)
        } else {
          t
        }
      },
    )
  })
}

///|
/// Same as above, but call APPLY instead of MAPPLY.
fn coerce_lisp_function_or_lisp_lambda(
  args : Value,
  expr : Value,
  float_fun? : Value = q_d_float,
) -> Value raise {
  let nargs = length(args)
  lfunc("coerce-lisp-function", actuals => {
    plot__check_lambda_args(actuals, nargs)
    with_specials(
      [(q_d_ratprint, Nil), (q_d_numer, t), (q_ear_nounsflag, t)],
      () => {
        let result = maybe_realpart(apply(expr, list(actuals)))
        // Always use float-fun.  See comment for
        // coerce-maxima-function-or-maxima-lambda above.
        plot__float_fun(float_fun, result)
      },
    )
  })
}

///|
/// macro zval: (aref points (+ 2 (* 3 (aref verts i))))
fn zval(points : Value, verts : Value, i : Value) -> Value raise {
  aref1(points, 2 + 3 * to_int(aref1(verts, to_int(i))))
}

///|
/// sort the edges array so that drawing the edges will happen from the back
/// towards the front.  The if n==4 the edges array coming in looks like
/// v1 v2 v3 v4 0 w1 w2 w3 w4 0 ...  where vi,wi are indices pointint into
/// the points array specifying a point in 3 space.  After the sorting is
/// done, the 0 is filled in with the vertex which is closer to us (ie
/// highest z component after rotating towards the user) and this is then
/// they are sorted in groups of 5.
fn sort_ngons(points : Value, edges : Value, n : Value) -> Value raise {
  let nv = to_int(n)
  let leng = length(edges)
  let new = make_array([leng], initial=Fix(0L))
  let n1 = nv - 1
  let lis = Collector::new()
  let mut i0 = 0
  while i0 < leng {
    let mut i = i0
    let mut at : Value = Fix(0L)
    let mut z = zval(points, edges, int(i))
    i = i + 1
    for _ in 0..<n1 {
      let z1 = zval(points, edges, int(i))
      if num_gt(z1, z) {
        z = z1
        at = aref1(edges, i)
      }
      i = i + 1
    }
    aset1(edges, i, at) |> ignore
    lis.add(cons(z, int(i0)))
    i0 = i0 + (nv + 1)
  }
  let sorted = sort_list(lis.result(), (a, b) => alphalessp(car(a), car(b))
    .truthy())
  let mut i = 0
  for v in sorted.iter() {
    let mut j = to_int(cdr(v))
    for _ in 0..=nv {
      aset1(new, i, aref1(edges, j)) |> ignore
      i = i + 1
      j = j + 1
    }
  }
  copy_array_portion(edges, new, Fix(0L), Fix(0L), int(length(edges)))
}

///|
fn copy_array_portion(
  ar1 : Value,
  ar2 : Value,
  i1 : Value,
  i2 : Value,
  n1 : Value,
) -> Value raise {
  let mut i1 = to_int(i1)
  let mut i2 = to_int(i2)
  let mut n1 = to_int(n1)
  while {
    n1 = n1 - 1
    n1 >= 0
  } {
    aset1(ar1, i1, aref1(ar2, i2)) |> ignore
    i1 = i1 + 1
    i2 = i2 + 1
  }
  Nil
}

///|
/// (array-element-type v): only arrays have one.
fn plot__check_array(v : Value) -> Unit raise {
  if !(v is Vec(_)) {
    raise LispError::SimpleError(
      "The value\n  " + prin1_to_string(v) + "\nis not of type\n  ARRAY",
    )
  }
}

///|
fn d_concat_polygons(pl1 : Value, pl2 : Value) -> Value raise {
  let acc = Collector::new()
  let mut v1 = pl1
  let mut w1 = pl2
  while v1 is Cons(_) && w1 is Cons(_) {
    let v = car(v1)
    let l = length(v) + length(car(w1))
    plot__check_array(v)
    acc.add(make_array([l], fill=l))
    v1 = cdr(v1)
    w1 = cdr(w1)
  }
  let new = acc.result()
  let new = make_polygon(first(new), second(new))
  // polygon-pts is the second and polygon-edges the third element
  copy_array_portion(
    second(pl1),
    second(new),
    Fix(0L),
    Fix(0L),
    int(length(second(pl1))),
  )
  |> ignore
  copy_array_portion(
    second(pl2),
    second(new),
    int(length(second(pl1))),
    Fix(0L),
    int(length(second(pl2))),
  )
  |> ignore
  copy_array_portion(
    third(pl1),
    third(new),
    Fix(0L),
    Fix(0L),
    int(length(third(pl1))),
  )
  |> ignore
  let lpts1 = length(second(pl1))
  let ar2 = third(pl2)
  let arnew = third(new)
  let mut i = length(third(pl1))
  for j in 0..<length(third(pl2)) {
    aset1(arnew, i, num_add(int(lpts1), aref1(ar2, j))) |> ignore
    i = i + 1
  }
  Nil
}

///|
fn d_copy_pts(lis : Value, vec : Value, start : Value) -> Value raise {
  if numberp(lis) {
    let lis = if floatp(lis) { lis } else { lfloat(lis) }
    aset1(vec, to_int(start), lis) |> ignore
    num_add(start, Fix(1L))
  } else if lis is Cons(_) {
    d_copy_pts(cdr(lis), vec, d_copy_pts(car(lis), vec, start))
  } else if symbolp(lis) {
    start
  } else {
    merr("copy_pts: unrecognized first argument: ~M", [lis])
  }
}
