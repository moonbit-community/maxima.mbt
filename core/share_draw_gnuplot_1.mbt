// Port of share/draw/gnuplot.lisp (part 1): the Maxima-Gnuplot interface
// of the draw package -- auxiliary functions and the 2d graphic objects.
//
// The graphic object constructors are DEFUN-CHECKED functions in the Lisp
// code (not in the generated contract): each is a private function
// share_draw__<object> plus an argument-count-checking Lisp function cell
// on the object's symbol (installed by init_share_gnuplot), which is what
// make-scene-2d / make-scene-3d APPLY.

///|
let share_draw__most_positive : Value = Flo(1.7976931348623157e308)

///|
let share_draw__most_negative : Value = Flo(-1.7976931348623157e308)

///|
fn extrema_over_finite_floats_list(x : Value) -> (Value, Value) raise {
  let mut xmax = share_draw__most_negative
  let mut xmin = share_draw__most_positive
  for x1 in x.iter() {
    if realp(x1) &&
      !float_inf_p(x1).truthy() &&
      !float_nan_p(x1).truthy() {
      if num_lt(x1, xmin) {
        xmin = x1
      }
      if num_gt(x1, xmax) {
        xmax = x1
      }
    }
  }
  (xmin, xmax)
}

///|
fn finite_real_p(x : Value) -> Value raise {
  lbool(realp(x) && !float_nan_p(x).truthy() && !float_inf_p(x).truthy())
}

///|
fn write_font_type() -> Value raise {
  if lstring(get_option(q_d_font)) == "" &&
    !eql(get_option(q_d_font_size), Fix(10L)) {
    mwarning(list1(Str("Cannot set the gnuplot font size without a font name.")))
    |> ignore
  }
  if eq(get_option(q_d_font), Nil) || lstring(get_option(q_d_font)) == "" {
    Str("")
  } else {
    format(Nil, "font '~a,~a'", [get_option(q_d_font), get_option(q_d_font_size)])
  }
}

///|
/// gnuplot_def.lisp's SEND-GNUPLOT-COMMAND.
fn share_draw__send_gnuplot_command(command : Value) -> Unit raise {
  send_gnuplot_command(command) |> ignore
}

///|
/// One-window multiplot: consecutive calls to draw always plot on the same
/// window.
fn d_multiplot_mode(term : Value) -> Value raise {
  let start = (name : String) => {
    d_multiplot_mode(q_d_none) |> ignore
    share_draw__send_gnuplot_command(
      format(Nil, "set terminal " + name + " dashed ~a~%set multiplot~%", [
        write_font_type(),
      ]),
    )
    set(q_ear_multiplot_is_active, t)
  }
  if eq(term, q_d_screen) {
    start("GNUTERM")
  } else if eq(term, q_d_wxt) {
    start("wxt")
  } else if eq(term, q_d_qt) {
    start("qt")
  } else if eq(term, q_d_windows) {
    start("windows")
  } else if eq(term, q_d_none) {
    share_draw__send_gnuplot_command(
      format(Nil, "unset multiplot~%unset output~%", []),
    )
    set(q_ear_multiplot_is_active, Nil)
  } else {
    merr("draw: ~M is not recognized as a multiplot mode", [term])
  }
}

///|
/// Macro UPDATE-RANGE: ranges are computed automatically unless the user
/// selected them (a list of length 2); nil or a list of length 3 (with a
/// dummy 0) can be changed by the object constructors.
fn share_draw__update_range_of(axi : Value, vmin : Value, vmax : Value) -> Unit raise {
  let cur = get_option(axi)
  match length(cur) {
    0 => share_draw__set_option(axi, list([vmin, vmax, Fix(0L)])) |> ignore
    3 =>
      share_draw__set_option(
        axi,
        list([
          num_min(vmin, first(get_option(axi))),
          num_max(vmax, second(get_option(axi))),
          Fix(0L),
        ]),
      )
      |> ignore
    _ => ()
  }
}

///|
/// macro UPDATE-RANGE (arguments evaluated).
fn update_range(axi : Value, vmin : Value, vmax : Value) -> Value raise {
  share_draw__update_range_of(axi, vmin, vmax)
  get_option(axi)
}

///|
/// macro CHECK-EXTREMES-X: reads and assigns the caller's XX, XMIN, XMAX;
/// expanded inline (ShareDrawExt::x).
fn check_extremes_x() -> Value raise {
  share_draw__inline_macro("CHECK-EXTREMES-X")
}

///|
/// macro CHECK-EXTREMES-Y: expanded inline (ShareDrawExt::y).
fn check_extremes_y() -> Value raise {
  share_draw__inline_macro("CHECK-EXTREMES-Y")
}

///|
/// macro CHECK-EXTREMES-Z: expanded inline (ShareDrawExt::z).
fn check_extremes_z() -> Value raise {
  share_draw__inline_macro("CHECK-EXTREMES-Z")
}

///|
/// macro BUILD-POLYGON: pushes onto the local PTS of REGION, where it is
/// expanded inline.
fn build_polygon(coord : Value) -> Value raise {
  ignore(coord)
  share_draw__inline_macro("BUILD-POLYGON")
}

///|
/// macro CHECK-TUBE-EXTREME: assigns local variables of TUBE, where it is
/// expanded inline.
fn check_tube_extreme(
  ex : Value,
  cx : Value,
  cy : Value,
  cz : Value,
  circ : Value,
) -> Value raise {
  ignore((ex, cx, cy, cz, circ))
  share_draw__inline_macro("CHECK-TUBE-EXTREME")
}

///|
/// macro WRITE-PALETTE-CODE.
fn write_palette_code() -> Value raise {
  share_draw__write_palette_code()
}

///|
/// macro WRITE-SUBARRAY (arguments evaluated).
fn write_subarray(arr : Value, str : Value) -> Value raise {
  share_draw__write_subarray(share_draw__vec_data(arr), str)
  Nil
}

///|
fn update_ranges_2d(
  xmin : Value,
  xmax : Value,
  ymin : Value,
  ymax : Value,
) -> Value raise {
  if get_option(q_d_xaxis_secondary).truthy() {
    share_draw__update_range_of(q_d_xrange_secondary, xmin, xmax)
  } else {
    share_draw__update_range_of(q_d_xrange, xmin, xmax)
  }
  if get_option(q_d_yaxis_secondary).truthy() {
    share_draw__update_range_of(q_d_yrange_secondary, ymin, ymax)
  } else {
    share_draw__update_range_of(q_d_yrange, ymin, ymax)
  }
  Nil
}

///|
fn update_ranges_3d(
  xmin : Value,
  xmax : Value,
  ymin : Value,
  ymax : Value,
  zmin : Value,
  zmax : Value,
) -> Value raise {
  update_ranges_2d(xmin, xmax, ymin, ymax) |> ignore
  share_draw__update_range_of(q_d_zrange, zmin, zmax)
  Nil
}

///|
/// Running extremes of the macros CHECK-EXTREMES-X/Y/Z.
priv struct ShareDrawExt {
  mut xmin : Value
  mut xmax : Value
  mut ymin : Value
  mut ymax : Value
  mut zmin : Value
  mut zmax : Value
}

///|
fn ShareDrawExt::new() -> ShareDrawExt {
  {
    xmin: share_draw__most_positive,
    xmax: share_draw__most_negative,
    ymin: share_draw__most_positive,
    ymax: share_draw__most_negative,
    zmin: share_draw__most_positive,
    zmax: share_draw__most_negative,
  }
}

///|
fn ShareDrawExt::x(self : ShareDrawExt, xx : Value) -> Unit raise {
  if finite_real_p(xx).truthy() {
    if num_lt(xx, self.xmin) {
      self.xmin = xx
    }
    if num_gt(xx, self.xmax) {
      self.xmax = xx
    }
  }
}

///|
fn ShareDrawExt::y(self : ShareDrawExt, yy : Value) -> Unit raise {
  if finite_real_p(yy).truthy() {
    if num_lt(yy, self.ymin) {
      self.ymin = yy
    }
    if num_gt(yy, self.ymax) {
      self.ymax = yy
    }
  }
}

///|
fn ShareDrawExt::z(self : ShareDrawExt, zz : Value) -> Unit raise {
  if finite_real_p(zz).truthy() {
    if num_lt(zz, self.zmin) {
      self.zmin = zz
    }
    if num_gt(zz, self.zmax) {
      self.zmax = zz
    }
  }
}

///|
/// Controls whether the actual graphics object must be plotted against
/// the primary or the secondary axes.
fn axes_to_plot() -> Value raise {
  format(Nil, "~a~a", [
    Str(if get_option(q_d_xaxis_secondary).truthy() { "x2" } else { "x1" }),
    Str(if get_option(q_d_yaxis_secondary).truthy() { "y2" } else { "y1" }),
  ])
}

///|
/// (defstruct gr-object name command groups points)
fn share_draw__make_gr_object(
  name : Value,
  command : Value,
  groups : Value,
  points : Value,
) -> Value {
  make_struct("gr-object", [name, command, groups, points])
}

///|
fn share_draw__gr_object_name(o : Value) -> Value raise {
  struct_ref(o, 0)
}

///|
fn share_draw__gr_object_command(o : Value) -> Value raise {
  struct_ref(o, 1)
}

///|
fn share_draw__gr_object_groups(o : Value) -> Value raise {
  struct_ref(o, 2)
}

///|
fn share_draw__gr_object_points(o : Value) -> Value raise {
  struct_ref(o, 3)
}

///|
fn share_draw__set_gr_object_name(o : Value, v : Value) -> Unit raise {
  struct_set(o, 0, v) |> ignore
}

///|
fn make_obj_title(str : Value) -> Value raise {
  let s = lstring(str)
  let n = s.length()
  if n == 0 {
    Str("notitle")
  } else if n > 80 {
    Str("t '" + lstring(subseq(str, 0, end=75)) + " ...'")
  } else {
    Str("t '" + s + "'")
  }
}

///|
/// A simple vector with the elements of the Lisp list L
/// ((make-array n :initial-contents l)).
fn share_draw__vec(l : Value) -> Value {
  vector(list_to_array(l))
}

///|
/// (hex-to-rgb (get-option opt))
fn share_draw__rgb(opt : Value) -> Value raise {
  hex_to_rgb(get_option(opt))
}

///|
/// (format nil "~@[ fillstyle solid ~a~]" (get-option '$fill_density))
fn share_draw__fillstyle() -> Value raise {
  format(Nil, "~@[ fillstyle solid ~a~]", [get_option(q_d_fill_density)])
}

///|
/// The argument-count check of a DEFUN-CHECKED function NAME with
/// required arguments REQ, NOPT optional ones, and the rest argument REST.
fn share_draw__check_args(
  name : String,
  req : Array[String],
  nopt : Int,
  rest : String?,
  args : Array[Value],
) -> Unit raise {
  let nargs = args.length()
  let nreq = req.length()
  let fsym = sym(name)
  let reqsyms = req.map(r => sym(r))
  match rest {
    Some(r) =>
      if nargs < nreq {
        let pretty = cons(
          list1(fsym),
          append(list(reqsyms), list1(list2(list1(q_mlist), sym(r)))),
        )
        defmfun_arity_error(
          Str("~M: expected at least ~M arguments but got ~M: ~M"),
          pretty,
          int(nreq),
          int(nargs),
          list(args),
        )
        |> ignore
      }
    None =>
      if nopt > 0 {
        if nargs > nreq + nopt {
          defmfun_arity_error(
            Str("~M: expected at most ~M arguments but got ~M: ~M"),
            fsym,
            int(nreq + nopt),
            int(nargs),
            list(args),
          )
          |> ignore
        }
        if nargs < nreq {
          defmfun_arity_error(
            Str("~M: expected at least ~M arguments but got ~M: ~M"),
            fsym,
            int(nreq),
            int(nargs),
            list(args),
          )
          |> ignore
        }
      } else if nargs != nreq {
        defmfun_arity_error(
          Str("~M: expected exactly ~M arguments but got ~M: ~M"),
          cons(list1(fsym), list(reqsyms)),
          int(nreq),
          int(nargs),
          list(args),
        )
        |> ignore
      }
  }
}

///|
/// The argument I of ARGS, or nil.
fn share_draw__argn(args : Array[Value], i : Int) -> Value {
  if i < args.length() {
    args[i]
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// Object: 'errors'
// Usage:
//     errors([[x1,y1,...], [x2,y2,...], [x3,y3,...],...])

///|
fn share_draw__errors(arg : Value) -> Value raise {
  let etype = get_option(q_d_error_type)
  let joined = get_option(q_d_points_joined)
  let mut element_size = 0
  if d_listp(arg).truthy() && every(z => d_listp(z).truthy(), rest(arg)) {
    element_size = length(cdadr(arg))
  } else {
    merr("draw (errors object): incorrect input format", []) |> ignore
  }
  if !every(z => share_draw__mlength(z) == element_size, rest(arg)) {
    merr("draw (errors object): lists of different sizes", []) |> ignore
  }
  // create plot command
  let with_ = if eql(etype, q_d_x) &&
    (element_size == 3 || element_size == 4) {
    if joined is Nil {
      "xerrorbars"
    } else {
      "xerrorlines"
    }
  } else if eql(etype, q_d_y) && (element_size == 3 || element_size == 4) {
    if joined is Nil {
      "yerrorbars"
    } else {
      "yerrorlines"
    }
  } else if eql(etype, q_d_xy) && (element_size == 4 || element_size == 6) {
    if joined is Nil {
      "xyerrorbars"
    } else {
      "xyerrorlines"
    }
  } else if eql(etype, q_d_boxes) && (element_size == 4 || element_size == 6) {
    "boxxyerrorbars"
  } else {
    merr("draw (errors object): incompatibility with option error_type", [])
    |> ignore
    ""
  }
  let grouping = list1(list2(int(element_size), Fix(0L)))
  let pltcmd = format(Nil, " ~a w ~a ~a lw ~a lt ~a lc ~a axis ~a", [
    make_obj_title(get_option(q_d_key)),
    Str(with_),
    if eql(etype, q_d_boxes) {
      // in case of boxes, should they be filled? Default is "not filled".
      let fd = get_option(q_d_fill_density)
      format(Nil, "fs solid ~a", [if fd.truthy() { fd } else { Fix(0L) }])
    } else {
      Str("")
    },
    get_option(q_d_line_width),
    get_option(q_d_line_type),
    share_draw__rgb(q_d_color),
    axes_to_plot(),
  ])
  let pts = mapcar(z => rest(z), rest(d_float(arg)))
  let x = mapcar(z => first(z), pts)
  let y = mapcar(z => second(z), pts)
  let xmin = share_draw__tree_minmax(x, true)
  let xmax = share_draw__tree_minmax(x, false)
  let ymin = share_draw__tree_minmax(y, true)
  let ymax = share_draw__tree_minmax(y, false)
  update_ranges_2d(xmin, xmax, ymin, ymax) |> ignore
  share_draw__make_gr_object(
    q_errors,
    pltcmd,
    grouping,
    list1(share_draw__vec(flatten(pts))),
  )
}

// ---------------------------------------------------------------------------
// Object: 'points'
// Usage:
//     points([[x1,y1], [x2,y2], [x3,y3],...])
//     points([x1,x2,x3,...], [y1,y2,y3,...])
//     points([y1,y2,y3,...]), abscissas are automatically chosen: 1,2,3,...
//     points(matrix), one-column, one-row, two-column or two-row matrix
//     points(array1d)
//     points(array1d, array1d)
//     points(array2d), two-column or two-row array

///|
fn points_command() -> Value raise {
  let pj = get_option(q_d_points_joined)
  let ps = get_option(q_d_point_size)
  let pt = get_option(q_d_point_type)
  if pj is Nil {
    // draws isolated points
    format(Nil, " ~a w p ps ~a pt ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      ps,
      pt,
      share_draw__rgb(q_d_color),
      axes_to_plot(),
    ])
  } else if eq(pj, t) && (num_eq(ps, Flo(0.0)) || num_eq(pt, Fix(0L))) {
    // draws joined points without symbols
    format(Nil, " ~a w l lw ~a lt ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
      axes_to_plot(),
    ])
  } else if eq(pj, t) {
    // draws joined points
    format(Nil, " ~a w lp ps ~a pt ~a lw ~a lt ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      ps,
      pt,
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
      axes_to_plot(),
    ])
  } else {
    // draws impulses
    format(Nil, " ~a w i lw ~a lt ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      get_option(q_d_line_width),
      pt,
      share_draw__rgb(q_d_color),
      axes_to_plot(),
    ])
  }
}

///|
fn points_array_2d(arg : Value) -> Value raise {
  let ext = ShareDrawExt::new()
  let dim = array_dimensions(arg)
  let mut n = 0
  let mut twocolumns = false
  if length(dim) == 2 && eql(cadr(dim), Fix(2L)) {
    // two-column array
    n = to_int(car(dim))
    twocolumns = true
  } else if length(dim) == 2 && eql(car(dim), Fix(2L)) {
    // two-row array
    n = to_int(cadr(dim))
    twocolumns = false
  } else {
    merr("draw (points2d): bad 2d array input format", []) |> ignore
  }
  let pts : Array[Value] = Array::make(2 * n, Nil)
  let mut pos = -1
  for k in 0..<n {
    let (xx, yy) = if twocolumns {
      (d_float(aref(arg, [k, 0])), d_float(aref(arg, [k, 1])))
    } else {
      (d_float(aref(arg, [0, k])), d_float(aref(arg, [1, k])))
    }
    let (xx, yy) = share_draw__transform_point2(xx, yy)
    ext.x(xx)
    ext.y(yy)
    pos = pos + 1
    pts[pos] = xx
    pos = pos + 1
    pts[pos] = yy
  }
  update_ranges_2d(ext.xmin, ext.xmax, ext.ymin, ext.ymax) |> ignore
  share_draw__make_gr_object(
    q_points,
    points_command(),
    share_draw__lit_groups_2_0,
    list1(vector(pts)),
  )
}

///|
/// '((2 0)): numbers are sent to gnuplot in groups of 2.
let share_draw__lit_groups_2_0 : Value = list1(list2(Fix(2L), Fix(0L)))

///|
fn points_array_1d(arg1 : Value, arg2? : Value = Nil) -> Value raise {
  let ext = ShareDrawExt::new()
  let dim = array_dimensions(arg1)
  let mut n = 0
  let mut x : Value = Nil
  let mut y : Value = Nil
  if arg2 is Nil && length(dim) == 1 {
    // y format
    n = to_int(car(dim))
    let xs : Array[Value] = []
    for k in 1..=n {
      xs.push(d_float(int(k)))
    }
    x = vector(xs)
    let ys : Array[Value] = []
    for k in 0..<n {
      ys.push(d_float(aref1(arg1, k)))
    }
    y = vector(ys)
  } else if arrayp(arg2) &&
    length(dim) == 1 &&
    equal(dim, array_dimensions(arg2)) {
    // xx yy format
    n = to_int(car(dim))
    x = arg1
    y = arg2
  } else {
    merr("draw (points2d): bad 1d array input format", []) |> ignore
  }
  let pts : Array[Value] = Array::make(2 * n, Nil)
  let mut pos = -1
  for k in 0..<n {
    let xx = d_float(aref1(x, k))
    let yy = d_float(aref1(y, k))
    let (xx, yy) = share_draw__transform_point2(xx, yy)
    ext.x(xx)
    ext.y(yy)
    pos = pos + 1
    pts[pos] = xx
    pos = pos + 1
    pts[pos] = yy
  }
  update_ranges_2d(ext.xmin, ext.xmax, ext.ymin, ext.ymax) |> ignore
  share_draw__make_gr_object(
    q_points,
    points_command(),
    share_draw__lit_groups_2_0,
    list1(vector(pts)),
  )
}

///|
/// (mapcan #'list x y): the elements of X and Y interleaved.
fn share_draw__interleave2(x : Value, y : Value) -> Value {
  let col = Collector::new()
  let mut a = x
  let mut b = y
  while consp(a) && consp(b) {
    col.add(car(a))
    col.add(car(b))
    a = cdr(a)
    b = cdr(b)
  }
  col.result()
}

///|
/// (mapcan #'list x y z ...): the elements of the lists interleaved.
fn share_draw__interleave(ls : Array[Value]) -> Value {
  let col = Collector::new()
  let cur = ls.copy()
  while cur.iter().all(l => consp(l)) {
    for i in 0..<cur.length() {
      col.add(car(cur[i]))
      cur[i] = cdr(cur[i])
    }
  }
  col.result()
}

///|
/// (loop for xx from 1 to n collect ($float xx))
fn share_draw__float_range(n : Int) -> Value raise {
  let col = Collector::new()
  for xx in 1..=n {
    col.add(d_float(int(xx)))
  }
  col.result()
}

///|
fn points_list(arg1 : Value, arg2? : Value = Nil) -> Value raise {
  let mut x : Value = Nil
  let mut y : Value = Nil
  if d_listp(arg1).truthy() &&
    arg2 is Nil &&
    every(z => d_listp(z).truthy(), rest(arg1)) {
    // xy format
    let tmp = mapcar(z => rest(z), rest(arg1))
    x = share_draw__float_list(mapcar(z => first(z), tmp))
    y = share_draw__float_list(mapcar(z => second(z), tmp))
  } else if d_matrixp(arg1).truthy() && length(cadr(arg1)) == 3 && arg2 is Nil {
    // two-column matrix
    let tmp = mapcar(z => rest(z), rest(arg1))
    x = share_draw__float_list(mapcar(z => first(z), tmp))
    y = share_draw__float_list(mapcar(z => second(z), tmp))
  } else if d_listp(arg1).truthy() &&
    arg2 is Nil &&
    !some(z => d_listp(z).truthy(), rest(arg1)) {
    // y format
    x = share_draw__float_range(length(rest(arg1)))
    y = share_draw__float_list(rest(arg1))
  } else if d_matrixp(arg1).truthy() && length(cadr(arg1)) == 2 && arg2 is Nil {
    // one-column matrix
    x = share_draw__float_range(length(rest(arg1)))
    y = share_draw__float_list(mapcar(z => second(z), rest(arg1)))
  } else if d_matrixp(arg1).truthy() &&
    share_draw__mlength(arg1) == 1 &&
    arg2 is Nil {
    // one-row matrix
    x = share_draw__float_range(length(cdadr(arg1)))
    y = share_draw__float_list(cdadr(arg1))
  } else if d_listp(arg1).truthy() &&
    d_listp(arg2).truthy() &&
    length(arg1) == length(arg2) {
    // xx yy format
    x = share_draw__float_list(rest(arg1))
    y = share_draw__float_list(rest(arg2))
  } else if d_matrixp(arg1).truthy() &&
    share_draw__mlength(arg1) == 2 &&
    arg2 is Nil {
    // two-row matrix
    x = share_draw__float_list(cdadr(arg1))
    y = share_draw__float_list(cdr(caddr(arg1)))
  } else {
    merr("draw (points2d): incorrect input format", []) |> ignore
  }
  let (x, y) = share_draw__transform_lists2(x, y)
  let (xmin, xmax) = extrema_over_finite_floats_list(x)
  let (ymin, ymax) = extrema_over_finite_floats_list(y)
  let pts = share_draw__vec(share_draw__interleave2(x, y))
  // update x-y ranges if necessary
  update_ranges_2d(xmin, xmax, ymin, ymax) |> ignore
  share_draw__make_gr_object(
    q_points,
    points_command(),
    share_draw__lit_groups_2_0,
    list1(pts),
  )
}

///|
fn share_draw__points(arg1 : Value, arg2 : Value) -> Value raise {
  if arrayp(arg1) {
    if length(array_dimensions(arg1)) == 2 {
      points_array_2d(arg1)
    } else {
      points_array_1d(arg1, arg2~)
    }
  } else {
    points_list(arg1, arg2~)
  }
}

// ---------------------------------------------------------------------------
// Object: 'points3d'
// Usage:
//     points([[x1,y1,z1], [x2,y2,z2], [x3,y3,z3],...])
//     points([x1,x2,x3,...], [y1,y2,y3,...], [z1,z2,z3,...])
//     points(matrix), three-column or three-row matrix
//     points(array2d),  three-column or three-row array
//     points(array1d, array1d, array1d, array1d)

///|
fn points3d_command() -> Value raise {
  let pj = get_option(q_d_points_joined)
  let ps = get_option(q_d_point_size)
  let pt = get_option(q_d_point_type)
  let pal : Value = if num_gt(symval(q_ear_draw_enhanced3d_type), Fix(0L)) {
    Str("palette")
  } else {
    share_draw__rgb(q_d_color)
  }
  if pj is Nil {
    // draws isolated points
    format(Nil, " ~a w p ps ~a pt ~a lc ~a", [
      make_obj_title(get_option(q_d_key)),
      ps,
      pt,
      pal,
    ])
  } else if eq(pj, t) && (num_eq(ps, Flo(0.0)) || num_eq(pt, Fix(0L))) {
    // draws joined points without symbols
    format(Nil, " ~a w l lw ~a lt ~a lc ~a ", [
      make_obj_title(get_option(q_d_key)),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
    ])
  } else if eq(pj, t) {
    // draws joined points
    format(Nil, " ~a w lp ps ~a pt ~a lw ~a lt ~a lc ~a", [
      make_obj_title(get_option(q_d_key)),
      ps,
      pt,
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      pal,
    ])
  } else {
    // draws impulses
    format(Nil, " ~a w i lw ~a lt ~a lc ~a", [
      make_obj_title(get_option(q_d_key)),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      pal,
    ])
  }
}

///|
/// ($float (aref arr ...)) for the elements of a row/column of a 2d array
/// or of a 1d array.
fn share_draw__float_array_seq(arr : Value) -> Value raise {
  let col = Collector::new()
  match arr {
    Vec(a) =>
      for v in a.data {
        col.add(d_float(v))
      }
    _ => ()
  }
  col.result()
}

///|
fn share_draw__points3d(arg1 : Value, arg2 : Value, arg3 : Value) -> Value raise {
  let mut x : Value = Nil
  let mut y : Value = Nil
  let mut z : Value = Nil
  check_enhanced3d_model(Str("points"), list([Fix(0L), Fix(1L), Fix(3L)]))
  |> ignore
  if d_listp(arg1).truthy() {
    // list input
    if every(z => d_listp(z).truthy(), rest(arg1)) && arg2 is Nil && arg3 is Nil {
      // xyz format
      let tmp = mapcar(z => rest(z), rest(arg1))
      x = share_draw__float_list(mapcar(z => first(z), tmp))
      y = share_draw__float_list(mapcar(z => second(z), tmp))
      z = share_draw__float_list(mapcar(z => third(z), tmp))
    } else if d_listp(arg2).truthy() &&
      d_listp(arg3).truthy() &&
      length(arg1) == length(arg2) &&
      length(arg2) == length(arg3) {
      // xx yy zz format
      x = share_draw__float_list(rest(arg1))
      y = share_draw__float_list(rest(arg2))
      z = share_draw__float_list(rest(arg3))
    } else {
      merr("draw (points3d): bad list input format", []) |> ignore
    }
  } else if d_matrixp(arg1).truthy() {
    // matrix input
    if length(cadr(arg1)) == 4 && arg2 is Nil && arg3 is Nil {
      // three-column matrix
      let tmp = mapcar(z => rest(z), rest(arg1))
      x = share_draw__float_list(mapcar(z => first(z), tmp))
      y = share_draw__float_list(mapcar(z => second(z), tmp))
      z = share_draw__float_list(mapcar(z => third(z), tmp))
    } else if share_draw__mlength(arg1) == 3 && arg2 is Nil && arg3 is Nil {
      // three-row matrix
      x = share_draw__float_list(cdadr(arg1))
      y = share_draw__float_list(cdr(caddr(arg1)))
      z = share_draw__float_list(cdr(caddr(rest(arg1))))
    } else {
      merr("draw (points3d): bad matrix input format", []) |> ignore
    }
  } else if arrayp(arg1) {
    // array input
    let dim = array_dimensions(arg1)
    let row_or_col = (row : Bool, i : Int, n : Int) => {
      let col = Collector::new()
      for k in 0..<n {
        col.add(d_float(if row { aref(arg1, [i, k]) } else { aref(arg1, [k, i]) }))
      }
      col.result()
    }
    if length(dim) == 2 && eql(first(dim), Fix(3L)) && arg2 is Nil && arg3 is Nil {
      // three-row array
      let n = to_int(second(dim))
      x = row_or_col(true, 0, n)
      y = row_or_col(true, 1, n)
      z = row_or_col(true, 2, n)
    } else if length(dim) == 2 &&
      eql(second(dim), Fix(3L)) &&
      arg2 is Nil &&
      arg3 is Nil {
      // three-column array
      let n = to_int(first(dim))
      x = row_or_col(false, 0, n)
      y = row_or_col(false, 1, n)
      z = row_or_col(false, 2, n)
    } else if length(dim) == 1 &&
      arrayp(arg2) &&
      arrayp(arg3) &&
      equal(dim, array_dimensions(arg2)) &&
      equal(dim, array_dimensions(arg3)) {
      // three 1d arrays
      x = share_draw__float_array_seq(arg1)
      y = share_draw__float_array_seq(arg2)
      z = share_draw__float_array_seq(arg3)
    } else {
      merr("draw (points3d): bad array input format", []) |> ignore
    }
  } else {
    merr("draw (points3d): bad input format", []) |> ignore
  }
  let (x, y, z) = share_draw__transform_lists3(x, y, z)
  // set pm3d colors
  let e3type = symval(q_ear_draw_enhanced3d_type)
  let e3fun = symval(q_ear_draw_enhanced3d_fun)
  let mut ncols = 0
  let mut pts : Value = Nil
  if num_eq(e3type, Fix(0L)) {
    ncols = 3
    pts = share_draw__vec(share_draw__interleave([x, y, z]))
  } else if num_eq(e3type, Fix(1L)) {
    let col = Collector::new()
    for k in 1..=length(x) {
      col.add(funcall(e3fun, [int(k)]))
    }
    ncols = 4
    pts = share_draw__vec(share_draw__interleave([x, y, z, col.result()]))
  } else if num_eq(e3type, Fix(3L)) {
    let col = share_draw__mapcar3(
      (xx, yy, zz) => funcall(e3fun, [xx, yy, zz]),
      x,
      y,
      z,
    )
    ncols = 4
    pts = share_draw__vec(share_draw__interleave([x, y, z, col]))
  }
  let xmin = share_draw__tree_minmax(x, true)
  let xmax = share_draw__tree_minmax(x, false)
  let ymin = share_draw__tree_minmax(y, true)
  let ymax = share_draw__tree_minmax(y, false)
  let zmin = share_draw__tree_minmax(z, true)
  let zmax = share_draw__tree_minmax(z, false)
  // update x-y-z ranges if necessary
  update_ranges_3d(xmin, xmax, ymin, ymax, zmin, zmax) |> ignore
  share_draw__make_gr_object(
    q_points,
    points3d_command(),
    // numbers are sent to gnuplot in groups of 4 or 3 (depending on
    // colored 4th dimension or not), without blank lines
    list1(list2(int(ncols), Fix(0L))),
    list1(pts),
  )
}

// ---------------------------------------------------------------------------
// Object: 'polygon'
// Usage:
//     polygon([[x1,y1], [x2,y2], [x3,y3],...])
//     polygon([x1,x2,x3,...], [y1,y2,y3,...])

///|
fn share_draw__polygon(arg1 : Value, arg2 : Value) -> Value raise {
  if get_option(q_d_transparent).truthy() && !get_option(q_d_border).truthy() {
    merr(
      "draw (polygon): transparent is true and border is false; this is not consistent",
      [],
    )
    |> ignore
  }
  let mut x : Value = Nil
  let mut y : Value = Nil
  if d_listp(arg1).truthy() &&
    every(z => d_listp(z).truthy(), rest(arg1)) &&
    arg2 is Nil {
    // xy format
    let tmp = mapcar(z => rest(z), rest(arg1))
    x = mapcar(z => d_float(first(z)), tmp)
    y = mapcar(z => d_float(second(z)), tmp)
  } else if d_listp(arg1).truthy() &&
    d_listp(arg2).truthy() &&
    length(arg1) == length(arg2) {
    // xx yy format
    x = share_draw__float_list(rest(arg1))
    y = share_draw__float_list(rest(arg2))
  } else {
    merr("draw (polygon): bad input format", []) |> ignore
  }
  let (x, y) = share_draw__transform_lists2(x, y)
  let xmin = share_draw__tree_minmax(x, true)
  let xmax = share_draw__tree_minmax(x, false)
  let ymin = share_draw__tree_minmax(y, true)
  let ymax = share_draw__tree_minmax(y, false)
  // update x-y ranges if necessary
  update_ranges_2d(xmin, xmax, ymin, ymax) |> ignore
  let mut pltcmd : Value = Nil
  let mut grps : Value = Nil
  let mut pts : Value = Nil
  if get_option(q_d_transparent).truthy() {
    // if transparent, draw only the border
    pltcmd = format(Nil, " ~a  w l lw ~a lt ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
      axes_to_plot(),
    ])
    grps = share_draw__lit_groups_2_0
    pts = list1(
      share_draw__vec(
        append(share_draw__interleave2(x, y), list2(first(x), first(y))),
      ),
    )
  } else if !get_option(q_d_border).truthy() {
    // no transparent, no border
    pltcmd = format(Nil, " ~a w filledcurves~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      share_draw__fillstyle(),
      share_draw__rgb(q_d_fill_color),
      axes_to_plot(),
    ])
    grps = share_draw__lit_groups_2_0
    pts = list1(share_draw__vec(share_draw__interleave2(x, y)))
  } else {
    // no transparent with border
    pltcmd = list2(
      format(Nil, " ~a w filledcurves~a lc ~a axis ~a", [
        make_obj_title(get_option(q_d_key)),
        share_draw__fillstyle(),
        share_draw__rgb(q_d_fill_color),
        axes_to_plot(),
      ]),
      format(Nil, " t '' w l lw ~a lt ~a lc ~a axis ~a", [
        get_option(q_d_line_width),
        get_option(q_d_line_type),
        share_draw__rgb(q_d_color),
        axes_to_plot(),
      ]),
    )
    // both sets of vertices (interior and border) are sent to gnuplot in
    // groups of 2
    grps = list2(list2(Fix(2L), Fix(0L)), list2(Fix(2L), Fix(0L)))
    pts = list2(
      share_draw__vec(share_draw__interleave2(x, y)),
      share_draw__vec(
        append(share_draw__interleave2(x, y), list2(first(x), first(y))),
      ),
    )
  }
  share_draw__make_gr_object(q_polygon, pltcmd, grps, pts)
}

///|
/// ((mlist simp) ...) of vertices for TRIANGLE, QUADRILATERAL, RECTANGLE.
fn share_draw__vertex_list(vs : Array[(Value, Value)]) -> Value {
  let items = vs.map(v => mk_simp(q_mlist, [v.0, v.1]))
  mk_simp(q_mlist, items)
}

///|
/// Checks that each of VS is a Maxima list of length N.
fn share_draw__vertices_ok(vs : Array[Value], n : Int) -> Bool raise {
  for v in vs {
    if !d_listp(v).truthy() || share_draw__mlength(v) != n {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Object: 'triangle'
// Usage:
//     triangle([x1,y1], [x2,y2], [x3,y3])

///|
fn share_draw__triangle(arg1 : Value, arg2 : Value, arg3 : Value) -> Value raise {
  if !share_draw__vertices_ok([arg1, arg2, arg3], 2) {
    merr("draw2d (triangle): vertices are not correct", []) |> ignore
  }
  let x1 = d_float(cadr(arg1))
  let y1 = d_float(caddr(arg1))
  let x2 = d_float(cadr(arg2))
  let y2 = d_float(caddr(arg2))
  let x3 = d_float(cadr(arg3))
  let y3 = d_float(caddr(arg3))
  let grobj = share_draw__polygon(
    share_draw__vertex_list([(x1, y1), (x2, y2), (x3, y3), (x1, y1)]),
    Nil,
  )
  share_draw__set_gr_object_name(grobj, q_triangle)
  grobj
}

// ---------------------------------------------------------------------------
// Object: 'quadrilateral'
// Usage:
//     quadrilateral([x1,y1], [x2,y2], [x3,y3], [x4,y4])

///|
fn share_draw__quadrilateral(
  arg1 : Value,
  arg2 : Value,
  arg3 : Value,
  arg4 : Value,
) -> Value raise {
  if !share_draw__vertices_ok([arg1, arg2, arg3, arg4], 2) {
    merr("draw2d (quadrilateral): vertices are not correct", []) |> ignore
  }
  let x1 = d_float(cadr(arg1))
  let y1 = d_float(caddr(arg1))
  let x2 = d_float(cadr(arg2))
  let y2 = d_float(caddr(arg2))
  let x3 = d_float(cadr(arg3))
  let y3 = d_float(caddr(arg3))
  let x4 = d_float(cadr(arg4))
  let y4 = d_float(caddr(arg4))
  let grobj = share_draw__polygon(
    share_draw__vertex_list([(x1, y1), (x2, y2), (x3, y3), (x4, y4), (x1, y1)]),
    Nil,
  )
  share_draw__set_gr_object_name(grobj, q_quadrilateral)
  grobj
}

// ---------------------------------------------------------------------------
// Object: 'rectangle'
// Usage:
//     rectangle([x1,y1], [x2,y2]), being [x1,y1] & [x2,y2] opposite vertices

///|
fn share_draw__rectangle(arg1 : Value, arg2 : Value) -> Value raise {
  if !share_draw__vertices_ok([arg1, arg2], 2) {
    merr("draw2d (rectangle): vertices are not correct", []) |> ignore
  }
  let x1 = d_float(cadr(arg1))
  let y1 = d_float(caddr(arg1))
  let x2 = d_float(cadr(arg2))
  let y2 = d_float(caddr(arg2))
  let grobj = share_draw__polygon(
    share_draw__vertex_list([(x1, y1), (x2, y1), (x2, y2), (x1, y2), (x1, y1)]),
    Nil,
  )
  share_draw__set_gr_object_name(grobj, q_rectangle)
  grobj
}

// ---------------------------------------------------------------------------
// Object: 'ellipse'
// Usage:
//     ellipse(xc, yc, a, b, ang1 ang2)

///|
fn share_draw__ellipse(
  xc : Value,
  yc : Value,
  a : Value,
  b : Value,
  ang1 : Value,
  ang2 : Value,
) -> Value raise {
  if get_option(q_d_transparent).truthy() && !get_option(q_d_border).truthy() {
    merr(
      "draw2d (ellipse): transparent is true and border is false; this is not consistent",
      [],
    )
    |> ignore
  }
  let mut fxc = d_float(xc)
  let mut fyc = d_float(yc)
  let fa = d_float(a)
  let fb = d_float(b)
  let mut fang1 = d_float(ang1)
  let mut fang2 = d_float(ang2)
  let nticks = get_option(q_d_nticks)
  let ext = ShareDrawExt::new()
  let mut result : Value = Nil
  if ![fxc, fyc, fa, fb, fang1, fang2].iter().all(v => floatp(v)) ||
    num_le(fa, Flo(0.0)) ||
    num_le(fb, Flo(0.0)) {
    merr("draw (ellipse): illegal argument(s)", []) |> ignore
  }
  // degrees to radians
  fang1 = num_mul(Flo(0.017453292519943295), fang1)
  fang2 = num_mul(Flo(0.017453292519943295), fang2)
  let tmin = num_min(fang1, num_add(fang1, fang2))
  let tmax = num_max(fang1, num_add(fang1, fang2))
  let eps = num_div(num_sub(tmax, tmin), num_sub(nticks, Fix(1L)))
  let mut tt = tmin
  while true {
    let xx = num_add(fxc, num_mul(fa, lcos(tt)))
    let yy = num_add(fyc, num_mul(fb, lsin(tt)))
    let (xx, yy) = share_draw__transform_point2(xx, yy)
    ext.x(xx)
    ext.y(yy)
    result = append(list2(xx, yy), result)
    if num_ge(tt, tmax) {
      break
    }
    tt = num_add(tt, eps)
    if num_ge(tt, tmax) {
      tt = tmax
    }
  }
  if share_draw__transforming() {
    let xold = fxc
    let yold = fyc
    fxc = funcall(symval(q_ear_draw_transform_f1), [xold, yold])
    fyc = funcall(symval(q_ear_draw_transform_f2), [xold, yold])
  }
  // update x-y ranges if necessary
  let xmin = num_min(fxc, ext.xmin)
  let xmax = num_max(fxc, ext.xmax)
  let ymin = num_min(fyc, ext.ymin)
  let ymax = num_max(fyc, ext.ymax)
  update_ranges_2d(xmin, xmax, ymin, ymax) |> ignore
  let mut pltcmd : Value = Nil
  let mut grps : Value = Nil
  let mut pts : Value = Nil
  if get_option(q_d_transparent).truthy() {
    // if transparent, draw only the border
    pltcmd = format(Nil, " ~a w l lw ~a lt ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
      axes_to_plot(),
    ])
    grps = share_draw__lit_groups_2_0
    pts = list1(share_draw__vec(result))
  } else if !get_option(q_d_border).truthy() {
    // no transparent, no border
    pltcmd = format(Nil, " ~a w filledcurves xy=~a,~a ~alc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      fxc,
      fyc,
      share_draw__fillstyle(),
      share_draw__rgb(q_d_fill_color),
      axes_to_plot(),
    ])
    grps = share_draw__lit_groups_2_0
    pts = list1(share_draw__vec(result))
  } else {
    // no transparent with border
    pltcmd = list2(
      format(Nil, " ~a w filledcurves xy=~a,~a ~a lc ~a axis ~a", [
        make_obj_title(get_option(q_d_key)),
        fxc,
        fyc,
        share_draw__fillstyle(),
        share_draw__rgb(q_d_fill_color),
        axes_to_plot(),
      ]),
      format(Nil, " t '' w l lw ~a lt ~a lc ~a axis ~a", [
        get_option(q_d_line_width),
        get_option(q_d_line_type),
        share_draw__rgb(q_d_color),
        axes_to_plot(),
      ]),
    )
    grps = list2(list2(Fix(2L), Fix(0L)), list2(Fix(2L), Fix(0L)))
    pts = list2(share_draw__vec(result), share_draw__vec(result))
  }
  share_draw__make_gr_object(q_ellipse, pltcmd, grps, pts)
}

// ---------------------------------------------------------------------------
// Object: 'label'
// Usage in 2d:
//     label([string1,xx1,y1],[string2,xx2,y2],...)
// Usage in 3d:
//     label([string1,x1,y1,z1],[string2,x2,y2,z2],...)

///|
fn replace_substring(
  string_ : Value,
  part : Value,
  replacement : Value,
) -> Value raise {
  let s = lstring(string_)
  let p = lstring(part)
  let r = lstring(replacement)
  let sb = StringBuilder::new()
  let chars = s.to_array()
  let pchars = p.to_array()
  let n = chars.length()
  let m = pchars.length()
  let mut old_pos = 0
  while true {
    // (search part string :start2 old-pos :test #'char=)
    let mut pos = -1
    let mut i = old_pos
    while i + m <= n {
      let mut ok = true
      for j in 0..<m {
        if chars[i + j] != pchars[j] {
          ok = false
          break
        }
      }
      if ok {
        pos = i
        break
      }
      i = i + 1
    }
    let end = if pos >= 0 { pos } else { n }
    for k in old_pos..<end {
      sb.write_char(chars[k])
    }
    if pos < 0 {
      break
    }
    sb.write_string(r)
    old_pos = pos + m
  }
  Str(sb.to_string())
}

///|
fn share_draw__label(lab : Value) -> Value raise {
  let n = length(lab)
  let mut result : Value = Nil
  let mut is2d = false
  if n == 0 {
    merr("draw (label): no arguments in object labels", []) |> ignore
  } else if every(z => d_listp(z).truthy(), lab) {
    if every(z => share_draw__mlength(z) == 3, lab) {
      // labels in 2d
      is2d = true
    } else if every(z => share_draw__mlength(z) == 4, lab) {
      // labels in 3d
      is2d = false
    } else {
      merr("draw (label): arguments of not equal length", []) |> ignore
    }
    if is2d {
      for k in lab.iter() {
        let xx = d_float(funcall(q_d_second, [k]))
        let yy = d_float(funcall(q_d_third, [k]))
        // backslashes are replaced by double backslashes to allow LaTeX
        // code in labels.
        let text = format(Nil, "\"~a\"", [
          replace_substring(d_first(k), Str("\\"), Str("\\\\")),
        ])
        if !floatp(xx) || !floatp(yy) {
          merr("draw (label): non real 2d coordinates", []) |> ignore
        }
        let (xx, yy) = share_draw__transform_point2(xx, yy)
        update_ranges_2d(xx, xx, yy, yy) |> ignore
        result = append(list([xx, yy, text]), result)
      }
    } else {
      // labels in 3d
      for k in lab.iter() {
        let xx = d_float(funcall(q_d_second, [k]))
        let yy = d_float(funcall(q_d_third, [k]))
        let zz = d_float(funcall(q_d_fourth, [k]))
        let text = format(Nil, "\"~a\"", [d_first(k)])
        if !floatp(xx) || !floatp(yy) || !floatp(zz) {
          merr("draw (label): non real 3d coordinates", []) |> ignore
        }
        let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
        update_ranges_3d(xx, xx, yy, yy, zz, zz) |> ignore
        result = append(list([xx, yy, zz, text]), result)
      }
    }
  } else {
    merr("draw (label): illegal arguments", []) |> ignore
  }
  let align = get_option(q_d_label_alignment)
  let orient = get_option(q_d_label_orientation)
  share_draw__make_gr_object(
    q_label,
    format(Nil, " t '' w labels ~a ~a tc ~a ~a", [
      if eq(align, q_d_center) {
        Str("center")
      } else if eq(align, q_d_left) {
        Str("left")
      } else if eq(align, q_d_right) {
        Str("right")
      } else {
        Nil
      },
      if eq(orient, q_d_horizontal) {
        Str("norotate")
      } else if eq(orient, q_d_vertical) {
        Str("rotate")
      } else {
        Nil
      },
      share_draw__rgb(q_d_color),
      if is2d {
        format(Nil, "axis ~a", [axes_to_plot()])
      } else {
        Str("")
      },
    ]),
    if is2d {
      list1(list2(Fix(3L), Fix(0L)))
    } else {
      list1(list2(Fix(4L), Fix(0L)))
    },
    list1(share_draw__vec(result)),
  )
}

// ---------------------------------------------------------------------------
// Object: 'bars'
//     bars([x1,h1,w1],[x2,h2,w2],...), x, height and width

///|
fn share_draw__bars(boxes : Value) -> Value raise {
  let n = length(boxes)
  let ext = ShareDrawExt::new()
  if n == 0 {
    merr("draw2d (bars): no arguments in object bars", []) |> ignore
  }
  if !every(
      z => d_listp(z).truthy() && share_draw__mlength(z) == 3,
      boxes,
    ) {
    merr("draw2d (bars): arguments must be lists of length three", [])
    |> ignore
  }
  let result : Array[Value] = Array::make(3 * n, Flo(0.0))
  let mut count = -1
  for k in boxes.iter() {
    let x = d_float(d_first(k))
    let h = d_float(funcall(q_d_second, [k]))
    let w = d_float(funcall(q_d_third, [k]))
    let w2 = num_div(w, Fix(2L))
    count = count + 1
    result[count] = x
    count = count + 1
    result[count] = h
    count = count + 1
    result[count] = w
    ext.xmin = num_min(ext.xmin, num_sub(x, w2))
    ext.xmax = num_max(ext.xmax, num_add(x, w2))
    ext.ymin = num_min(ext.ymin, h)
    ext.ymax = num_max(ext.ymax, h)
  }
  update_ranges_2d(ext.xmin, ext.xmax, ext.ymin, ext.ymax) |> ignore
  let fd = get_option(q_d_fill_density)
  share_draw__make_gr_object(
    q_bars,
    format(Nil, " ~a w boxes fs solid ~a lw ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      if fd.truthy() {
        fd
      } else {
        Fix(0L)
      },
      get_option(q_d_line_width),
      share_draw__rgb(q_d_fill_color),
      axes_to_plot(),
    ]),
    // numbers are sent to gnuplot in groups of 3, without blank lines
    list1(list2(Fix(3L), Fix(0L))),
    list1(vector(result)),
  )
}

///|
/// The head description of the vector objects.
fn share_draw__head_type_name() -> Value raise {
  let ht = get_option(q_d_head_type)
  if eq(ht, q_d_filled) {
    Str("filled")
  } else if eq(ht, q_d_empty) {
    Str("empty")
  } else if eq(ht, q_d_nofilled) {
    Str("nofilled")
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// Object: 'vector'
// Usage:
//     vector([x,y], [dx,dy]), represents vector from [x,y] to [x+dx,y+dy]

///|
fn share_draw__vect(arg1 : Value, arg2 : Value) -> Value raise {
  if !share_draw__vertices_ok([arg1, arg2], 2) {
    merr("draw (vector): coordinates are not correct", []) |> ignore
  }
  let xo = d_float(cadr(arg1))
  let yo = d_float(caddr(arg1))
  let mut dx = d_float(cadr(arg2))
  let mut dy = d_float(caddr(arg2))
  if get_option(q_d_unit_vectors).truthy() &&
    (!num_eq(dx, Fix(0L)) || !num_eq(dy, Fix(0L))) {
    let module = lsqrt(num_add(num_mul(dx, dx), num_mul(dy, dy)))
    dx = num_div(dx, module)
    dy = num_div(dy, module)
  }
  let xdx = d_float(num_add(xo, dx))
  let ydy = d_float(num_add(yo, dy))
  // apply geometric transformation before plotting
  let (x, y) = share_draw__transform_lists2(list2(xo, xdx), list2(yo, ydy))
  update_ranges_2d(
    share_draw__tree_minmax(x, true),
    share_draw__tree_minmax(x, false),
    share_draw__tree_minmax(y, true),
    share_draw__tree_minmax(y, false),
  )
  |> ignore
  share_draw__make_gr_object(
    q_vector,
    format(Nil, " ~a w vect ~a size ~a, ~a ~a lw ~a lt ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      Str(if get_option(q_d_head_both).truthy() { "heads" } else { "head" }),
      get_option(q_d_head_length),
      get_option(q_d_head_angle),
      share_draw__head_type_name(),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
      axes_to_plot(),
    ]),
    list1(list2(Fix(4L), Fix(0L))),
    list1(
      vector([
        car(x),
        car(y),
        num_sub(cadr(x), car(x)),
        num_sub(cadr(y), car(y)),
      ]),
    ),
  )
}

// ---------------------------------------------------------------------------
// Object: 'vector3d'
// Usage:
//     vector([x,y,z], [dx,dy,dz]), represents vector from [x,y,z] to
//     [x+dx,y+dy,z+dz]

///|
fn share_draw__vect3d(arg1 : Value, arg2 : Value) -> Value raise {
  if !share_draw__vertices_ok([arg1, arg2], 3) {
    merr("draw (vector): coordinates are not correct", []) |> ignore
  }
  let xo = d_float(cadr(arg1))
  let yo = d_float(caddr(arg1))
  let zo = d_float(cadddr(arg1))
  let mut dx = d_float(cadr(arg2))
  let mut dy = d_float(caddr(arg2))
  let mut dz = d_float(cadddr(arg2))
  if get_option(q_d_unit_vectors).truthy() &&
    (
      !num_eq(dx, Fix(0L)) || !num_eq(dy, Fix(0L)) || !num_eq(dz, Fix(0L))
    ) {
    let module = lsqrt(
      num_sum([num_mul(dx, dx), num_mul(dy, dy), num_mul(dz, dz)]),
    )
    dx = num_div(dx, module)
    dy = num_div(dy, module)
    dz = num_div(dz, module)
  }
  let xdx = d_float(num_add(xo, dx))
  let ydy = d_float(num_add(yo, dy))
  let zdz = d_float(num_add(zo, dz))
  // apply geometric transformation before plotting
  let (x, y, z) = share_draw__transform_lists3(
    list2(xo, xdx),
    list2(yo, ydy),
    list2(zo, zdz),
  )
  update_ranges_3d(
    share_draw__tree_minmax(x, true),
    share_draw__tree_minmax(x, false),
    share_draw__tree_minmax(y, true),
    share_draw__tree_minmax(y, false),
    share_draw__tree_minmax(z, true),
    share_draw__tree_minmax(z, false),
  )
  |> ignore
  share_draw__make_gr_object(
    q_vector,
    format(Nil, " ~a w vect ~a size ~a, ~a ~a lw ~a lt ~a lc ~a", [
      make_obj_title(get_option(q_d_key)),
      Str(if get_option(q_d_head_both).truthy() { "heads" } else { "head" }),
      get_option(q_d_head_length),
      get_option(q_d_head_angle),
      share_draw__head_type_name(),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
    ]),
    list1(list2(Fix(6L), Fix(0L))),
    list1(
      vector([
        car(x),
        car(y),
        car(z),
        num_sub(cadr(x), car(x)),
        num_sub(cadr(y), car(y)),
        num_sub(cadr(z), car(z)),
      ]),
    ),
  )
}

// ---------------------------------------------------------------------------
// Object: 'explicit'
// Usage:
//     explicit(fcn,var,minval,maxval)

///|
fn share_draw__explicit(
  fcn : Value,
  var_ : Value,
  minval : Value,
  maxval : Value,
) -> Value raise {
  with_specials(
    [(q_d_numer, t), (share_draw__q_plot_realpart, symval(share_draw__q_plot_realpart))],
    () => share_draw__explicit_body(fcn, var_, minval, maxval),
  )
}

///|
fn share_draw__explicit_body(
  fcn : Value,
  var_ : Value,
  minval : Value,
  maxval : Value,
) -> Value raise {
  let nticks = get_option(q_d_nticks)
  let depth = get_option(q_d_adapt_depth)
  let mut xmin = d_float(minval)
  let mut xmax = d_float(maxval)
  let mut x_step = num_div(num_div(num_sub(xmax, xmin), d_float(nticks)), Fix(2L))
  let ext = ShareDrawExt::new()
  let mut result : Value = Nil
  if num_lt(xmax, xmin) {
    merr("draw2d (explicit): illegal range", []) |> ignore
  }
  set(share_draw__q_plot_realpart, get_option(q_d_draw_realpart)) |> ignore
  let fcn = share_draw__coerce_float_fun(fcn, mk(q_mlist, [var_]))
  if get_option(q_d_logx).truthy() {
    xmin = llog(xmin)
    xmax = llog(xmax)
    x_step = num_div(num_div(num_sub(xmax, xmin), d_float(nticks)), Fix(2L))
  }
  let fun = (x : Value) => {
    let y = if get_option(q_d_logx).truthy() {
      funcall(fcn, [lexp(x)])
    } else {
      funcall(fcn, [x])
    }
    if get_option(q_d_logy).truthy() && numberp(y) {
      if num_gt(y, Fix(0L)) {
        llog(y)
      } else {
        merr("draw2d (explicit): logarithm of negative number", [])
      }
    } else {
      y
    }
  }
  let xs = Collector::new()
  let ys = Collector::new()
  for k in 0..<(1 + 2 * to_int(nticks)) {
    let x = num_add(xmin, num_mul(int(k), x_step))
    xs.add(x)
    ys.add(fun(x))
  }
  let x_samples = xs.result()
  let y_samples = ys.result()
  // For each region, adaptively plot it.
  let mut x_start = x_samples
  let mut x_mid = cdr(x_samples)
  let mut x_end = cddr(x_samples)
  let mut y_start = y_samples
  let mut y_mid = cdr(y_samples)
  let mut y_end = cddr(y_samples)
  while !(x_end is Nil) {
    // The region is x-start to x-end, with mid-point x-mid.
    let mut sublst = share_draw__adaptive_plot(
      fun,
      car(x_start),
      car(x_mid),
      car(x_end),
      car(y_start),
      car(y_mid),
      car(y_end),
      to_int(depth),
      Flo(1.0e-5),
    )
    if !every(x => numberp(x) || eq(x, t) || x is Nil, sublst) {
      // Search for the item in sublist that is the undefined variable
      let mut item : Value = Nil
      for it in sublst.iter() {
        if !(numberp(it) || eq(it, t) || it is Nil) {
          item = it
        }
      }
      merr("draw2d (explicit): non defined variable in term: ~M", [item])
      |> ignore
    }
    if !(result is Nil) {
      sublst = cddr(sublst)
    }
    let mut lst = sublst
    while !(lst is Nil) {
      result = cons(
        if get_option(q_d_logy).truthy() && numberp(second(lst)) {
          lexp(second(lst))
        } else {
          second(lst)
        },
        result,
      )
      result = cons(
        if get_option(q_d_logx).truthy() && numberp(first(lst)) {
          lexp(first(lst))
        } else {
          first(lst)
        },
        result,
      )
      lst = cddr(lst)
    }
    x_start = cddr(x_start)
    x_mid = cddr(x_mid)
    x_end = cddr(x_end)
    y_start = cddr(y_start)
    y_mid = cddr(y_mid)
    y_end = cddr(y_end)
  }
  // reset x extremes to original values
  if get_option(q_d_logx).truthy() {
    xmin = lexp(xmin)
    xmax = lexp(xmax)
  }
  let filled = get_option(q_d_filled_func)
  if filled is Nil {
    let mut result_array : Value = Nil
    if share_draw__transforming() {
      // With geometric transformation. When option filled_func in not nil,
      // geometric transformation is ignored
      let arr : Array[Value] = Array::make(length(result), Nil)
      xmin = share_draw__most_positive
      xmax = share_draw__most_negative
      let mut count = -1
      let mut lis = result
      while !(lis is Nil) {
        let xold = first(lis)
        let yold = second(lis)
        let x = funcall(symval(q_ear_draw_transform_f1), [xold, yold])
        let y = funcall(symval(q_ear_draw_transform_f2), [xold, yold])
        if num_gt(x, xmax) {
          xmax = x
        }
        if num_lt(x, xmin) {
          xmin = x
        }
        if num_gt(y, ext.ymax) {
          ext.ymax = y
        }
        if num_lt(y, ext.ymin) {
          ext.ymin = y
        }
        count = count + 1
        arr[count] = x
        count = count + 1
        arr[count] = y
        lis = cddr(lis)
      }
      result_array = vector(arr)
    } else {
      // No geometric transformation invoked.
      let mut y = cdr(result)
      while !(y is Nil) {
        ext.y(car(y))
        y = cddr(y)
      }
      result_array = share_draw__vec(result)
    }
    update_ranges_2d(xmin, xmax, ext.ymin, ext.ymax) |> ignore
    let pltcmd = format(Nil, " ~a w l lw ~a lt ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
      axes_to_plot(),
    ])
    share_draw__make_gr_object(
      q_explicit,
      pltcmd,
      share_draw__lit_groups_2_0,
      list1(result_array),
    )
  } else if equal(filled, t) {
    let mut y = cdr(result)
    while !(y is Nil) {
      ext.y(car(y))
      y = cddr(y)
    }
    update_ranges_2d(xmin, xmax, ext.ymin, ext.ymax) |> ignore
    let result_array = share_draw__vec(result)
    let pltcmd = format(Nil, " ~a w filledcurves x1 ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      share_draw__fillstyle(),
      share_draw__rgb(q_d_fill_color),
      axes_to_plot(),
    ])
    share_draw__make_gr_object(
      q_explicit,
      pltcmd,
      share_draw__lit_groups_2_0,
      list1(result_array),
    )
  } else {
    let arr : Array[Value] = Array::make(length(result) / 2 * 3, Flo(0.0))
    let mut count = -1
    let fcn2 = share_draw__coerce_float_fun(filled, mk(q_mlist, [var_]))
    let mut xx = result
    while !(xx is Nil) {
      let yy = second(xx)
      let yy2 = funcall(fcn2, [first(xx)])
      ext.ymax = num_max(num_max(ext.ymax, yy), yy2)
      ext.ymin = num_min(num_min(ext.ymin, yy), yy2)
      count = count + 1
      arr[count] = first(xx)
      count = count + 1
      arr[count] = yy
      count = count + 1
      arr[count] = yy2
      xx = cddr(xx)
    }
    update_ranges_2d(xmin, xmax, ext.ymin, ext.ymax) |> ignore
    let pltcmd = format(Nil, " ~a w filledcurves~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      share_draw__fillstyle(),
      share_draw__rgb(q_d_fill_color),
      axes_to_plot(),
    ])
    share_draw__make_gr_object(
      q_explicit,
      pltcmd,
      // numbers are sent to gnuplot in groups of 3
      list1(list2(Fix(3L), Fix(0L))),
      list1(vector(arr)),
    )
  }
}

// ---------------------------------------------------------------------------
// Object: 'region'
// Usage:
//     region(ineq,x-var,x-minval,x-maxval,y-var,y-minval,y-maxval)

///|
/// (subsetp a b :test #'like)
fn share_draw__subsetp_like(a : Value, b : Value) -> Bool raise {
  every(x => some(y => like(x, y).truthy(), b), a)
}

///|
fn share_draw__region(
  ineq : Value,
  x_var : Value,
  x_minval : Value,
  x_maxval : Value,
  y_var : Value,
  y_minval : Value,
  y_maxval : Value,
) -> Value raise {
  let nx = to_int(get_option(q_d_x_voxel))
  let ny = to_int(get_option(q_d_y_voxel))
  let xmin = d_float(x_minval)
  let xmax = d_float(x_maxval)
  let ymin = d_float(y_minval)
  let ymax = d_float(y_maxval)
  let dx = num_div(num_sub(xmax, xmin), int(nx))
  let dy = num_div(num_sub(ymax, ymin), int(ny))
  let err = num_mul(Flo(0.02), num_min(dx, dy))
  let xarr = make_array([nx + 1, ny + 1], elt="flonum")
  let yarr = make_array([nx + 1, ny + 1], elt="flonum")
  let barr = make_array([nx + 1, ny + 1])
  let mut pts : Value = Nil
  if !share_draw__subsetp_like(rest(d_listofvars(ineq)), list2(x_var, y_var)) {
    merr("draw2d (region): non defined variable", []) |> ignore
  }
  // evaluates boolean expression
  let fun = (xx : Value, yy : Value) => with_special(q_d_prederror, t, () => {
    d_is_boole_eval(
      simplify(
        d_substitute(
          list([
            list1(q_mlist),
            list([list1(q_mequal), x_var, xx]),
            list([list1(q_mequal), y_var, yy]),
          ]),
          ineq,
        ),
      ),
    )
  })
  // bipartition, (xx1, yy1) => T, (xx2, yy2) => NIL
  fn bipart(
    xx1 : Value,
    yy1 : Value,
    xx2 : Value,
    yy2 : Value,
  ) -> Value raise {
    let xm = num_mul(Flo(0.5), num_add(xx1, xx2))
    let ym = num_mul(Flo(0.5), num_add(yy1, yy2))
    if num_lt(
        num_add(
          num_mul(num_sub(xx2, xx1), num_sub(xx2, xx1)),
          num_mul(num_sub(yy2, yy1), num_sub(yy2, yy1)),
        ),
        num_mul(err, err),
      ) {
      list2(xm, ym)
    } else if fun(xm, ym).truthy() {
      bipart(xm, ym, xx2, yy2)
    } else {
      bipart(xx1, yy1, xm, ym)
    }
  }
  // fill arrays
  for i in 0..=nx {
    for j in 0..=ny {
      let x = num_add(xmin, num_mul(int(i), dx))
      let y = num_add(ymin, num_mul(int(j), dy))
      aset(xarr, [i, j], x) |> ignore
      aset(yarr, [i, j], y) |> ignore
      aset(barr, [i, j], fun(x, y)) |> ignore
    }
  }
  let build_polygon = (coord : Array[Value]) => {
    pts = cons(vector(coord), pts)
  }
  // check vertices of rectangles and cuts
  for i in 0..<nx {
    for j in 0..<ny {
      let x1 = aref(xarr, [i, j]) // SW point
      let y1 = aref(yarr, [i, j])
      let b1 = aref(barr, [i, j]).truthy()
      let x2 = aref(xarr, [i + 1, j]) // SE point
      let y2 = aref(yarr, [i + 1, j])
      let b2 = aref(barr, [i + 1, j]).truthy()
      let x3 = aref(xarr, [i + 1, j + 1]) // NE point
      let y3 = aref(yarr, [i + 1, j + 1])
      let b3 = aref(barr, [i + 1, j + 1]).truthy()
      let x4 = aref(xarr, [i, j + 1]) // NW point
      let y4 = aref(yarr, [i, j + 1])
      let b4 = aref(barr, [i, j + 1]).truthy()
      // pa and pb are frontier points
      if b1 && b2 && b3 && b4 {
        build_polygon([x1, y1, x2, y2, x3, y3, x4, y4])
      } else if b1 && b2 && b3 {
        let pa = bipart(x3, y3, x4, y4)
        let pb = bipart(x1, y1, x4, y4)
        build_polygon([x1, y1, x2, y2, x3, y3, first(pa), second(pa), first(pb), second(pb)])
      } else if b4 && b1 && b2 {
        let pa = bipart(x2, y2, x3, y3)
        let pb = bipart(x4, y4, x3, y3)
        build_polygon([x4, y4, x1, y1, x2, y2, first(pa), second(pa), first(pb), second(pb)])
      } else if b3 && b4 && b1 {
        let pa = bipart(x1, y1, x2, y2)
        let pb = bipart(x3, y3, x2, y2)
        build_polygon([x3, y3, x4, y4, x1, y1, first(pa), second(pa), first(pb), second(pb)])
      } else if b2 && b3 && b4 {
        let pa = bipart(x4, y4, x1, y1)
        let pb = bipart(x2, y2, x1, y1)
        build_polygon([x2, y2, x3, y3, x4, y4, first(pa), second(pa), first(pb), second(pb)])
      } else if b2 && b3 {
        let pa = bipart(x3, y3, x4, y4)
        let pb = bipart(x2, y2, x1, y1)
        build_polygon([x2, y2, x3, y3, first(pa), second(pa), first(pb), second(pb)])
      } else if b4 && b1 {
        let pa = bipart(x1, y1, x2, y2)
        let pb = bipart(x4, y4, x3, y3)
        build_polygon([x4, y4, x1, y1, first(pa), second(pa), first(pb), second(pb)])
      } else if b3 && b4 {
        let pa = bipart(x4, y4, x1, y1)
        let pb = bipart(x3, y3, x2, y2)
        build_polygon([x3, y3, x4, y4, first(pa), second(pa), first(pb), second(pb)])
      } else if b1 && b2 {
        let pa = bipart(x2, y2, x3, y3)
        let pb = bipart(x1, y1, x4, y4)
        build_polygon([x1, y1, x2, y2, first(pa), second(pa), first(pb), second(pb)])
      } else if b1 {
        let pa = bipart(x1, y1, x2, y2)
        let pb = bipart(x1, y1, x3, y4)
        let pc = bipart(x1, y1, x4, y4)
        build_polygon([
          x1,
          y1,
          first(pa),
          second(pa),
          first(pb),
          second(pb),
          first(pc),
          second(pc),
        ])
      } else if b2 {
        let pa = bipart(x2, y2, x3, y3)
        let pb = bipart(x2, y2, x4, y4)
        let pc = bipart(x2, y2, x1, y1)
        build_polygon([
          x2,
          y2,
          first(pa),
          second(pa),
          first(pb),
          second(pb),
          first(pc),
          second(pc),
        ])
      } else if b3 {
        let pa = bipart(x3, y3, x4, y4)
        let pb = bipart(x3, y3, x1, y1)
        let pc = bipart(x3, y3, x2, y2)
        build_polygon([
          x3,
          y3,
          first(pa),
          second(pa),
          first(pb),
          second(pb),
          first(pc),
          second(pc),
        ])
      } else if b4 {
        let pa = bipart(x4, y4, x1, y1)
        let pb = bipart(x4, y4, x2, y2)
        let pc = bipart(x4, y4, x3, y3)
        build_polygon([
          x4,
          y4,
          first(pa),
          second(pa),
          first(pb),
          second(pb),
          first(pc),
          second(pc),
        ])
      }
    }
  }
  // list of commands
  let npts = length(pts)
  if npts - 1 < 0 {
    raise LispError::SimpleError(
      "The value -1 is not of type (MOD 4611686018427387901)",
    )
  }
  let other = format(Nil, " t '' w filledcurves~a lc ~a axis ~a", [
    share_draw__fillstyle(),
    share_draw__rgb(q_d_fill_color),
    axes_to_plot(),
  ])
  let others = Collector::new()
  for _ in 0..<(npts - 1) {
    others.add(other)
  }
  let pltcmd = cons(
    format(Nil, " ~a w filledcurves~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      share_draw__fillstyle(),
      share_draw__rgb(q_d_fill_color),
      axes_to_plot(),
    ]),
    others.result(),
  )
  update_ranges_2d(xmin, xmax, ymin, ymax) |> ignore
  let grouping = Collector::new()
  for _ in 0..<npts {
    grouping.add(share_draw__lit_group_2_0)
  }
  share_draw__make_gr_object(q_region, pltcmd, grouping.result(), pts)
}

///|
/// '(2 0)
let share_draw__lit_group_2_0 : Value = list2(Fix(2L), Fix(0L))

// ---------------------------------------------------------------------------
// Object: 'implicit'
// Usage:
//     implicit(fcn,x-var,x-minval,x-maxval,y-var,y-minval,y-maxval)
// Note: taken from implicit_plot.lisp

///|
/// Returns elements at odd positions.
fn x_elements(list_ : Value) -> Value raise {
  if list_ is Nil {
    list_
  } else {
    cons(first(list_), x_elements(rest(rest(list_))))
  }
}

///|
/// Returns elements at even positions.
fn y_elements(list_ : Value) -> Value raise {
  x_elements(rest(list_))
}

///|
fn contains_zeros(i : Value, j : Value, sample : Value) -> Value raise {
  let i = to_int(i)
  let j = to_int(j)
  let s = (a : Int, b : Int) => aref(sample, [a, b])
  lbool(
    !(
      num_gt(num_mul(s(i, j), s(i + 1, j)), Fix(0L)) &&
      num_gt(num_mul(s(i, j), s(i, j + 1)), Fix(0L)) &&
      num_gt(num_mul(s(i, j), s(i + 1, j + 1)), Fix(0L))
    ),
  )
}

///|
fn sample_data(
  expr : Value,
  xmin : Value,
  xmax : Value,
  ymin : Value,
  ymax : Value,
  sample : Value,
  grid : Value,
) -> Value raise {
  let xdelta = num_div(num_sub(xmax, xmin), d_first(grid))
  let ydelta = num_div(num_sub(ymax, ymin), funcall(q_d_second, [grid]))
  let epsilon : Value = Flo(1.0e-6)
  let mut x_val = xmin
  let mut i = 0
  while !num_gt(int(i), d_first(grid)) {
    let mut y_val = ymin
    let mut j = 0
    while !num_gt(int(j), funcall(q_d_second, [grid])) {
      let fun_val = funcall(expr, [x_val, y_val])
      if !floatp(fun_val) && !eq(fun_val, t) {
        merr("draw2d (implicit): non defined variable in condition ~M=0", [
          fun_val,
        ])
        |> ignore
      }
      if eq(fun_val, t) || num_ge(fun_val, epsilon) {
        aset(sample, [i, j], Fix(1L)) |> ignore
      } else {
        aset(sample, [i, j], Fix(-1L)) |> ignore
      }
      y_val = num_add(y_val, ydelta)
      j = j + 1
    }
    x_val = num_add(x_val, xdelta)
    i = i + 1
  }
  Nil
}

///|
fn draw_print_segment(
  points : Value,
  xmin : Value,
  xdelta : Value,
  ymin : Value,
  ydelta : Value,
) -> Value raise {
  let point1 = car(points)
  let point2 = cadr(points)
  let coord = (a : Value, b : Value, m : Value, d : Value) => lfloat(
    num_add(m, num_div(num_mul(d, num_add(a, b)), Fix(2L))),
  )
  let x1 = coord(car(point1), caddr(point1), xmin, xdelta)
  let y1 = coord(cadr(point1), cadddr(point1), ymin, ydelta)
  let x2 = coord(car(point2), caddr(point2), xmin, xdelta)
  let y2 = coord(cadr(point2), cadddr(point2), ymin, ydelta)
  set(q_pts, nconc(list([x1, y1, x2, y2]), symval(q_pts)))
}

///|
fn draw_print_square(
  xmin : Value,
  xmax : Value,
  ymin : Value,
  ymax : Value,
  sample : Value,
  grid : Value,
) -> Value raise {
  let xdelta = num_div(num_sub(xmax, xmin), d_first(grid))
  let ydelta = num_div(num_sub(ymax, ymin), funcall(q_d_second, [grid]))
  let ni = to_int(d_first(grid))
  let nj = to_int(funcall(q_d_second, [grid]))
  let s = (a : Int, b : Int) => aref(sample, [a, b])
  for i in 0..<ni {
    for j in 0..<nj {
      if contains_zeros(int(i), int(j), sample).truthy() {
        let mut points : Value = Nil
        if num_lt(num_mul(s(i, j), s(i + 1, j)), Fix(0L)) {
          points = cons(list([int(i), int(j), int(i + 1), int(j)]), points)
        }
        if num_lt(num_mul(s(i + 1, j), s(i + 1, j + 1)), Fix(0L)) {
          points = cons(
            list([int(i + 1), int(j), int(i + 1), int(j + 1)]),
            points,
          )
        }
        if num_lt(num_mul(s(i, j + 1), s(i + 1, j + 1)), Fix(0L)) {
          points = cons(
            list([int(i), int(j + 1), int(i + 1), int(j + 1)]),
            points,
          )
        }
        if num_lt(num_mul(s(i, j), s(i, j + 1)), Fix(0L)) {
          points = cons(list([int(i), int(j), int(i), int(j + 1)]), points)
        }
        draw_print_segment(points, xmin, xdelta, ymin, ydelta) |> ignore
      }
    }
  }
  Nil
}

///|
fn imp_pl_prepare_factor(expr : Value) -> Value raise {
  if d_numberp(expr).truthy() || atom(expr) {
    expr
  } else if eq(caar(expr), q_mexpt) {
    cadr(expr)
  } else {
    expr
  }
}

///|
fn imp_pl_prepare_expr(expr : Value) -> Value raise {
  let expr1 = d_factor(m_(d_rhs(expr), a2=d_lhs(expr)))
  if d_numberp(expr).truthy() || atom(expr1) {
    expr1
  } else if eq(caar(expr1), q_mtimes) {
    cons(
      list([q_mtimes, q_simp, q_factored, Fix(1L)]),
      mapcar(z => imp_pl_prepare_factor(z), cdr(expr1)),
    )
  } else if eq(caar(expr), q_mexpt) {
    imp_pl_prepare_factor(expr1)
  } else {
    expr1
  }
}

///|
fn share_draw__implicit(
  expr : Value,
  x : Value,
  xmin : Value,
  xmax : Value,
  y : Value,
  ymin : Value,
  ymax : Value,
) -> Value raise {
  // ($plot_options $plot_options) of the Lisp code rebinds a plot.lisp
  // variable nothing here changes.
  with_specials([(q_d_numer, t), (q_pts, Nil)], () => {
    let expr = m_(d_rhs(expr), a2=d_lhs(expr))
    let ip_grid = get_option(q_d_ip_grid)
    let ip_grid_in = get_option(q_d_ip_grid_in)
    let xmin = d_float(xmin)
    let xmax = d_float(xmax)
    let ymin = d_float(ymin)
    let ymax = d_float(ymax)
    let xdelta = num_div(num_sub(xmax, xmin), d_first(ip_grid))
    let ydelta = num_div(num_sub(ymax, ymin), funcall(q_d_second, [ip_grid]))
    let g1 = to_int(d_first(ip_grid))
    let g2 = to_int(funcall(q_d_second, [ip_grid]))
    let sample = make_array([g1 + 1, g2 + 1])
    let ssample = make_array([
      to_int(d_first(ip_grid_in)) + 1,
      to_int(funcall(q_d_second, [ip_grid_in])) + 1,
    ])
    let e = share_draw__coerce_float_fun(
      imp_pl_prepare_expr(expr),
      mk_simp(q_mlist, [x, y]),
    )
    update_ranges_2d(xmin, xmax, ymin, ymax) |> ignore
    sample_data(e, xmin, xmax, ymin, ymax, sample, ip_grid) |> ignore
    for i in 0..<g1 {
      for j in 0..<g2 {
        if contains_zeros(int(i), int(j), sample).truthy() {
          let xxmin = num_add(xmin, num_mul(int(i), xdelta))
          let xxmax = num_add(xxmin, xdelta)
          let yymin = num_add(ymin, num_mul(int(j), ydelta))
          let yymax = num_add(yymin, ydelta)
          sample_data(e, xxmin, xxmax, yymin, yymax, ssample, ip_grid_in)
          |> ignore
          draw_print_square(xxmin, xxmax, yymin, yymax, ssample, ip_grid_in)
          |> ignore
        }
      }
    }
    // geometric transformation
    if share_draw__transforming() {
      let x = x_elements(symval(q_pts))
      let y = y_elements(symval(q_pts))
      let (x, y) = share_draw__transform_lists2(x, y)
      let xmin = share_draw__tree_minmax(x, true)
      let xmax = share_draw__tree_minmax(x, false)
      let ymin = share_draw__tree_minmax(y, true)
      let ymax = share_draw__tree_minmax(y, false)
      update_ranges_2d(xmin, xmax, ymin, ymax) |> ignore
      let col = Collector::new()
      let mut x = x
      let mut y = y
      while true {
        col.add(car(x))
        col.add(car(y))
        x = cdr(x)
        y = cdr(y)
        if x is Nil {
          break
        }
      }
      set(q_pts, col.result()) |> ignore
    }
    let pltcmd = format(Nil, " ~a w l lw ~a lt ~a lc ~a axis ~a", [
      make_obj_title(get_option(q_d_key)),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
      axes_to_plot(),
    ])
    share_draw__make_gr_object(
      q_implicit,
      pltcmd,
      list1(list2(Fix(2L), Fix(2L))),
      list1(share_draw__vec(symval(q_pts))),
    )
  })
}
