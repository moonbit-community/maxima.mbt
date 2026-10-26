// Port of share/draw/grcommon.lisp: graphics options common to the
// Gnuplot and VTK renderers of the draw package, the marching cubes
// algorithm for implicit surfaces, and the entry points draw, draw2d and
// draw3d.

// ---------------------------------------------------------------------------
// The plot.lisp / plotcolors.lisp helpers used by the draw package

///|
/// plot.lisp's special *PLOT-REALPART* (T by default).
let share_draw__q_plot_realpart : Value = q_ear_plot_realpart

///|
/// plotcolors.lisp's special *COLOR-TABLE* (an EQUAL hash table of color
/// names to "#rrggbb" strings).
let share_draw__q_color_table : Value = q_ear_color_table

///|
/// server.lisp's GETPID: the process id.
fn share_draw__getpid() -> Value {
  int(process_id())
}

///|
/// plot.lisp's MAYBE-REALPART.
fn share_draw__maybe_realpart(x : Value) -> Value raise {
  maybe_realpart(x)
}

///|
/// plot.lisp's COERCE-FLOAT-FUN called as (coerce-float-fun expr lvars).
fn share_draw__coerce_float_fun(expr : Value, lvars : Value) -> Value raise {
  coerce_float_fun(expr, list1(lvars))
}

///|
/// plot.lisp's ADAPTIVE-PLOT.
fn share_draw__adaptive_plot(
  fcn : (Value) -> Value raise,
  a : Value,
  b : Value,
  c : Value,
  f_a : Value,
  f_b : Value,
  f_c : Value,
  depth : Int,
  eps : Value,
) -> Value raise {
  adaptive_plot(
    lfunc("adaptive-plot-fcn", args => fcn(arg(args, 0))),
    a,
    b,
    c,
    f_a,
    f_b,
    f_c,
    int(depth),
    eps,
  )
}

///|
/// plot.lisp's PLOT-TEMP-FILE called as (plot-temp-file file t).
fn share_draw__plot_temp_file(file : Value) -> Value raise {
  plot_temp_file(file, preserve_file=t)
}

///|
/// plotcolors.lisp's ATOM-TO-DOWNCASED-STRING.
fn share_draw__atom_to_downcased_string(val : Value) -> String raise {
  lstring(atom_to_downcased_string(val))
}

///|
/// plotcolors.lisp's HEX-TO-NUMERIC-LIST: "#rrggbb" to a list of three
/// floats in [0, 1].
fn share_draw__hex_to_numeric_list(str : Value) -> Value raise {
  hex_to_numeric_list(str)
}

///|
/// (gethash str *color-table*)
fn share_draw__color_table_get(str : String) -> Value raise {
  gethash(Str(str), symval(share_draw__q_color_table))
}

// ---------------------------------------------------------------------------
// Helpers for the macros of grcommon.lisp / gnuplot.lisp

///|
/// (gethash opt *gr-options*) as a setf place.
fn share_draw__set_option(opt : Value, val : Value) -> Value raise {
  sethash(opt, symval(q_ear_gr_options), val)
}

///|
/// ($length x) as an Int.
fn share_draw__mlength(x : Value) -> Int raise {
  to_int(d_length(x))
}

///|
/// (> *draw-transform-dimensions* 0)
fn share_draw__transforming() -> Bool raise {
  num_gt(symval(q_ear_draw_transform_dimensions), Fix(0L))
}

///|
/// Macro TRANSFORM-POINT 2: the transformed point (xx, yy).
fn share_draw__transform_point2(xx : Value, yy : Value) -> (Value, Value) raise {
  if share_draw__transforming() {
    let xold = xx
    let yold = yy
    (
      funcall(symval(q_ear_draw_transform_f1), [xold, yold]),
      funcall(symval(q_ear_draw_transform_f2), [xold, yold]),
    )
  } else {
    (xx, yy)
  }
}

///|
/// Macro TRANSFORM-POINT 3: the transformed point (xx, yy, zz).
fn share_draw__transform_point3(
  xx : Value,
  yy : Value,
  zz : Value,
) -> (Value, Value, Value) raise {
  if share_draw__transforming() {
    let xold = xx
    let yold = yy
    let zold = zz
    (
      funcall(symval(q_ear_draw_transform_f1), [xold, yold, zold]),
      funcall(symval(q_ear_draw_transform_f2), [xold, yold, zold]),
      funcall(symval(q_ear_draw_transform_f3), [xold, yold, zold]),
    )
  } else {
    (xx, yy, zz)
  }
}

///|
/// MAPCAR over three lists.
fn share_draw__mapcar3(
  f : (Value, Value, Value) -> Value raise,
  a : Value,
  b : Value,
  c : Value,
) -> Value raise {
  let col = Collector::new()
  let mut x = a
  let mut y = b
  let mut z = c
  while consp(x) && consp(y) && consp(z) {
    col.add(f(car(x), car(y), car(z)))
    x = cdr(x)
    y = cdr(y)
    z = cdr(z)
  }
  col.result()
}

///|
/// Macro TRANSFORM-LISTS 2: the transformed lists (x, y).
fn share_draw__transform_lists2(x : Value, y : Value) -> (Value, Value) raise {
  if share_draw__transforming() {
    let xold = x
    let yold = y
    let f1 = symval(q_ear_draw_transform_f1)
    let f2 = symval(q_ear_draw_transform_f2)
    (
      mapcar2((u1, u2) => funcall(f1, [u1, u2]), xold, yold),
      mapcar2((u1, u2) => funcall(f2, [u1, u2]), xold, yold),
    )
  } else {
    (x, y)
  }
}

///|
/// Macro TRANSFORM-LISTS 3: the transformed lists (x, y, z).
fn share_draw__transform_lists3(
  x : Value,
  y : Value,
  z : Value,
) -> (Value, Value, Value) raise {
  if share_draw__transforming() {
    let xold = x
    let yold = y
    let zold = z
    let f1 = symval(q_ear_draw_transform_f1)
    let f2 = symval(q_ear_draw_transform_f2)
    let f3 = symval(q_ear_draw_transform_f3)
    (
      share_draw__mapcar3((u1, u2, u3) => funcall(f1, [u1, u2, u3]), xold, yold, zold),
      share_draw__mapcar3((u1, u2, u3) => funcall(f2, [u1, u2, u3]), xold, yold, zold),
      share_draw__mapcar3((u1, u2, u3) => funcall(f3, [u1, u2, u3]), xold, yold, zold),
    )
  } else {
    (x, y, z)
  }
}

///|
/// Macro LISTIFY-ARGUMENTS: arguments of make-scene-2d, make-scene-3d,
/// draw and vtk3d flattened into a unique list, so that nested lists of
/// options and graphic objects are admitted.
fn share_draw__listify_arguments(args : Value) -> Value raise {
  rest(
    d_flatten(
      d_tree_reduce(
        q_d_append,
        cons(
          list1(q_mlist),
          mapcar(
            z => if d_listp(z).truthy() { z } else { list2(list1(q_mlist), z) },
            args,
          ),
        ),
      ),
    ),
  )
}

///|
/// Error of a function-like macro of the draw package whose expansion
/// refers to local variables of its caller: it is expanded inline in the
/// port (see the share_draw__ helpers) and cannot be called.
fn share_draw__inline_macro(name : String) -> Value raise {
  raise LispError::SimpleError(
    name + " is a macro expanded inline by its callers in the draw package",
  )
}

///|
/// macro TRANSFORM-POINT: its expansion assigns the caller's XX, YY (and
/// ZZ); see share_draw__transform_point2/3.
fn transform_point(n : Value) -> Value raise {
  ignore(n)
  share_draw__inline_macro("TRANSFORM-POINT")
}

///|
/// macro TRANSFORM-LISTS: its expansion assigns the caller's X, Y (and Z);
/// see share_draw__transform_lists2/3.
fn transform_lists(n : Value) -> Value raise {
  ignore(n)
  share_draw__inline_macro("TRANSFORM-LISTS")
}

///|
/// macro LISTIFY-ARGUMENTS (ARGS is the evaluated argument list).
fn listify_arguments(args : Value) -> Value raise {
  share_draw__listify_arguments(args)
}

///|
/// macro MAKE-TRIANGLE-VERTICES: its expansion reads the local arrays PX,
/// PY, PZ and VAL of FIND-TRIANGLES, where it is expanded inline.
fn make_triangle_vertices(
  i1 : Value,
  j1 : Value,
  k1 : Value,
  i2 : Value,
  j2 : Value,
  k2 : Value,
  e1 : Value,
  e2 : Value,
) -> Value raise {
  ignore((i1, j1, k1, i2, j2, k2, e1, e2))
  share_draw__inline_macro("MAKE-TRIANGLE-VERTICES")
}

///|
/// ($tree_reduce 'min l) / ($tree_reduce 'max l) of a list of numbers
/// (CL MIN / MAX are associative on reals, so a left fold gives the same
/// result).
fn share_draw__tree_minmax(l : Value, is_min : Bool) -> Value raise {
  if l is Nil {
    return merr(
      "tree_reduce: either a nonempty set or initial value must be given.",
      [],
    )
  }
  let mut acc = car(l)
  for x in cdr(l).iter() {
    acc = if is_min { num_min(acc, x) } else { num_max(acc, x) }
  }
  acc
}

///|
/// ($float x) for each element of the Lisp list L.
fn share_draw__float_list(l : Value) -> Value raise {
  mapcar(z => d_float(z), l)
}

// ---------------------------------------------------------------------------
// grcommon.lisp

///|
fn d_set_draw_defaults(opts : Value) -> Value raise {
  set(q_ear_user_gr_default_options, opts) |> ignore
  cons(list1(q_mlist), opts)
}

///|
fn user_defaults() -> Value raise {
  for x in symval(q_ear_user_gr_default_options).iter() {
    if equal(d_op(x), Str("=")) {
      update_gr_option(d_lhs(x), d_rhs(x)) |> ignore
    } else {
      merr("draw: item ~M is not recognized as an option assignment", [x])
      |> ignore
    }
  }
  Nil
}

///|
/// Sets default values of graphics options.
fn ini_gr_options() -> Value raise {
  let o = (k : Value, v : Value) => share_draw__set_option(k, v) |> ignore
  // global options to control general aspects of graphics
  o(q_d_allocation, Nil)
  o(q_d_proportional_axes, q_d_none)
  o(q_d_xrange, Nil)
  o(q_d_xrange_secondary, Nil)
  o(q_d_yrange, Nil)
  o(q_d_yrange_secondary, Nil)
  o(q_d_zrange, Nil)
  o(q_d_cbrange, Nil)
  o(q_d_logx, Nil)
  o(q_d_logx_secondary, Nil)
  o(q_d_logy, Nil)
  o(q_d_logy_secondary, Nil)
  o(q_d_logz, Nil)
  o(q_d_logcb, Nil)
  o(q_d_title, Str(""))
  o(q_d_view, share_draw__lit_view)
  o(q_d_xy_file, Str(""))
  o(q_d_user_preamble, Str(""))
  o(q_d_xyplane, Nil)
  o(q_d_font, Str(""))
  o(q_d_font_size, Fix(10L))
  o(q_d_key_pos, Nil)
  // colors are specified by name
  o(q_d_background_color, Str("#ffffff"))
  o(q_d_color, Str("#0000ff"))
  o(q_d_fill_color, Str("#ff0000"))
  o(q_d_fill_density, Nil)
  // implicit plot options
  o(q_d_ip_grid, share_draw__lit_ip_grid)
  o(q_d_ip_grid_in, share_draw__lit_ip_grid_in)
  o(q_d_x_voxel, Fix(10L))
  o(q_d_y_voxel, Fix(10L))
  o(q_d_z_voxel, Fix(10L))
  // tics
  o(q_d_grid, list2(Fix(0L), Fix(0L)))
  o(q_d_xtics, Str("autofreq"))
  o(q_d_xtics_secondary, Nil)
  o(q_d_ytics, Str("autofreq"))
  o(q_d_ytics_secondary, Nil)
  o(q_d_ztics, Str("autofreq"))
  o(q_d_cbtics, Str("autofreq"))
  o(q_d_xtics_rotate, Nil)
  o(q_d_xtics_secondary_rotate, Nil)
  o(q_d_ytics_rotate, Nil)
  o(q_d_ytics_secondary_rotate, Nil)
  o(q_d_ztics_rotate, Nil)
  o(q_d_xtics_axis, Nil)
  o(q_d_xtics_secondary_axis, Nil)
  o(q_d_ytics_axis, Nil)
  o(q_d_ytics_secondary_axis, Nil)
  o(q_d_ztics_axis, Nil)
  // axes
  o(q_d_axis_bottom, t)
  o(q_d_axis_left, t)
  o(q_d_axis_top, t)
  o(q_d_axis_right, t)
  o(q_d_axis_3d, t)
  o(q_d_xaxis, Nil)
  o(q_d_xaxis_width, Fix(1L))
  o(q_d_xaxis_type, Fix(0L))
  o(q_d_xaxis_color, Str("#000000"))
  o(q_d_yaxis, Nil)
  o(q_d_yaxis_width, Fix(1L))
  o(q_d_yaxis_type, Fix(0L))
  o(q_d_yaxis_color, Str("#000000"))
  o(q_d_zaxis, Nil)
  o(q_d_zaxis_width, Fix(1L))
  o(q_d_zaxis_type, Fix(0L))
  o(q_d_zaxis_color, Str("#000000"))
  o(q_d_xlabel, Str(""))
  o(q_d_xlabel_secondary, Str(""))
  o(q_d_ylabel, Str(""))
  o(q_d_ylabel_secondary, Str(""))
  o(q_d_zlabel, Str(""))
  o(q_d_zlabel_rotate, q_d_auto)
  // point options
  o(q_d_point_size, Fix(1L))
  o(q_d_point_type, Fix(1L))
  o(q_d_points_joined, Nil)
  // error bars option
  o(q_d_error_type, q_d_y)
  // polygon options
  o(q_d_transparent, Nil)
  o(q_d_opacity, Fix(1L))
  o(q_d_border, t)
  // vector options
  o(q_d_head_both, Nil)
  o(q_d_head_length, Fix(2L))
  o(q_d_head_angle, Fix(45L))
  o(q_d_head_type, q_d_filled)
  o(q_d_unit_vectors, Nil)
  // label options
  o(q_d_label_alignment, q_d_center)
  o(q_d_label_orientation, q_d_horizontal)
  // line options
  o(q_d_line_width, Fix(1L))
  o(q_d_line_type, Fix(1L))
  // function options
  o(q_d_nticks, Fix(29L))
  o(q_d_adapt_depth, Fix(10L))
  o(q_d_key, Str(""))
  o(q_d_filled_func, Nil)
  o(q_d_xaxis_secondary, Nil)
  o(q_d_yaxis_secondary, Nil)
  o(q_d_draw_realpart, t)
  // transformation option
  o(q_d_transform, q_d_none)
  // 3d options
  o(q_d_xu_grid, Fix(50L))
  o(q_d_yv_grid, Fix(50L))
  o(q_d_surface_hide, Nil)
  o(q_d_interpolate_color, Str("depthorder"))
  o(q_d_enhanced3d, q_d_none)
  o(q_d_isolines, q_d_none)
  o(q_d_wired_surface, Nil)
  o(q_d_contour, q_d_none)
  o(q_d_contour_levels, Fix(5L))
  o(q_d_isolines_levels, Fix(10L))
  o(q_d_colorbox, t)
  o(q_d_palette, q_d_color)
  o(q_d_capping, share_draw__lit_capping)
  Nil
}

///|
let share_draw__lit_view : Value = list2(Fix(60L), Fix(30L))

///|
let share_draw__lit_ip_grid : Value = mk_simp(q_mlist, [Fix(50L), Fix(50L)])

///|
let share_draw__lit_ip_grid_in : Value = mk_simp(q_mlist, [Fix(5L), Fix(5L)])

///|
let share_draw__lit_capping : Value = mk_simp(q_mlist, [Nil, Nil])

///|
/// Returns option value.
fn get_option(opt : Value) -> Value raise {
  gethash(opt, symval(q_ear_gr_options))
}

///|
fn correct_color_name(str : Value) -> Value raise {
  // (some (lambda (z) (string= z str)) <hash keys>): the table is an EQUAL
  // table of strings, so a key STRING= to STR is a hit of GETHASH.
  lbool(stringp(str) && gethash2(str, symval(share_draw__q_color_table)).1)
}

///|
/// Hex colors can either read #rrggbb or #rrggbbaa with rr, bb, gg and aa
/// being two-digit hex numbers.
fn correct_color_hex(str : Value) -> Value raise {
  let s = lstring(str)
  let chars = s.to_array()
  lbool(
    (chars.length() == 7 || chars.length() == 9) &&
    chars[0] == '#' &&
    chars[1:].iter().all(z => "0123456789abcdef".contains_char(z)),
  )
}

///|
fn correct_color(str : Value) -> Value raise {
  let a = correct_color_name(str)
  if a.truthy() {
    return a
  }
  let b = correct_color_hex(str)
  if b.truthy() {
    return b
  }
  lbool(lstring(str) == "auto")
}

///|
/// Interprets a rgb string or a rgba string and converts the latter to
/// argb as gnuplot needs this format.
fn hex_to_rgb(str : Value) -> Value raise {
  let s = lstring(str)
  if s.length() == 7 {
    format(Nil, "rgb '~a'", [str])
  } else {
    format(Nil, "rgb '#~a~a'", [subseq(str, 7, end=9), subseq(str, 1, end=7)])
  }
}

///|
fn update_color(opt : Value, val : Value) -> Value raise {
  let mut val = val
  if numberp(val) {
    let names = [
      "black", "red", "blue", "green", "pink", "orange", "violet", "yellow", "magenta",
      "cyan", "gray", "springgreen", "darkcyan", "darkmagenta", "darkred", "mintcream",
      "azure", "navy",
    ]
    let mut found = false
    for i in 0..<names.length() {
      if eql(val, int(i)) {
        val = Str(names[i])
        found = true
        break
      }
    }
    if !found {
      merr("model3d: unknown color ~M", [val]) |> ignore
    }
  }
  let mut str : Value = Str(share_draw__atom_to_downcased_string(val))
  if !correct_color(str).truthy() {
    merr("model3d: unknown color ~M", [val]) |> ignore
  }
  if correct_color_name(str).truthy() {
    str = gethash(str, symval(share_draw__q_color_table))
  }
  share_draw__set_option(opt, str)
}

///|
fn update_key_pos(val : Value) -> Value raise {
  let table = [
    (q_d_top_left, "top left"),
    (q_d_top_center, "top center"),
    (q_d_top_right, "top right"),
    (q_d_center_left, "center left"),
    (q_d_center, "center center"),
    (q_d_center_right, "center right"),
    (q_d_bottom_left, "bottom left"),
    (q_d_bottom_center, "bottom center"),
    (q_d_bottom_right, "bottom right"),
  ]
  for kv in table {
    if eq(val, kv.0) {
      return share_draw__set_option(q_d_key_pos, Str(kv.1))
    }
  }
  merr("draw: illegal key position specification", [])
}

///|
fn update_terminal(val : Value) -> Value raise {
  let terms = list([
    q_d_screen, q_d_png, q_d_pngcairo, q_d_jpg, q_d_gif, q_d_eps, q_d_eps_color,
    q_d_canvas, q_d_epslatex, q_d_epslatex_standalone, q_d_svg, q_d_tikz, q_d_tikz_standalone,
    q_d_x11, q_d_qt, q_d_dumb, q_d_dumb_file, q_d_pdf, q_d_pdfcairo, q_d_wxt, q_d_animated_gif,
    q_d_windows, q_d_multipage_pdfcairo, q_d_multipage_pdf, q_d_multipage_eps, q_d_multipage_eps_color,
    q_d_aquaterm, q_d_tiff, q_d_vrml, q_d_obj, q_d_stl, q_d_pnm, q_d_ply, q_d_cairolatex_pdf,
    q_d_cairolatex_pdf_standalone,
  ])
  if member(val, terms).truthy() {
    let mut val = val
    if eq(val, q_d_png) && symval(q_d_draw_use_pngcairo).truthy() {
      val = q_d_pngcairo
    }
    share_draw__set_option(q_d_terminal, val) |> ignore
    set(q_ear_draw_terminal_number, Str(""))
  } else if d_listp(val).truthy() &&
    share_draw__mlength(val) == 2 &&
    member(
      cadr(val),
      list([q_d_screen, q_d_wxt, q_d_aquaterm, q_d_qt, q_d_windows]),
    ).truthy() &&
    integerp(caddr(val)) &&
    num_ge(caddr(val), Fix(0L)) {
    share_draw__set_option(q_d_terminal, cadr(val)) |> ignore
    set(q_ear_draw_terminal_number, caddr(val))
  } else {
    merr("draw: illegal terminal specification: ~M", [val])
  }
}

///|
fn update_transform(val : Value) -> Value raise {
  let nth_m = (s : Value, l : Value) => funcall(s, [l])
  if equal(val, q_d_none) {
    share_draw__set_option(q_d_transform, q_d_none) |> ignore
    set(q_ear_draw_transform_dimensions, Fix(0L)) |> ignore
    set(q_ear_draw_transform_f1, Nil) |> ignore
    set(q_ear_draw_transform_f2, Nil) |> ignore
    set(q_ear_draw_transform_f3, Nil)
  } else if d_listp(val).truthy() &&
    share_draw__mlength(val) == 4 &&
    d_subsetp(
      d_union(
        list([
          d_setify(d_listofvars(d_first(val))),
          d_setify(d_listofvars(nth_m(q_d_second, val))),
        ]),
      ),
      d_setify(
        list([list1(q_mlist), nth_m(q_d_third, val), nth_m(q_d_fourth, val)]),
      ),
    ).truthy() {
    // transformation in 2d
    let vars = list([list1(q_mlist), nth_m(q_d_third, val), nth_m(q_d_fourth, val)])
    share_draw__set_option(q_d_transform, val) |> ignore
    set(q_ear_draw_transform_dimensions, Fix(2L)) |> ignore
    set(
      q_ear_draw_transform_f1,
      share_draw__coerce_float_fun(d_first(val), vars),
    )
    |> ignore
    set(
      q_ear_draw_transform_f2,
      share_draw__coerce_float_fun(nth_m(q_d_second, val), vars),
    )
  } else if d_listp(val).truthy() &&
    share_draw__mlength(val) == 6 &&
    d_subsetp(
      d_union(
        list([
          d_setify(d_listofvars(d_first(val))),
          d_setify(d_listofvars(nth_m(q_d_second, val))),
          d_setify(d_listofvars(nth_m(q_d_third, val))),
        ]),
      ),
      d_setify(
        list([
          list1(q_mlist),
          nth_m(q_d_fourth, val),
          nth_m(q_d_fifth, val),
          nth_m(q_d_sixth, val),
        ]),
      ),
    ).truthy() {
    // transformation in 3d
    let vars = list([
      list1(q_mlist),
      nth_m(q_d_fourth, val),
      nth_m(q_d_fifth, val),
      nth_m(q_d_sixth, val),
    ])
    share_draw__set_option(q_d_transform, val) |> ignore
    set(q_ear_draw_transform_dimensions, Fix(3L)) |> ignore
    set(
      q_ear_draw_transform_f1,
      share_draw__coerce_float_fun(d_first(val), vars),
    )
    |> ignore
    set(
      q_ear_draw_transform_f2,
      share_draw__coerce_float_fun(nth_m(q_d_second, val), vars),
    )
    |> ignore
    set(
      q_ear_draw_transform_f3,
      share_draw__coerce_float_fun(nth_m(q_d_third, val), vars),
    )
  } else {
    merr("draw: illegal transform definition", [])
  }
}

///|
fn check_enhanced3d_model(grobj : Value, lis : Value) -> Value raise {
  if position(symval(q_ear_draw_enhanced3d_type), lis) < 0 {
    merror(
      format(Nil, "draw (~a): unacceptable enhanced3d model", [grobj]),
      Nil,
    )
    |> ignore
  }
  Nil
}

///|
fn update_enhanced3d_expression(vars : Value) -> Value raise {
  let texture = get_option(q_d_enhanced3d)
  if !d_subsetp(d_setify(d_listofvars(texture)), d_setify(vars)).truthy() {
    merr("draw: incompatible variables in enhanced3d expression", []) |> ignore
  }
  set(q_ear_draw_enhanced3d_fun, share_draw__coerce_float_fun(texture, vars))
}

///|
/// Shared body of UPDATE-ENHANCED3D and UPDATE-ISOLINES.
fn share_draw__update_texture(
  val : Value,
  opt : Value,
  qtype : Value,
  qfun : Value,
  what : String,
) -> Value raise {
  let nth_m = (s : Value, l : Value) => funcall(s, [l])
  if val is Nil || equal(val, q_d_none) {
    share_draw__set_option(opt, q_d_none) |> ignore
    set(qtype, Fix(0L)) |> ignore
    set(qfun, Nil)
  } else if equal(val, t) {
    let model = mk(q_mlist, [q_d_z, q_d_x, q_d_y, q_d_z])
    share_draw__set_option(opt, model) |> ignore
    set(qtype, Fix(3L)) |> ignore
    set(
      qfun,
      share_draw__coerce_float_fun(
        d_first(model),
        list([
          list1(q_mlist),
          nth_m(q_d_second, model),
          nth_m(q_d_third, model),
          nth_m(q_d_fourth, model),
        ]),
      ),
    )
  } else if d_listp(val).truthy() &&
    d_subsetp(d_setify(d_listofvars(d_first(val))), d_setify(d_rest(val))).truthy() {
    match share_draw__mlength(val) {
      2 => {
        share_draw__set_option(opt, val) |> ignore
        set(qtype, Fix(1L)) |> ignore
        set(
          qfun,
          share_draw__coerce_float_fun(
            d_first(val),
            list([list1(q_mlist), nth_m(q_d_second, val)]),
          ),
        )
      }
      3 => {
        share_draw__set_option(opt, val) |> ignore
        set(qtype, Fix(2L)) |> ignore
        set(
          qfun,
          share_draw__coerce_float_fun(
            d_first(val),
            list([list1(q_mlist), nth_m(q_d_second, val), nth_m(q_d_third, val)]),
          ),
        )
      }
      4 => {
        share_draw__set_option(opt, val) |> ignore
        set(qtype, Fix(3L)) |> ignore
        set(
          qfun,
          share_draw__coerce_float_fun(
            d_first(val),
            list([
              list1(q_mlist),
              nth_m(q_d_second, val),
              nth_m(q_d_third, val),
              nth_m(q_d_fourth, val),
            ]),
          ),
        )
      }
      _ => merr("draw: illegal length of " + what, [])
    }
  } else if !d_listp(val).truthy() {
    // the option is given an expression without explicit declaration of
    // its variables. Each graphic object must check for them.
    share_draw__set_option(opt, val) |> ignore
    set(qtype, Fix(99L)) |> ignore
    set(qfun, Nil)
  } else {
    merr("draw: illegal " + what + " definition", [])
  }
}

///|
fn update_enhanced3d(val : Value) -> Value raise {
  share_draw__update_texture(
    val,
    q_d_enhanced3d,
    q_ear_draw_enhanced3d_type,
    q_ear_draw_enhanced3d_fun,
    "enhanced3d",
  )
}

///|
fn check_isolines_model(grobj : Value, lis : Value) -> Value raise {
  if position(symval(q_ear_draw_isolines_type), lis) < 0 {
    merror(format(Nil, "draw (~a): unacceptable isolines model", [grobj]), Nil)
    |> ignore
  }
  Nil
}

///|
fn update_isolines_expression(vars : Value) -> Value raise {
  let texture = get_option(q_d_isolines)
  if !d_subsetp(d_setify(d_listofvars(texture)), d_setify(vars)).truthy() {
    merr("draw: incompatible variables in isolines expression", []) |> ignore
  }
  set(q_ear_draw_isolines_fun, share_draw__coerce_float_fun(texture, vars))
}

///|
fn update_isolines(val : Value) -> Value raise {
  share_draw__update_texture(
    val,
    q_d_isolines,
    q_ear_draw_isolines_type,
    q_ear_draw_isolines_fun,
    "isolines",
  )
}

///|
/// Update contour (Gnuplot) and isolines (VTK) levels.
fn update_contour_isolines(opt : Value, val : Value) -> Value raise {
  if integerp(val) && num_gt(val, Fix(0L)) {
    share_draw__set_option(opt, val)
  } else if d_listp(val).truthy() && share_draw__mlength(val) == 3 {
    let ini = d_float(nth(1, val))
    let step = d_float(nth(2, val))
    let end = d_float(nth(3, val))
    if num_lt(ini, end) && num_lt(step, num_sub(end, ini)) {
      share_draw__set_option(
        opt,
        format(Nil, "incremental ~a,~a,~a", [ini, step, end]),
      )
    } else {
      merr("draw: illegal contour level incremental description: ~M ", [val])
    }
  } else if d_setp(val).truthy() && !d_emptyp(val).truthy() {
    let pts = mapcar(z => d_float(z), rest(val))
    let mut str = "discrete "
    for num in pts.iter() {
      str = str + " " + format_to_string("~a,", [num])
    }
    share_draw__set_option(opt, Str(string_trim(",", str)))
  } else {
    merr("draw: unknown contour level description: ~M ", [val])
  }
}

///|
fn update_boolean_option(opt : Value, val : Value) -> Value raise {
  if equal(val, t) || val is Nil {
    share_draw__set_option(opt, val)
  } else {
    merr("draw: non boolean value: ~M ", [val])
  }
}

///|
fn update_positive_integer(opt : Value, val : Value) -> Value raise {
  if integerp(val) && num_gt(val, Fix(0L)) {
    share_draw__set_option(opt, val)
  } else {
    merr("draw: non positive integer: ~M ", [val])
  }
}

///|
fn update_positive_float(opt : Value, val : Value) -> Value raise {
  let val = d_float(val)
  if numberp(val) && num_gt(val, Fix(0L)) {
    share_draw__set_option(opt, val)
  } else {
    merr("draw: Non positive number: ~M ", [val])
  }
}

///|
fn update_nonnegative_float(opt : Value, val : Value) -> Value raise {
  let val = d_float(val)
  if numberp(val) && num_ge(val, Fix(0L)) {
    share_draw__set_option(opt, val)
  } else {
    merr("draw: Not a non-negative number: ~M ", [val])
  }
}

///|
fn update_view(val : Value) -> Value raise {
  if eql(val, q_d_map) {
    share_draw__set_option(q_d_view, val)
  } else if d_listp(val).truthy() && share_draw__mlength(val) == 2 {
    let rv = d_float(cadr(val))
    let rh = d_float(caddr(val))
    if !(numberp(rv) && num_ge(rv, Fix(0L)) && num_le(rv, Fix(360L))) {
      merr("draw: vertical rotation angle must be in [0, 360]", []) |> ignore
    }
    if !(numberp(rh) && num_ge(rh, Fix(0L)) && num_le(rh, Fix(360L))) {
      merr("draw: horizontal rotation angle must be in [0, 360]", []) |> ignore
    }
    share_draw__set_option(q_d_view, list2(rv, rh))
  } else {
    merr("draw: illegal view specification ~M", [val])
  }
}

///|
fn update_interpolate_color(val : Value) -> Value raise {
  if val is Nil {
    share_draw__set_option(q_d_interpolate_color, Str("depthorder"))
  } else if equal(val, t) {
    share_draw__set_option(q_d_interpolate_color, Str("interpolate 0, 0"))
  } else if d_listp(val).truthy() && share_draw__mlength(val) == 2 {
    let x = d_float(cadr(val))
    let y = d_float(caddr(val))
    if !(numberp(x) && numberp(y)) {
      merr("draw: interpolate_color parameters must be numbers", []) |> ignore
    }
    share_draw__set_option(
      q_d_interpolate_color,
      format(Nil, "interpolate ~a,~a", [x, y]),
    )
  } else {
    merr("draw: illegal interpolate_color specification ~M", [val])
  }
}

///|
fn update_allocation(val : Value) -> Value raise {
  if d_listp(val).truthy() &&
    share_draw__mlength(val) == 2 &&
    every(
      z => d_listp(z).truthy() && share_draw__mlength(z) == 2,
      rest(val),
    ) {
    let fval = rest(d_float(val))
    let cls = list([
      cadar(fval),
      car(cddar(fval)),
      car(cdadr(fval)),
      caddr(cadr(fval)),
    ])
    if every(
        z => lfloat(z).truthy() &&
          num_ge(z, Flo(0.0)) &&
          num_le(z, Flo(1.0)),
        cls,
      ) {
      share_draw__set_option(q_d_allocation, cls)
    } else {
      merr("draw: allocations must me given in relative values", [])
    }
  } else {
    merr("draw: illegal allocation format ~M", [val])
  }
}

///|
fn update_dimensions(val : Value) -> Value raise {
  if d_listp(val).truthy() && share_draw__mlength(val) == 2 {
    let cls = rest(val)
    if every(z => numberp(z) && num_gt(z, Fix(0L)), cls) {
      share_draw__set_option(q_d_dimensions, cls)
    } else {
      merr("draw: illegal dimensions", [])
    }
  } else {
    merr("draw: illegal dimensions format ~M", [val])
  }
}

///|
fn update_pointtype(val : Value) -> Value raise {
  if integerp(val) && num_ge(val, Fix(-1L)) {
    share_draw__set_option(q_d_point_type, val)
  } else {
    let shapes = list([
      q_d_none, q_d_dot, q_d_plus, q_d_multiply, q_d_asterisk, q_d_square, q_d_filled_square,
      q_d_circle, q_d_filled_circle, q_d_up_triangle, q_d_filled_up_triangle, q_d_down_triangle,
      q_d_filled_down_triangle, q_d_diamant, q_d_filled_diamant, q_d_sphere, q_d_cube,
      q_d_cylinder, q_d_cone,
    ])
    let pos = position(val, shapes)
    if pos >= 0 {
      share_draw__set_option(q_d_point_type, int(pos - 1))
    } else {
      merr("draw: illegal point type: ~M ", [val])
    }
  }
}

///|
fn update_string(opt : Value, val : Value) -> Value raise {
  share_draw__set_option(opt, d_sconcat(list1(val)))
}

///|
fn update_opacity(val : Value) -> Value raise {
  let value = d_float(val)
  if !floatp(value) || num_gt(value, Fix(1L)) || num_lt(value, Fix(0L)) {
    merr("draw: illegal opacity value: ~M ", [val]) |> ignore
  }
  share_draw__set_option(q_d_opacity, value)
}

///|
/// Color of a palette entry: hex code or color name.
fn share_draw__palette_color(str : String) -> Value raise {
  if correct_color_hex(Str(str)).truthy() {
    share_draw__hex_to_numeric_list(Str(str))
  } else if correct_color_name(Str(str)).truthy() {
    share_draw__hex_to_numeric_list(share_draw__color_table_get(str))
  } else {
    merr("draw: illegal color in palette description", [])
  }
}

///|
fn update_palette(val : Value) -> Value raise {
  // defined as $color, $gray, [f1,f2,f3], with -36<=fi<=36,
  // or a list of triplets defining a user palette.
  if memq(val, list2(q_d_color, q_d_gray)).truthy() {
    share_draw__set_option(q_d_palette, val)
  } else if d_listp(val).truthy() &&
    share_draw__mlength(val) == 3 &&
    every(
      x => integerp(x) && num_le(num_abs(x), Fix(36L)),
      cdr(val),
    ) {
    share_draw__set_option(q_d_palette, rest(val))
  } else if d_listp(val).truthy() && !d_listp(cadr(val)).truthy() {
    // user defined palette without transparency
    let palette = cdr(val)
    let col = Collector::new()
    for k in palette.iter() {
      let str = share_draw__atom_to_downcased_string(k)
      col.add(share_draw__palette_color(str))
    }
    share_draw__set_option(q_d_palette, col.result())
  } else if d_listp(val).truthy() &&
    every(x => d_listp(x).truthy() && length(x) == 3, cdr(val)) {
    // user defined palette with transparency
    let palette = cdr(val)
    let col = Collector::new()
    for k in palette.iter() {
      let str = share_draw__atom_to_downcased_string(d_first(k))
      let color = share_draw__palette_color(str)
      let transparency = d_float(funcall(q_d_second, [k]))
      if num_lt(transparency, Fix(0L)) ||
        num_gt(transparency, Fix(1L)) ||
        !floatp(transparency) {
        merr("draw: illegal transparency in palette description", []) |> ignore
      }
      col.add(append(color, list1(transparency)))
    }
    share_draw__set_option(q_d_palette, col.result())
  } else {
    merr("draw: illegal palette description: ~M", [val])
  }
}

///|
/// Update line_type and line-axes. Negative indices indicate the number of
/// faces to be drawn in case of tubes. Default number of faces is 8.
fn update_linestyle(opt : Value, val : Value) -> Value raise {
  if atom(val) {
    let table = [
      (q_d_dots, 0L),
      (q_d_solid, 1L),
      (q_d_dashes, 2L),
      (q_d_short_dashes, 3L),
      (q_d_short_long_dashes, 4L),
      (q_d_short_short_long_dashes, 5L),
      (q_d_dot_dash, 6L),
      (q_d_tube, -8L),
    ]
    for kv in table {
      if eql(val, kv.0) {
        return share_draw__set_option(opt, Fix(kv.1))
      }
    }
    if numberp(val) {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal line type: ~M", [val])
    }
  } else if d_listp(val).truthy() &&
    share_draw__mlength(val) == 2 &&
    equal(d_first(val), q_d_tube) &&
    integerp(funcall(q_d_second, [val])) &&
    num_gt(funcall(q_d_second, [val]), Fix(2L)) {
    share_draw__set_option(opt, num_neg(funcall(q_d_second, [val])))
  } else {
    merr("draw: unknown line type: ~M", [val])
  }
}

///|
fn update_pointsjoined(val : Value) -> Value raise {
  if member(val, list([t, Nil, q_d_impulses])).truthy() {
    share_draw__set_option(q_d_points_joined, val)
  } else {
    merr("draw: illegal points_joined option: ~M ", [val])
  }
}

///|
/// Capping option: a list of two elements, false and/or true.
fn update_capping(val : Value) -> Value raise {
  let nil_t = list2(Nil, t)
  if d_listp(val).truthy() &&
    share_draw__mlength(val) == 2 &&
    member(d_first(val), nil_t).truthy() &&
    member(funcall(q_d_second, [val]), nil_t).truthy() {
    share_draw__set_option(q_d_capping, val)
  } else if member(val, nil_t).truthy() {
    share_draw__set_option(q_d_capping, mk_simp(q_mlist, [val, val]))
  } else {
    merr("draw: illegal capping: ~M ", [val])
  }
}

///|
fn ini_local_option_variables() -> Value raise {
  set(q_ear_draw_transform_dimensions, Fix(0L)) |> ignore
  set(q_ear_draw_transform_f1, Nil) |> ignore
  set(q_ear_draw_transform_f2, Nil) |> ignore
  set(q_ear_draw_transform_f3, Nil) |> ignore
  set(q_ear_draw_enhanced3d_type, Fix(0L)) |> ignore
  set(q_ear_draw_enhanced3d_fun, Nil) |> ignore
  set(q_ear_draw_isolines_type, Fix(0L)) |> ignore
  set(q_ear_draw_isolines_fun, Nil)
}

///|
/// Sets default values to global options.
fn ini_global_options() -> Value raise {
  share_draw__set_option(q_d_columns, Fix(1L)) |> ignore
  share_draw__set_option(q_d_terminal, q_d_screen) |> ignore
  share_draw__set_option(q_d_key_pos, Nil) |> ignore
  share_draw__set_option(q_d_dimensions, share_draw__lit_dimensions) |> ignore
  share_draw__set_option(q_d_file_name, Str("maxima_out")) |> ignore
  share_draw__set_option(
    q_d_gnuplot_file_name,
    format(Nil, "maxout~d.gnuplot", [share_draw__getpid()]),
  )
  |> ignore
  share_draw__set_option(
    q_d_data_file_name,
    format(Nil, "data~d.gnuplot", [share_draw__getpid()]),
  )
  |> ignore
  share_draw__set_option(q_d_delay, Fix(5L))
}

///|
let share_draw__lit_dimensions : Value = list2(Fix(600L), Fix(500L))

///|
/// Tics option value of UPDATE-GR-OPTION.
fn share_draw__update_tics(opt : Value, val : Value) -> Value raise {
  if member(val, list2(q_d_none, Nil)).truthy() {
    return share_draw__set_option(opt, Nil)
  }
  if member(val, list2(q_d_auto, t)).truthy() {
    return share_draw__set_option(opt, Str("autofreq"))
  }
  let val = d_float(val)
  if numberp(val) && num_gt(val, Fix(0L)) {
    // increment
    share_draw__set_option(opt, val)
  } else if d_listp(val).truthy() &&
    share_draw__mlength(val) == 3 &&
    num_lt(cadr(val), cadddr(val)) &&
    num_gt(caddr(val), Fix(0L)) &&
    num_lt(caddr(val), num_sub(cadddr(val), cadr(val))) {
    // [ini,incr,end]
    share_draw__set_option(
      opt,
      format(Nil, "~a,~a,~a", [cadr(val), caddr(val), cadddr(val)]),
    )
  } else if d_setp(val).truthy() && every(z => numberp(z), cdr(val)) {
    // {n1,n2,n3,...}
    let mut str = ""
    for k in cdr(val).iter() {
      str = str + format_to_string("~a,", [k])
    }
    share_draw__set_option(opt, Str("(" + string_right_trim(",", str) + ")"))
  } else if d_setp(val).truthy() &&
    every(
      z => d_listp(z).truthy() &&
        share_draw__mlength(z) == 2 &&
        numberp(caddr(z)),
      cdr(val),
    ) {
    // {[lab1,n1],[lab2,n2],...}
    let mut str = ""
    for k in cdr(val).iter() {
      str = str + format_to_string("'~a' ~a,", [cadr(k), caddr(k)])
    }
    share_draw__set_option(opt, Str("(" + string_right_trim(",", str) + ")"))
  } else {
    merr("draw: illegal tics allocation: ~M", [val])
  }
}

///|
/// Range option value of UPDATE-GR-OPTION.
fn share_draw__update_range(opt : Value, val : Value) -> Value raise {
  if member(val, list2(q_d_auto, Nil)).truthy() {
    share_draw__set_option(opt, Nil)
  } else if !d_listp(val).truthy() || share_draw__mlength(val) != 2 {
    merr("draw: illegal range: ~M ", [val])
  } else {
    let fval1 = d_float(cadr(val))
    let fval2 = d_float(caddr(val))
    if !floatp(fval1) || !floatp(fval2) || num_lt(fval2, fval1) {
      merr("draw: illegal values in range specification", [])
    } else if share_draw__mlength(val) == 2 {
      // it's a trick: length 2 => user change
      share_draw__set_option(opt, list2(fval1, fval2))
    } else {
      share_draw__set_option(opt, list([fval1, fval2, Fix(0L)]))
    }
  }
}

///|
/// Grid option value of UPDATE-GR-OPTION.
fn share_draw__update_grid(opt : Value, val : Value) -> Value raise {
  if val is Nil {
    share_draw__set_option(opt, list2(Fix(0L), Fix(0L)))
  } else if eq(val, t) {
    share_draw__set_option(opt, list2(Fix(1L), Fix(1L)))
  } else if !d_listp(val).truthy() || share_draw__mlength(val) != 2 {
    merr("draw: illegal grid lines specification: ~M ", [val])
  } else {
    let fval1 = d_float(cadr(val))
    let fval2 = d_float(caddr(val))
    if !floatp(fval1) ||
      !floatp(fval2) ||
      num_lt(fval1, Fix(1L)) ||
      num_lt(fval2, Fix(1L)) {
      merr("grid: illegal grid lines specification", [])
    } else {
      share_draw__set_option(
        opt,
        list2(funcall(q_d_round, [fval1]), funcall(q_d_round, [fval2])),
      )
    }
  }
}

///|
/// User preamble option value of UPDATE-GR-OPTION.
fn share_draw__update_user_preamble(opt : Value, val : Value) -> Value raise {
  let mut str : Value = Str("")
  if d_atom(val).truthy() {
    str = val
  } else if d_listp(val).truthy() {
    for st in rest(val).iter() {
      if !d_atom(st).truthy() {
        merr("draw: user preamble ~M should be a string", [st]) |> ignore
      }
      let s = lstring(str)
      str = Str(s + format_to_string(if s == "" { "~a" } else { "~%~a" }, [st]))
    }
  } else {
    merr("draw: illegal user preamble especification", []) |> ignore
  }
  share_draw__set_option(opt, str)
}

///|
/// Sets new values to graphic options.
fn update_gr_option(opt : Value, val : Value) -> Value raise {
  let opt_is = (opts : Array[Value]) => opts.iter().any(o => eql(opt, o))
  if opt_is([q_d_allocation]) {
    update_allocation(val)
  } else if opt_is([q_d_dimensions]) {
    update_dimensions(val)
  } else if opt_is([q_d_fill_density]) {
    // in range [0, 1]
    let val = d_float(val)
    if numberp(val) && num_ge(val, Fix(0L)) && num_le(val, Fix(1L)) {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: fill_density must be a number in [0, 1]", [])
    }
  } else if opt_is([
      q_d_line_width, q_d_head_length, q_d_head_angle, q_d_xaxis_width, q_d_yaxis_width,
      q_d_zaxis_width,
    ]) {
    update_positive_float(opt, val)
  } else if opt_is([q_d_xyplane]) {
    // defined as real number or false
    let val = d_float(val)
    if numberp(val) || val is Nil {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal xyplane allocation: ~M ", [val])
    }
  } else if opt_is([q_d_point_size]) {
    update_nonnegative_float(opt, val)
  } else if opt_is([q_d_points_joined]) {
    update_pointsjoined(val)
  } else if opt_is([q_d_colorbox]) {
    // defined as true, false or string
    if member(val, list2(t, Nil)).truthy() || stringp(val) {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal colorbox option: ~M ", [val])
    }
  } else if opt_is([q_d_line_type, q_d_xaxis_type, q_d_yaxis_type, q_d_zaxis_type]) {
    update_linestyle(opt, val)
  } else if opt_is([q_d_capping]) {
    update_capping(val)
  } else if opt_is([q_d_point_type]) {
    update_pointtype(val)
  } else if opt_is([
      q_d_columns, q_d_nticks, q_d_adapt_depth, q_d_xu_grid, q_d_yv_grid, q_d_delay,
      q_d_x_voxel, q_d_y_voxel, q_d_z_voxel, q_d_font_size,
    ]) {
    update_positive_integer(opt, val)
  } else if opt_is([q_d_contour_levels, q_d_isolines_levels]) {
    update_contour_isolines(opt, val)
  } else if opt_is([q_d_opacity]) {
    update_opacity(val)
  } else if opt_is([
      q_d_transparent, q_d_border, q_d_logx, q_d_logx_secondary, q_d_logy, q_d_logy_secondary,
      q_d_logz, q_d_logcb, q_d_head_both, q_d_xaxis_secondary, q_d_yaxis_secondary,
      q_d_axis_bottom, q_d_axis_left, q_d_axis_top, q_d_axis_right, q_d_axis_3d,
      q_d_surface_hide, q_d_xaxis, q_d_yaxis, q_d_zaxis, q_d_unit_vectors, q_d_xtics_rotate,
      q_d_ytics_rotate, q_d_xtics_secondary_rotate, q_d_ytics_secondary_rotate, q_d_ztics_rotate,
      q_d_xtics_axis, q_d_ytics_axis, q_d_xtics_secondary_axis, q_d_ytics_secondary_axis,
      q_d_ztics_axis, q_d_draw_realpart, q_d_wired_surface,
    ]) {
    update_boolean_option(opt, val)
  } else if opt_is([q_d_filled_func]) {
    share_draw__set_option(opt, val)
  } else if opt_is([q_d_transform]) {
    update_transform(val)
  } else if opt_is([q_d_enhanced3d]) {
    update_enhanced3d(val)
  } else if opt_is([q_d_isolines]) {
    update_isolines(val)
  } else if opt_is([
      q_d_xtics, q_d_ytics, q_d_xtics_secondary, q_d_ytics_secondary, q_d_ztics, q_d_cbtics,
    ]) {
    share_draw__update_tics(opt, val)
  } else if opt_is([q_d_terminal]) {
    update_terminal(val)
  } else if opt_is([q_d_key_pos]) {
    update_key_pos(val)
  } else if opt_is([q_d_zlabel_rotate]) {
    if member(val, list([t, Nil, q_d_auto])).truthy() {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal zlabel_rotate option: ~M", [val])
    }
  } else if opt_is([q_d_head_type]) {
    if member(val, list([q_d_filled, q_d_empty, q_d_nofilled])).truthy() {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal head type for vectors: ~M", [val])
    }
  } else if opt_is([q_d_contour]) {
    if member(val, list([q_d_none, q_d_base, q_d_surface, q_d_both, q_d_map])).truthy() {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal contour allocation: ~M", [val])
    }
  } else if opt_is([q_d_proportional_axes]) {
    if member(val, list([q_d_none, q_d_xy, q_d_xyz])).truthy() {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal proportional_axes specification", [])
    }
  } else if opt_is([q_d_error_type]) {
    if member(val, list([q_d_x, q_d_y, q_d_xy, q_d_boxes])).truthy() {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal error_type specification", [])
    }
  } else if opt_is([q_d_label_alignment]) {
    if member(val, list([q_d_center, q_d_left, q_d_right])).truthy() {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal label alignment: ~M", [val])
    }
  } else if opt_is([q_d_label_orientation]) {
    if member(val, list([q_d_horizontal, q_d_vertical])).truthy() {
      share_draw__set_option(opt, val)
    } else {
      merr("draw: illegal label orientation: ~M", [val])
    }
  } else if opt_is([
      q_d_key, q_d_file_name, q_d_xy_file, q_d_title, q_d_xlabel, q_d_ylabel, q_d_zlabel,
      q_d_xlabel_secondary, q_d_ylabel_secondary, q_d_font, q_d_gnuplot_file_name,
      q_d_data_file_name,
    ]) {
    update_string(opt, val)
  } else if opt_is([q_d_user_preamble]) {
    // defined as a string or a Maxima list of strings
    share_draw__update_user_preamble(opt, val)
  } else if opt_is([
      q_d_xrange, q_d_yrange, q_d_xrange_secondary, q_d_yrange_secondary, q_d_zrange,
      q_d_cbrange,
    ]) {
    // defined as a Maxima list with two numbers in increasing order
    share_draw__update_range(opt, val)
  } else if opt_is([q_d_grid]) {
    // defined as a Maxima list with two numbers. 0 0 means "off",
    // >0 >0 means "on with n grid lines per tick"
    share_draw__update_grid(opt, val)
  } else if opt_is([q_d_ip_grid, q_d_ip_grid_in]) {
    if !d_listp(val).truthy() {
      merr("draw: illegal value for grid", [])
    } else if !(integerp(d_first(val)) && integerp(funcall(q_d_second, [val]))) {
      merr("draw: illegal value for grid", [])
    } else {
      share_draw__set_option(opt, val)
    }
  } else if opt_is([q_d_palette]) {
    update_palette(val)
  } else if opt_is([
      q_d_color, q_d_fill_color, q_d_xaxis_color, q_d_yaxis_color, q_d_zaxis_color,
      q_d_background_color,
    ]) {
    update_color(opt, val)
  } else if opt_is([q_d_view]) {
    update_view(val)
  } else if opt_is([q_d_interpolate_color]) {
    update_interpolate_color(val)
    // DEPRECATED OPTIONS
  } else if opt_is([q_d_tube_extremes]) {
    d_print(
      list1(Str("Warning: 'tube_extremes' is deprecated, using 'capping' instead...")),
    )
    |> ignore
    update_capping(
      share_draw__substitute(Nil, q_d_open, share_draw__substitute(t, q_d_closed, val)),
    )
  } else if opt_is([q_d_file_bgcolor]) {
    d_print(
      list1(
        Str("Warning: 'file_bgcolor' is deprecated, using 'background_color' instead..."),
      ),
    )
    |> ignore
    update_color(q_d_background_color, val)
  } else if opt_is([q_d_rot_vertical]) {
    d_print(list1(Str("Warning: 'rot_vertical' is deprecated, using 'view' instead...")))
    |> ignore
    update_view(list([list1(q_mlist), val, second(get_option(q_d_view))]))
  } else if opt_is([q_d_rot_horizontal]) {
    d_print(
      list1(Str("Warning: 'rot_horizontal' is deprecated, using 'view' instead...")),
    )
    |> ignore
    update_view(list([list1(q_mlist), first(get_option(q_d_view)), val]))
  } else if opt_is([q_d_pic_width]) {
    d_print(
      list1(Str("Warning: 'pic_width' is deprecated, using 'dimensions' instead...")),
    )
    |> ignore
    update_dimensions(
      list([list1(q_mlist), val, second(get_option(q_d_dimensions))]),
    )
  } else if opt_is([q_d_pic_height]) {
    d_print(
      list1(Str("Warning: 'pic_height' is deprecated, using 'dimensions' instead...")),
    )
    |> ignore
    update_dimensions(
      list([list1(q_mlist), first(get_option(q_d_dimensions)), val]),
    )
  } else if opt_is([q_d_eps_width, q_d_pdf_width]) {
    d_print(
      list1(Str("Warning: 'eps_width' is deprecated, using 'dimensions' instead...")),
    )
    |> ignore
    update_dimensions(
      list([
        list1(q_mlist),
        num_mul(Fix(100L), val),
        second(get_option(q_d_dimensions)),
      ]),
    )
  } else if opt_is([q_d_eps_height, q_d_pdf_height]) {
    d_print(
      list1(Str("Warning: 'eps_height' is deprecated, using 'dimensions' instead...")),
    )
    |> ignore
    update_dimensions(
      list([
        list1(q_mlist),
        first(get_option(q_d_dimensions)),
        num_mul(Fix(100L), val),
      ]),
    )
  } else {
    merr("draw: unknown option ~M ", [opt])
  }
}

///|
/// CL (substitute new old sequence) on a list (non-destructive, EQL test).
fn share_draw__substitute(new : Value, old : Value, seq : Value) -> Value raise {
  mapcar(z => if eql(z, old) { new } else { z }, seq)
}

// ---------------------------------------------------------------------------
// OTHER COMMON GNUPLOT - VTK AUXILIARY FUNCTIONS

///|
fn near_equal(a : Value, b : Value) -> Value raise {
  let eps : Value = Flo(10.0e-14)
  lbool(num_lt(num_abs(num_sub(a, b)), eps))
}

///|
/// Copies multidimensional arrays.
fn copy_array(array : Value) -> Value raise {
  match array {
    Vec(a) => Vec({ data: a.data.copy(), dims: a.dims.copy(), fill: None, elt: a.elt })
    _ => raise LispError::SimpleError("copy-array: not an array")
  }
}

///|
/// Calculates surface-edge intersection by interpolation.
fn edge_interpolation(
  x1 : Value,
  y1 : Value,
  z1 : Value,
  x2 : Value,
  y2 : Value,
  z2 : Value,
  v1 : Value,
  v2 : Value,
) -> Value raise {
  let small : Value = Flo(0.00001)
  if num_lt(num_abs(v1), small) || num_lt(num_abs(num_sub(v1, v2)), small) {
    list([x1, y1, z1])
  } else if num_lt(num_abs(v2), small) {
    list([x2, y2, z2])
  } else {
    let m = num_div(num_neg(v1), num_sub(v2, v1))
    list([
      num_add(x1, num_mul(m, num_sub(x2, x1))),
      num_add(y1, num_mul(m, num_sub(y2, y1))),
      num_add(z1, num_mul(m, num_sub(z2, z1))),
    ])
  }
}

///|
fn flatten(lis : Value) -> Value raise {
  if atom(lis) {
    lis
  } else if listp(car(lis)) {
    append(flatten(car(lis)), flatten(cdr(lis)))
  } else {
    append(list1(car(lis)), flatten(cdr(lis)))
  }
}

///|
/// The marching cubes algorithm for implicit functions in 3d: the list of
/// vertices of the triangles approximating the surface EXPR.
fn find_triangles(
  expr : Value,
  par1 : Value,
  xmin : Value,
  xmax : Value,
  par2 : Value,
  ymin : Value,
  ymax : Value,
  par3 : Value,
  zmin : Value,
  zmax : Value,
) -> Value raise {
  let nx = get_option(q_d_x_voxel)
  let ny = get_option(q_d_y_voxel)
  let nz = get_option(q_d_z_voxel)
  let dx = num_div(num_sub(xmax, xmin), nx)
  let dy = num_div(num_sub(ymax, ymin), ny)
  let dz = num_div(num_sub(zmax, zmin), nz)
  let fcn = share_draw__coerce_float_fun(
    m_(d_lhs(expr), a2=d_rhs(expr)),
    list([list1(q_mlist), par1, par2, par3]),
  )
  let mut vert : Value = Nil
  let nx = to_int(nx)
  let ny = to_int(ny)
  let nz = to_int(nz)
  let px : Array[Value] = Array::make(nx + 1, Flo(0.0))
  let py : Array[Value] = Array::make(ny + 1, Flo(0.0))
  let pz : Array[Value] = Array::make(nz + 1, Flo(0.0))
  let mut oldval = make_array([nx + 1, ny + 1], elt="flonum")
  let newval = make_array([nx + 1, ny + 1], elt="flonum")
  // initialize coordinate arrays
  for i in 0..=nx {
    px[i] = num_add(xmin, num_mul(int(i), dx))
  }
  for j in 0..=ny {
    py[j] = num_add(ymin, num_mul(int(j), dy))
  }
  for k in 0..=nz {
    pz[k] = num_add(zmin, num_mul(int(k), dz))
  }
  // initialize first layer
  for i in 0..=nx {
    for j in 0..=ny {
      let fxy = funcall(fcn, [px[i], py[j], pz[0]])
      if floatp(fxy) {
        aset(oldval, [i, j], fxy) |> ignore
      } else {
        merr("draw3d (implicit): non real value", []) |> ignore
      }
    }
  }
  let triangles_table = symval(q_ear_i3d_triangles)
  // begin triangularization process
  for k in 1..=nz {
    // calculate node values in new layer
    for i in 0..=nx {
      for j in 0..=ny {
        let fxy = funcall(fcn, [px[i], py[j], pz[k]])
        if floatp(fxy) {
          aset(newval, [i, j], fxy) |> ignore
        } else {
          merr(
            "draw3d (implicit): check surface definition; non real value",
            [],
          )
          |> ignore
        }
      }
    }
    // analyze voxels in this slide
    for i in 0..<nx {
      for j in 0..<ny {
        let k_1 = k - 1
        let i_1 = i + 1
        let j_1 = j + 1
        let val = [
          aref(oldval, [i, j_1]),
          aref(oldval, [i_1, j_1]),
          aref(oldval, [i_1, j]),
          aref(oldval, [i, j]),
          aref(newval, [i, j_1]),
          aref(newval, [i_1, j_1]),
          aref(newval, [i_1, j]),
          aref(newval, [i, j]),
        ]
        let mut cubidx = 0
        for b in 0..<8 {
          if num_le(val[b], Flo(0.0)) {
            cubidx = cubidx | (1 << b)
          }
        }
        // edges intersecting the surface
        let triangles = aref1(triangles_table, cubidx)
        let vertices = (
          i1 : Int,
          j1 : Int,
          k1 : Int,
          i2 : Int,
          j2 : Int,
          k2 : Int,
          e1 : Int,
          e2 : Int,
        ) => edge_interpolation(
          px[i1],
          py[j1],
          pz[k1],
          px[i2],
          py[j2],
          pz[k2],
          val[e1],
          val[e2],
        )
        let mut e = 0
        while to_int(aref1(triangles, e)) != -1 {
          let v = match to_int(aref1(triangles, e)) {
            0 => vertices(i, j_1, k_1, i_1, j_1, k_1, 0, 1)
            1 => vertices(i_1, j_1, k_1, i_1, j, k_1, 1, 2)
            2 => vertices(i_1, j, k_1, i, j, k_1, 2, 3)
            3 => vertices(i, j, k_1, i, j_1, k_1, 3, 0)
            4 => vertices(i, j_1, k, i_1, j_1, k, 4, 5)
            5 => vertices(i_1, j_1, k, i_1, j, k, 5, 6)
            6 => vertices(i_1, j, k, i, j, k, 6, 7)
            7 => vertices(i, j, k, i, j_1, k, 7, 4)
            8 => vertices(i, j_1, k_1, i, j_1, k, 0, 4)
            9 => vertices(i_1, j_1, k_1, i_1, j_1, k, 1, 5)
            10 => vertices(i_1, j, k_1, i_1, j, k, 2, 6)
            11 => vertices(i, j, k_1, i, j, k, 3, 7)
            _ => Nil
          }
          vert = cons(v, vert)
          e = e + 1
        }
      }
    }
    // make oldval a copy of newval
    oldval = copy_array(newval)
  }
  vert
}

///|
/// This is the function to be called at Maxima level.
///   draw(gr2d(opt & obj))$ => a 2d plot, equivalent to draw2d(opt & obj)
///   draw(gr3d(opt & obj))$ => a 3d plot, equivalent to draw3d(opt & obj)
///   draw(gr2d(opt & obj),gr2d(opt & obj),gr3d(opt & obj),gr2d(opt & obj))$
///                            => four plots in one column
///   draw(terminal=png,columns=2,gr2d(opt & obj),gr3d(opt & obj))
///                            => png file with two plots side by side
fn d_draw(args : Value) -> Value raise {
  let r = symval(q_d_draw_renderer)
  if member(r, list2(q_d_gnuplot, q_d_gnuplot_pipes)).truthy() {
    apply(q_draw_gnuplot, args)
  } else if member(r, list([q_d_vtk, q_d_vtk6, q_d_vtk7])).truthy() {
    apply(q_draw_vtk, args)
  } else {
    merr("draw: unknown renderer ~M", [r])
  }
}

///|
/// Equivalent to draw(gr2d(opt & obj)).
fn d_draw2d(args : Value) -> Value raise {
  d_draw(list1(cons(list1(q_d_gr2d), args)))
}

///|
/// Equivalent to draw(gr3d(opt & obj)).
fn d_draw3d(args : Value) -> Value raise {
  let r = symval(q_d_draw_renderer)
  if member(r, list2(q_d_gnuplot, q_d_gnuplot_pipes)).truthy() {
    draw_gnuplot(list1(cons(list1(q_d_gr3d), args)))
  } else if member(r, list([q_d_vtk, q_d_vtk6, q_d_vtk7])).truthy() {
    draw_vtk(list1(cons(list1(q_d_gr3d), args)))
  } else {
    merr("draw: unknown renderer ~M", [r])
  }
}

///|
/// Top-level forms of grcommon.lisp.
fn init_share_grcommon() -> Unit raise {
  // draw.lisp, the loader of the draw system, does ($put '$draw 2 '$version)
  // before loading the system's files; the port's share loader runs only
  // the files of the group.
  d_put(q_d_draw, Fix(2L), q_d_version) |> ignore
  if !boundp(share_draw__q_plot_realpart) {
    set(share_draw__q_plot_realpart, t) |> ignore
  }
  if !boundp(q_ear_gr_options) {
    set(q_ear_gr_options, make_hash_table()) |> ignore
  }
  // The colors grcommon.lisp adds to *COLOR-TABLE* (plotcolors.lisp).
  let tab = symval(share_draw__q_color_table)
  for kv in share_draw__grcommon_colors {
    sethash(Str(kv.0), tab, Str(kv.1)) |> ignore
  }
}

///|
/// Colors grcommon.lisp adds to *COLOR-TABLE*.
let share_draw__grcommon_colors : Array[(String, String)] = [
  ("antiquewhite2", "#EEDFCC"),
  ("antiquewhite3", "#CDC0B0"),
  ("antiquewhite4", "#8B8378"),
  ("antiquewhite", "#FAEBD7"),
  ("aquamarine1", "#7FFFD4"),
  ("aquamarine2", "#76EEC6"),
  ("aquamarine3", "#66CDAA"),
  ("aquamarine4", "#458B74"),
  ("azure1", "#F0FFFF"),
  ("azure2", "#E0EEEE"),
  ("azure3", "#C1CDCD"),
  ("azure4", "#838B8B"),
  ("bisque1", "#FFE4C4"),
  ("bisque2", "#EED5B7"),
  ("bisque3", "#CDB79E"),
  ("bisque4", "#8B7D6B"),
  ("blue1", "#0000FF"),
  ("blue2", "#0000EE"),
  ("blue3", "#0000CD"),
  ("blue4", "#00008B"),
  ("brown1", "#FF4040"),
  ("brown2", "#EE3B3B"),
  ("brown3", "#CD3333"),
  ("brown4", "#8B2323"),
  ("burlywood1", "#FFD39B"),
  ("burlywood2", "#EEC591"),
  ("burlywood3", "#CDAA7D"),
  ("burlywood4", "#8B7355"),
  ("cadetblue1", "#98F5FF"),
  ("cadetblue2", "#8EE5EE"),
  ("cadetblue3", "#7AC5CD"),
  ("cadetblue4", "#53868B"),
  ("chartreuse1", "#7FFF00"),
  ("chartreuse2", "#76EE00"),
  ("chartreuse3", "#66CD00"),
  ("chartreuse4", "#458B00"),
  ("chocolate1", "#FF7F24"),
  ("chocolate2", "#EE7621"),
  ("chocolate3", "#CD661D"),
  ("chocolate4", "#8B4513"),
  ("coral1", "#FF7256"),
  ("coral2", "#EE6A50"),
  ("coral3", "#CD5B45"),
  ("coral4", "#8B3E2F"),
  ("cornsilk1", "#FFF8DC"),
  ("cornsilk2", "#EEE8CD"),
  ("cornsilk3", "#CDC8B1"),
  ("cornsilk4", "#8B8878"),
  ("cyan1", "#00FFFF"),
  ("cyan2", "#00EEEE"),
  ("cyan3", "#00CDCD"),
  ("cyan4", "#008B8B"),
  ("darkgoldenrod1", "#FFB90F"),
  ("darkgoldenrod2", "#EEAD0E"),
  ("darkgoldenrod3", "#CD950C"),
  ("darkgoldenrod4", "#8B6508"),
  ("darkolivegreen1", "#CAFF70"),
  ("darkolivegreen2", "#BCEE68"),
  ("darkolivegreen3", "#A2CD5A"),
  ("darkolivegreen4", "#6E8B3D"),
  ("darkorange1", "#FF7F00"),
  ("darkorange2", "#EE7600"),
  ("darkorange3", "#CD6600"),
  ("darkorange4", "#8B4500"),
  ("darkorchid1", "#BF3EFF"),
  ("darkorchid2", "#B23AEE"),
  ("darkorchid3", "#9A32CD"),
  ("darkorchid4", "#68228B"),
  ("darkseagreen1", "#C1FFC1"),
  ("darkseagreen2", "#B4EEB4"),
  ("darkseagreen3", "#9BCD9B"),
  ("darkseagreen4", "#698B69"),
  ("darkslategray1", "#97FFFF"),
  ("darkslategray2", "#8DEEEE"),
  ("darkslategray3", "#79CDCD"),
  ("darkslategray4", "#528B8B"),
  ("debianred", "#D70751"),
  ("deeppink1", "#FF1493"),
  ("deeppink2", "#EE1289"),
  ("deeppink3", "#CD1076"),
  ("deeppink4", "#8B0A50"),
  ("deepskyblue1", "#00BFFF"),
  ("deepskyblue2", "#00B2EE"),
  ("deepskyblue3", "#009ACD"),
  ("deepskyblue4", "#00688B"),
  ("dodgerblue1", "#1E90FF"),
  ("dodgerblue2", "#1C86EE"),
  ("dodgerblue3", "#1874CD"),
  ("dodgerblue4", "#104E8B"),
  ("firebrick1", "#FF3030"),
  ("firebrick2", "#EE2C2C"),
  ("firebrick3", "#CD2626"),
  ("firebrick4", "#8B1A1A"),
  ("gold1", "#FFD700"),
  ("gold2", "#EEC900"),
  ("gold3", "#CDAD00"),
  ("gold4", "#8B7500"),
  ("goldenrod1", "#FFC125"),
  ("goldenrod2", "#EEB422"),
  ("goldenrod3", "#CD9B1D"),
  ("goldenrod4", "#8B6914"),
  ("gray0", "#000000"),
  ("gray100", "#FFFFFF"),
  ("gray10", "#1A1A1A"),
  ("gray11", "#1C1C1C"),
  ("gray12", "#1F1F1F"),
  ("gray13", "#212121"),
  ("gray14", "#242424"),
  ("gray15", "#262626"),
  ("gray16", "#292929"),
  ("gray17", "#2B2B2B"),
  ("gray18", "#2E2E2E"),
  ("gray19", "#303030"),
  ("gray1", "#030303"),
  ("gray20", "#333333"),
  ("gray21", "#363636"),
  ("gray22", "#383838"),
  ("gray23", "#3B3B3B"),
  ("gray24", "#3D3D3D"),
  ("gray25", "#404040"),
  ("gray26", "#424242"),
  ("gray27", "#454545"),
  ("gray28", "#474747"),
  ("gray29", "#4A4A4A"),
  ("gray2", "#050505"),
  ("gray30", "#4D4D4D"),
  ("gray31", "#4F4F4F"),
  ("gray32", "#525252"),
  ("gray33", "#545454"),
  ("gray34", "#575757"),
  ("gray35", "#595959"),
  ("gray36", "#5C5C5C"),
  ("gray37", "#5E5E5E"),
  ("gray38", "#616161"),
  ("gray39", "#636363"),
  ("gray3", "#080808"),
  ("gray40", "#666666"),
  ("gray41", "#696969"),
  ("gray42", "#6B6B6B"),
  ("gray43", "#6E6E6E"),
  ("gray44", "#707070"),
  ("gray45", "#737373"),
  ("gray46", "#757575"),
  ("gray47", "#787878"),
  ("gray48", "#7A7A7A"),
  ("gray49", "#7D7D7D"),
  ("gray4", "#0A0A0A"),
  ("gray50", "#7F7F7F"),
  ("gray51", "#828282"),
  ("gray52", "#858585"),
  ("gray53", "#878787"),
  ("gray54", "#8A8A8A"),
  ("gray55", "#8C8C8C"),
  ("gray56", "#8F8F8F"),
  ("gray57", "#919191"),
  ("gray58", "#949494"),
  ("gray59", "#969696"),
  ("gray5", "#0D0D0D"),
  ("gray60", "#999999"),
  ("gray61", "#9C9C9C"),
  ("gray62", "#9E9E9E"),
  ("gray63", "#A1A1A1"),
  ("gray64", "#A3A3A3"),
  ("gray65", "#A6A6A6"),
  ("gray66", "#A8A8A8"),
  ("gray67", "#ABABAB"),
  ("gray68", "#ADADAD"),
  ("gray69", "#B0B0B0"),
  ("gray6", "#0F0F0F"),
  ("gray70", "#B3B3B3"),
  ("gray71", "#B5B5B5"),
  ("gray72", "#B8B8B8"),
  ("gray73", "#BABABA"),
  ("gray74", "#BDBDBD"),
  ("gray75", "#BFBFBF"),
  ("gray76", "#C2C2C2"),
  ("gray77", "#C4C4C4"),
  ("gray78", "#C7C7C7"),
  ("gray79", "#C9C9C9"),
  ("gray7", "#121212"),
  ("gray80", "#CCCCCC"),
  ("gray81", "#CFCFCF"),
  ("gray82", "#D1D1D1"),
  ("gray83", "#D4D4D4"),
  ("gray84", "#D6D6D6"),
  ("gray85", "#D9D9D9"),
  ("gray86", "#DBDBDB"),
  ("gray87", "#DEDEDE"),
  ("gray88", "#E0E0E0"),
  ("gray89", "#E3E3E3"),
  ("gray8", "#141414"),
  ("gray90", "#E5E5E5"),
  ("gray91", "#E8E8E8"),
  ("gray92", "#EBEBEB"),
  ("gray93", "#EDEDED"),
  ("gray94", "#F0F0F0"),
  ("gray95", "#F2F2F2"),
  ("gray96", "#F5F5F5"),
  ("gray97", "#F7F7F7"),
  ("gray98", "#FAFAFA"),
  ("gray99", "#FCFCFC"),
  ("gray9", "#171717"),
  ("green1", "#00FF00"),
  ("green2", "#00EE00"),
  ("green3", "#00CD00"),
  ("green4", "#008B00"),
  ("grey0", "#000000"),
  ("grey100", "#FFFFFF"),
  ("grey10", "#1A1A1A"),
  ("grey11", "#1C1C1C"),
  ("grey12", "#1F1F1F"),
  ("grey13", "#212121"),
  ("grey14", "#242424"),
  ("grey15", "#262626"),
  ("grey16", "#292929"),
  ("grey17", "#2B2B2B"),
  ("grey18", "#2E2E2E"),
  ("grey19", "#303030"),
  ("grey1", "#030303"),
  ("grey20", "#333333"),
  ("grey21", "#363636"),
  ("grey22", "#383838"),
  ("grey23", "#3B3B3B"),
  ("grey24", "#3D3D3D"),
  ("grey25", "#404040"),
  ("grey26", "#424242"),
  ("grey27", "#454545"),
  ("grey28", "#474747"),
  ("grey29", "#4A4A4A"),
  ("grey2", "#050505"),
  ("grey30", "#4D4D4D"),
  ("grey31", "#4F4F4F"),
  ("grey32", "#525252"),
  ("grey33", "#545454"),
  ("grey34", "#575757"),
  ("grey35", "#595959"),
  ("grey36", "#5C5C5C"),
  ("grey37", "#5E5E5E"),
  ("grey38", "#616161"),
  ("grey39", "#636363"),
  ("grey3", "#080808"),
  ("grey40", "#666666"),
  ("grey41", "#696969"),
  ("grey42", "#6B6B6B"),
  ("grey43", "#6E6E6E"),
  ("grey44", "#707070"),
  ("grey45", "#737373"),
  ("grey46", "#757575"),
  ("grey47", "#787878"),
  ("grey48", "#7A7A7A"),
  ("grey49", "#7D7D7D"),
  ("grey4", "#0A0A0A"),
  ("grey50", "#7F7F7F"),
  ("grey51", "#828282"),
  ("grey52", "#858585"),
  ("grey53", "#878787"),
  ("grey54", "#8A8A8A"),
  ("grey55", "#8C8C8C"),
  ("grey56", "#8F8F8F"),
  ("grey57", "#919191"),
  ("grey58", "#949494"),
  ("grey59", "#969696"),
  ("grey5", "#0D0D0D"),
  ("grey60", "#999999"),
  ("grey61", "#9C9C9C"),
  ("grey62", "#9E9E9E"),
  ("grey63", "#A1A1A1"),
  ("grey64", "#A3A3A3"),
  ("grey65", "#A6A6A6"),
  ("grey66", "#A8A8A8"),
  ("grey67", "#ABABAB"),
  ("grey68", "#ADADAD"),
  ("grey69", "#B0B0B0"),
  ("grey6", "#0F0F0F"),
  ("grey70", "#B3B3B3"),
  ("grey71", "#B5B5B5"),
  ("grey72", "#B8B8B8"),
  ("grey73", "#BABABA"),
  ("grey74", "#BDBDBD"),
  ("grey75", "#BFBFBF"),
  ("grey76", "#C2C2C2"),
  ("grey77", "#C4C4C4"),
  ("grey78", "#C7C7C7"),
  ("grey79", "#C9C9C9"),
  ("grey7", "#121212"),
  ("grey80", "#CCCCCC"),
  ("grey81", "#CFCFCF"),
  ("grey82", "#D1D1D1"),
  ("grey83", "#D4D4D4"),
  ("grey84", "#D6D6D6"),
  ("grey85", "#D9D9D9"),
  ("grey86", "#DBDBDB"),
  ("grey87", "#DEDEDE"),
  ("grey88", "#E0E0E0"),
  ("grey89", "#E3E3E3"),
  ("grey8", "#141414"),
  ("grey90", "#E5E5E5"),
  ("grey91", "#E8E8E8"),
  ("grey92", "#EBEBEB"),
  ("grey93", "#EDEDED"),
  ("grey94", "#F0F0F0"),
  ("grey95", "#F2F2F2"),
  ("grey96", "#F5F5F5"),
  ("grey97", "#F7F7F7"),
  ("grey98", "#FAFAFA"),
  ("grey99", "#FCFCFC"),
  ("grey9", "#171717"),
  ("honeydew1", "#F0FFF0"),
  ("honeydew2", "#E0EEE0"),
  ("honeydew3", "#C1CDC1"),
  ("honeydew4", "#838B83"),
  ("hotpink1", "#FF6EB4"),
  ("hotpink2", "#EE6AA7"),
  ("hotpink3", "#CD6090"),
  ("hotpink4", "#8B3A62"),
  ("indianred1", "#FF6A6A"),
  ("indianred2", "#EE6363"),
  ("indianred3", "#CD5555"),
  ("indianred4", "#8B3A3A"),
  ("ivory1", "#FFFFF0"),
  ("ivory2", "#EEEEE0"),
  ("ivory3", "#CDCDC1"),
  ("ivory4", "#8B8B83"),
  ("khaki1", "#FFF68F"),
  ("khaki2", "#EEE685"),
  ("khaki3", "#CDC673"),
  ("khaki4", "#8B864E"),
  ("lavenderblush1", "#FFF0F5"),
  ("lavenderblush2", "#EEE0E5"),
  ("lavenderblush3", "#CDC1C5"),
  ("lavenderblush4", "#8B8386"),
  ("lemonchiffon1", "#FFFACD"),
  ("lemonchiffon2", "#EEE9BF"),
  ("lemonchiffon3", "#CDC9A5"),
  ("lemonchiffon4", "#8B8970"),
  ("lightblue1", "#BFEFFF"),
  ("lightblue2", "#B2DFEE"),
  ("lightblue3", "#9AC0CD"),
  ("lightblue4", "#68838B"),
  ("lightcyan1", "#E0FFFF"),
  ("lightcyan2", "#D1EEEE"),
  ("lightcyan3", "#B4CDCD"),
  ("lightcyan4", "#7A8B8B"),
  ("lightgoldenrod1", "#FFEC8B"),
  ("lightgoldenrod2", "#EEDC82"),
  ("lightgoldenrod3", "#CDBE70"),
  ("lightgoldenrod4", "#8B814C"),
  ("lightpink1", "#FFAEB9"),
  ("lightpink2", "#EEA2AD"),
  ("lightpink3", "#CD8C95"),
  ("lightpink4", "#8B5F65"),
  ("lightred", "#f03232"),
  ("lightsalmon1", "#FFA07A"),
  ("lightsalmon2", "#EE9572"),
  ("lightsalmon3", "#CD8162"),
  ("lightsalmon4", "#8B5742"),
  ("lightskyblue1", "#B0E2FF"),
  ("lightskyblue2", "#A4D3EE"),
  ("lightskyblue3", "#8DB6CD"),
  ("lightskyblue4", "#607B8B"),
  ("lightskyblue", "#87CEFA"),
  ("lightslateblue", "#8470FF"),
  ("lightsteelblue1", "#CAE1FF"),
  ("lightsteelblue2", "#BCD2EE"),
  ("lightsteelblue3", "#A2B5CD"),
  ("lightsteelblue4", "#6E7B8B"),
  ("lightyellow1", "#FFFFE0"),
  ("lightyellow2", "#EEEED1"),
  ("lightyellow3", "#CDCDB4"),
  ("lightyellow4", "#8B8B7A"),
  ("magenta1", "#FF00FF"),
  ("magenta2", "#EE00EE"),
  ("magenta3", "#CD00CD"),
  ("magenta4", "#8B008B"),
  ("maroon1", "#FF34B3"),
  ("maroon2", "#EE30A7"),
  ("maroon3", "#CD2990"),
  ("maroon4", "#8B1C62"),
  ("mediumorchid1", "#E066FF"),
  ("mediumorchid2", "#D15FEE"),
  ("mediumorchid3", "#B452CD"),
  ("mediumorchid4", "#7A378B"),
  ("mediumpurple1", "#AB82FF"),
  ("mediumpurple2", "#9F79EE"),
  ("mediumpurple3", "#8968CD"),
  ("mediumpurple4", "#5D478B"),
  ("mistyrose1", "#FFE4E1"),
  ("mistyrose2", "#EED5D2"),
  ("mistyrose3", "#CDB7B5"),
  ("mistyrose4", "#8B7D7B"),
  ("navajowhite1", "#FFDEAD"),
  ("navajowhite2", "#EECFA1"),
  ("navajowhite3", "#CDB38B"),
  ("navajowhite4", "#8B795E"),
  ("navyblue", "#000080"),
  ("olivedrab1", "#C0FF3E"),
  ("olivedrab2", "#B3EE3A"),
  ("olivedrab3", "#9ACD32"),
  ("olivedrab4", "#698B22"),
  ("orange1", "#FFA500"),
  ("orange2", "#EE9A00"),
  ("orange3", "#CD8500"),
  ("orange4", "#8B5A00"),
  ("orangered1", "#FF4500"),
  ("orangered2", "#EE4000"),
  ("orangered3", "#CD3700"),
  ("orangered4", "#8B2500"),
  ("orchid1", "#FF83FA"),
  ("orchid2", "#EE7AE9"),
  ("orchid3", "#CD69C9"),
  ("orchid4", "#8B4789"),
  ("palegreen1", "#9AFF9A"),
  ("palegreen2", "#90EE90"),
  ("palegreen3", "#7CCD7C"),
  ("palegreen4", "#548B54"),
  ("paleturquoise1", "#BBFFFF"),
  ("paleturquoise2", "#AEEEEE"),
  ("paleturquoise3", "#96CDCD"),
  ("paleturquoise4", "#668B8B"),
  ("palevioletred1", "#FF82AB"),
  ("palevioletred2", "#EE799F"),
  ("palevioletred3", "#CD6889"),
  ("palevioletred4", "#8B475D"),
  ("peachpuff1", "#FFDAB9"),
  ("peachpuff2", "#EECBAD"),
  ("peachpuff3", "#CDAF95"),
  ("peachpuff4", "#8B7765"),
  ("pink1", "#FFB5C5"),
  ("pink2", "#EEA9B8"),
  ("pink3", "#CD919E"),
  ("pink4", "#8B636C"),
  ("plum1", "#FFBBFF"),
  ("plum2", "#EEAEEE"),
  ("plum3", "#CD96CD"),
  ("plum4", "#8B668B"),
  ("purple1", "#9B30FF"),
  ("purple2", "#912CEE"),
  ("purple3", "#7D26CD"),
  ("purple4", "#551A8B"),
  ("red1", "#FF0000"),
  ("red2", "#EE0000"),
  ("red3", "#CD0000"),
  ("red4", "#8B0000"),
  ("rosybrown1", "#FFC1C1"),
  ("rosybrown2", "#EEB4B4"),
  ("rosybrown3", "#CD9B9B"),
  ("rosybrown4", "#8B6969"),
  ("royalblue1", "#4876FF"),
  ("royalblue2", "#436EEE"),
  ("royalblue3", "#3A5FCD"),
  ("royalblue4", "#27408B"),
  ("salmon1", "#FF8C69"),
  ("salmon2", "#EE8262"),
  ("salmon3", "#CD7054"),
  ("salmon4", "#8B4C39"),
  ("seagreen1", "#54FF9F"),
  ("seagreen2", "#4EEE94"),
  ("seagreen3", "#43CD80"),
  ("seagreen4", "#2E8B57"),
  ("seashell1", "#FFF5EE"),
  ("seashell2", "#EEE5DE"),
  ("seashell3", "#CDC5BF"),
  ("seashell4", "#8B8682"),
  ("sienna1", "#FF8247"),
  ("sienna2", "#EE7942"),
  ("sienna3", "#CD6839"),
  ("sienna4", "#8B4726"),
  ("skyblue1", "#87CEFF"),
  ("skyblue2", "#7EC0EE"),
  ("skyblue3", "#6CA6CD"),
  ("skyblue4", "#4A708B"),
  ("slateblue1", "#836FFF"),
  ("slateblue2", "#7A67EE"),
  ("slateblue3", "#6959CD"),
  ("slateblue4", "#473C8B"),
  ("slategray1", "#C6E2FF"),
  ("slategray2", "#B9D3EE"),
  ("slategray3", "#9FB6CD"),
  ("slategray4", "#6C7B8B"),
  ("snow1", "#FFFAFA"),
  ("snow2", "#EEE9E9"),
  ("snow3", "#CDC9C9"),
  ("snow4", "#8B8989"),
  ("springgreen1", "#00FF7F"),
  ("springgreen2", "#00EE76"),
  ("springgreen3", "#00CD66"),
  ("springgreen4", "#008B45"),
  ("steelblue1", "#63B8FF"),
  ("steelblue2", "#5CACEE"),
  ("steelblue3", "#4F94CD"),
  ("steelblue4", "#36648B"),
  ("tan1", "#FFA54F"),
  ("tan2", "#EE9A49"),
  ("tan3", "#CD853F"),
  ("tan4", "#8B5A2B"),
  ("thistle1", "#FFE1FF"),
  ("thistle2", "#EED2EE"),
  ("thistle3", "#CDB5CD"),
  ("thistle4", "#8B7B8B"),
  ("tomato1", "#FF6347"),
  ("tomato2", "#EE5C42"),
  ("tomato3", "#CD4F39"),
  ("tomato4", "#8B3626"),
  ("turquoise1", "#00F5FF"),
  ("turquoise2", "#00E5EE"),
  ("turquoise3", "#00C5CD"),
  ("turquoise4", "#00868B"),
  ("violetred1", "#FF3E96"),
  ("violetred2", "#EE3A8C"),
  ("violetred3", "#CD3278"),
  ("violetred4", "#8B2252"),
  ("violetred", "#D02090"),
  ("wheat1", "#FFE7BA"),
  ("wheat2", "#EED8AE"),
  ("wheat3", "#CDBA96"),
  ("wheat4", "#8B7E66"),
  ("yellow1", "#FFFF00"),
  ("yellow2", "#EEEE00"),
  ("yellow3", "#CDCD00"),
  ("yellow4", "#8B8B00"),
]

