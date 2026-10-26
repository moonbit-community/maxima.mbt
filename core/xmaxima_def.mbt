// Port of src/xmaxima_def.lisp: routines for Maxima's interface to xmaxima
// (the methods of the xmaxima-plot class).

///|
/// Given a list of valid colors (see rgb-color function) and an object c
/// that can be a real number or a string, produces an rgb color
/// specification for c; when c is real, its nearest integer is assigned to
/// one of the numbers in the list, using modulo length of the list.
fn xmaxima_color(colors : Value, c : Value) -> Value raise {
  let colors = if listp(colors) { colors } else { list1(colors) }
  let mut c = c
  if realp(c) {
    if !integerp(c) {
      c = round1(c)
    }
    c = nth(
      to_int(num_mod(num_sub(c, Fix(1L)), int(length(colors)))),
      colors,
    )
  }
  rgb_color(c)
}

///|
/// style is a list starting with a symbol from the list: points, lines,
/// linespoints or dots,
/// The meaning of the numbers that follow the symbol are:
///
///   lines, linewidth, color
///   points, radius, color
///   linespoints, linewidth, radius, color
///   dots, color
///
/// linewidth and radius are measured in the same units and can be
/// floating-point numbers.
///
/// type must be an integer
/// color can be an integer, used as index to get one of the colors defined
/// by the color option, or a 6-digit hexadecimal number #rrggbb
fn xmaxima_curve_style(style : Value, colors : Value, i : Value) -> Value raise {
  let style = if listp(style) { style } else { list1(style) }
  let colors = if listp(colors) { colors } else { list1(colors) }
  let st = make_string_output_stream()
  let f = (ctl : String, args : Array[Value]) => format(st, ctl, args) |> ignore
  let kind = first(style)
  if eq(kind, q_d_dots) {
    f("{ nolines 1 } { plotpoints 1 } { pointsize 0.7 }", [])
    if second(style).truthy() {
      f(" { color ~a }", [xmaxima_color(colors, second(style))])
    } else {
      f(" { color ~a }", [xmaxima_color(colors, i)])
    }
  } else if eq(kind, q_d_lines) {
    f("{ nolines 0 } { plotpoints 0 }", [])
    if realp(second(style)) {
      f(" { linewidth ~f }", [second(style)])
    }
    if third(style).truthy() {
      f(" { color ~a }", [xmaxima_color(colors, third(style))])
    } else {
      f(" { color ~a }", [xmaxima_color(colors, i)])
    }
  } else if eq(kind, q_d_points) {
    f("{ nolines 1 } { plotpoints 1 }", [])
    if realp(second(style)) {
      f(" { pointsize ~f }", [second(style)])
    } else {
      f(" { pointsize 3 }", [])
    }
    if third(style).truthy() {
      f(" { color ~a }", [xmaxima_color(colors, third(style))])
    } else {
      f(" { color ~a }", [xmaxima_color(colors, i)])
    }
  } else if eq(kind, q_d_linespoints) {
    f("{ nolines 0 } { plotpoints 1 }", [])
    if realp(second(style)) {
      f(" { linewidth ~f }", [second(style)])
    }
    if realp(third(style)) {
      f(" { pointsize ~f }", [third(style)])
    } else {
      f(" { pointsize 3 }", [])
    }
    if fourth(style).truthy() {
      f(" { color ~a }", [xmaxima_color(colors, fourth(style))])
    } else {
      f(" { color ~a }", [xmaxima_color(colors, i)])
    }
  } else {
    f("{ nolines 0 } { plotpoints 0 } { color ~a }", [xmaxima_color(colors, i)])
  }
  Str(get_output_stream_string(st))
}

///|
/// Given a valid palette, it returns its definition for Xmaxima.
fn xmaxima_palette(palette : Value) -> Value raise {
  let mut type_ : Value = Nil
  let mut colors : Value = Nil
  let mut fun : Value = Nil
  let fun_format = " {hue ~,,,,,,'eg} {saturation ~,,,,,,'eg} {value ~,,,,,,'eg} {colorrange ~,,,,,,'eg}"
  if atom(palette) {
    if getf(symval(q_ear_plot_palettes), palette).truthy() {
      type_ = palette
      colors = cdr(getf(symval(q_ear_plot_palettes), palette))
    } else {
      type_ = q_d_monochromatic
      colors = rgb_color(palette)
      if !colors.truthy() {
        colors = Str("#ffffff")
      }
    }
  } else {
    type_ = car(palette)
    if eq(type_, q_d_gradient) {
      colors = cdr(palette)
    } else if eq(type_, q_d_hue) ||
      eq(type_, q_d_saturation) ||
      eq(type_, q_d_value) {
      fun = format(Nil, fun_format, [
        second(palette),
        third(palette),
        fourth(palette),
        fifth(palette),
      ])
    } else {
      colors = palette
    }
  }
  let st = make_string_output_stream()
  if eq(type_, q_d_monochromatic) {
    format(st, "~&{colorscheme ~a}", [colors]) |> ignore
  } else if eq(type_, q_d_hue) {
    format(st, "~&~a {colorscheme hue}", [fun]) |> ignore
  } else if eq(type_, q_d_saturation) {
    format(st, "~&~a {colorscheme saturation}", [fun]) |> ignore
  } else if eq(type_, q_d_value) {
    format(st, "~&~a {colorscheme value}", [fun]) |> ignore
  } else if eq(type_, q_d_gray) || eq(type_, q_d_grey) {
    format(st, "~&{colorscheme gray}", []) |> ignore
  } else {
    colors = mapcar(c => rgb_color(c), colors)
    format(st, "~&{colorscheme gradient} {gradlist {~{~s~^ ~}}}", [colors])
    |> ignore
  }
  Str(get_output_stream_string(st))
}

///|
/// Method PLOT-PREAMBLE of xmaxima-plot.
fn xmaxima_def__plot_preamble(plot : PlotObj, options : Value) -> Value raise {
  let mut outfile : Value = Nil
  let st = make_string_output_stream()
  let f = (ctl : String, args : Array[Value]) => format(st, ctl, args) |> ignore
  let opt = (k : Value) => getf(options, k)
  if symval(q_d_show_openplot).truthy() {
    f("~a ", [opt(q_d_type)])
    f("-background ~a -data {~%", [rgb_color(opt(q_d_background_color))])
    // record Maxima version and date-time
    f("# Created by Maxima ~a~%", [symval(q_ear_autoconf_version)])
    f("# ~a~%", [d_timedate()])
  } else {
    f("{~a {background ~a} ", [
      opt(q_d_type),
      rgb_color(opt(q_d_background_color)),
    ])
  }
  if lstring(opt(q_d_type)) == "plot3d" {
    let elev = opt(q_d_elevation)
    let azim = opt(q_d_azimuth)
    if elev.truthy() {
      f(" {el ~d}", [elev])
    }
    if azim.truthy() {
      f(" {az ~d}", [azim])
    }
    f("~%", [])
  }
  if opt(q_d_ps_file).truthy() {
    outfile = plot_file_path(opt(q_d_ps_file), preserve_file=t)
    f(" {psfile ~s}", [outfile])
  }
  if memq(q_d_legend, options).truthy() {
    if !opt(q_d_legend).truthy() {
      f(" {nolegend 1}", [])
    }
  }
  if memq(q_mbox, options).truthy() {
    if !opt(q_mbox).truthy() {
      f(" {nobox 1}", [])
    }
  }
  let axes = opt(q_d_axes)
  if axes.truthy() {
    if eq(axes, q_d_x) {
      f(" {axes {x} }", [])
    } else if eq(axes, q_d_y) {
      f(" {axes {y} }", [])
    } else {
      f(" {axes {xy} }", [])
    }
  } else {
    f(" {axes 0}", [])
  }
  if opt(q_d_x).truthy() {
    f(" {xrange ~{~,,,,,,'eg~^ ~}}", [opt(q_d_x)])
  }
  if opt(q_d_y).truthy() {
    f(" {yrange ~{~,,,,,,'eg~^ ~}}", [opt(q_d_y)])
  }
  if opt(q_d_z).truthy() {
    let zmin = first(opt(q_d_z))
    let zmax = second(opt(q_d_z))
    f(" {zcenter ~,,,,,,'eg }", [num_div(num_add(zmax, zmin), Flo(2.0))])
    f(" {zradius ~,,,,,,'eg }", [num_div(num_sub(zmax, zmin), Flo(2.0))])
  }
  if opt(q_d_xlabel).truthy() {
    f(" {xaxislabel ~s}", [opt(q_d_xlabel)])
  }
  if opt(q_d_ylabel).truthy() {
    f(" {yaxislabel ~s}", [opt(q_d_ylabel)])
  }
  if opt(q_d_z).truthy() {
    let z = opt(q_d_z)
    let mut sum : Value = Fix(0L)
    for v in z.iter() {
      sum = num_add(sum, v)
    }
    // (apply #'- z)
    let mut dif = car(z)
    if cdr(z) is Nil {
      dif = num_neg(dif)
    } else {
      for v in cdr(z).iter() {
        dif = num_sub(dif, v)
      }
    }
    f(" {zcenter ~,,,,,,'eg }", [num_div(sum, Fix(2L))])
    f(" {zradius ~,,,,,,'eg }~%", [num_div(dif, Fix(-2L))])
  }
  f("~%", [])
  plot.data = plot.data + get_output_stream_string(st)
  // returns a list with the name of the file to be created, or nil
  if outfile is Nil {
    Nil
  } else {
    list1(outfile)
  }
}

///|
/// The point lists of the curve LIS (x1 y1 x2 y2 ...) as Tcl lists, broken
/// at the MOVETO's: segments with less than two points are not output.
fn xmaxima_def__output_curve(st : Value, lis0 : Value) -> Unit raise {
  let mut lis = lis0
  while lis.truthy() {
    let xx = Collector::new()
    let yy = Collector::new()
    while lis.truthy() && !eq(car(lis), q_moveto) {
      xx.add(car(lis))
      yy.add(cadr(lis))
      lis = cddr(lis)
    }
    // only output if at least two points for line
    let xs = xx.result()
    if cdr(xs).truthy() {
      tcl_output_list(st, xs) |> ignore
      tcl_output_list(st, yy.result()) |> ignore
    }
    // remove the moveto
    lis = cddr(lis)
  }
}

///|
/// Method PLOT2D-COMMAND of xmaxima-plot.
fn xmaxima_def__plot2d_command(
  plot : PlotObj,
  fun : Value,
  options : Value,
  range : Value,
) -> Unit raise {
  let points_lists = mapcar(f => cdr(draw2d(f, range, options)), cdr(fun))
  if count_if(x => x.truthy(), points_lists) == 0 {
    merr("plot2d: nothing to plot.~%", []) |> ignore
  }
  plot__prune_legends(points_lists, options)
  let st = make_string_output_stream()
  let f = (ctl : String, args : Array[Value]) => format(st, ctl, args) |> ignore
  if !(
      getf(options, q_d_logy).truthy() ||
      (getf(options, q_d_y).truthy() && listp(getf(options, q_d_y)))
    ) {
    match plot__auto_yrange(points_lists, options) {
      Some((ymin, ymax)) =>
        f(" {yrange ~,,,,,,'eg ~,,,,,,'eg}~%", [ymin, ymax])
      None => ()
    }
  }
  let mut legend = getf(options, q_d_legend)
  let mut colors = getf(options, q_d_color)
  let mut styles = getf(options, q_d_style)
  let mut i = 0
  if !listp(legend) {
    legend = list1(legend)
  }
  if !listp(colors) {
    colors = list1(colors)
  }
  if !listp(styles) {
    styles = list1(styles)
  }
  let style_for = (i : Int) => {
    let style = if styles.truthy() {
      nth(i % length(styles), styles)
    } else {
      Nil
    }
    if d_listp(style).truthy() {
      cdr(style)
    } else {
      style
    }
  }
  let mut vs = cdr(fun)
  let mut pls = points_lists
  while vs is Cons(_) && pls is Cons(_) {
    let v = car(vs)
    let points_list = car(pls)
    vs = cdr(vs)
    pls = cdr(pls)
    if points_list.truthy() {
      // case "contour" with several plots in one list
      if d_listp(car(points_list)).truthy() {
        let mut j = 0
        for level in cdar(points_list).iter() {
          let style = style_for(i)
          i = i + 1
          j = j + 1
          f(" {label ~s} ", [ensure_string(level)])
          f(lstring(xmaxima_curve_style(style, colors, int(i))), [])
          f("~%{xversusy~%", [])
          xmaxima_def__output_curve(st, cdr(nth(j, points_list)))
          f("}", [])
        }
        break
      }
      // other cases with only one plot per list
      let style = style_for(i)
      i = i + 1
      // label the expression according to the legend, unless it is "false"
      // or there is only one expression
      let plot_name = plot__plot_name(v, fun, options, legend, i)
      if plot_name.truthy() {
        f(" {label ~s} ", [plot_name])
      } else {
        f(" {nolegend 1} ", [])
      }
      f(lstring(xmaxima_curve_style(style, colors, int(i))), [])
      f("~%{xversusy~%", [])
      xmaxima_def__output_curve(st, points_list)
      f("}", [])
    }
  }
  f("} ", [])
  plot.data = plot.data + get_output_stream_string(st)
}

///|
/// Method PLOT3D-COMMAND of xmaxima-plot.
fn xmaxima_def__plot3d_command(
  plot : PlotObj,
  functions : Value,
  options : Value,
  titles : Value,
) -> Unit raise {
  ignore(titles)
  let st = make_string_output_stream()
  // generate the mesh points for each surface in the functions stack
  for f in functions.iter() {
    let (fun, trans) = plot__surface_fun(f, None)
    let xrange = second(f)
    let yrange = third(f)
    let (points, _) = draw3d(
      fun,
      third(xrange),
      fourth(xrange),
      third(yrange),
      fourth(yrange),
      first(getf(options, q_d_grid)),
      second(getf(options, q_d_grid)),
    )
    let palette = getf(options, q_d_palette)
    let meshcolor = if memq(q_d_mesh_lines_color, options).truthy() {
      getf(options, q_d_mesh_lines_color)
    } else {
      q_d_black
    }
    if trans.truthy() {
      funcall(trans, [points]) |> ignore
    }
    if getf(options, q_d_transform_xy).truthy() {
      mfuncall(getf(options, q_d_transform_xy), list1(points)) |> ignore
    }
    if meshcolor.truthy() {
      format(st, " {mesh_lines ~a}", [rgb_color(meshcolor)]) |> ignore
    } else {
      format(st, " {mesh_lines 0}", []) |> ignore
    }
    if palette.truthy() {
      format(st, " ~a", [xmaxima_palette(palette)]) |> ignore
    } else {
      format(st, " {colorscheme 0}", []) |> ignore
    }
    output_points_tcl(st, points, first(getf(options, q_d_grid))) |> ignore
  }
  format(st, "}~%", []) |> ignore
  plot.data = plot.data + get_output_stream_string(st)
}

///|
/// Method PLOT-SHIPOUT of xmaxima-plot.
fn xmaxima_def__plot_shipout(
  plot : PlotObj,
  options : Value,
  output_file : Value,
) -> Value raise {
  ignore(options)
  let file = plot_file_path(format(Nil, "~a.xmaxima", [random_name(Fix(16L))]))
  if symval(q_d_show_openplot).truthy() {
    write_file(lstring(file), plot.data)
    d_system(
      list2(
        symval(q_d_xmaxima_plot_command),
        format(Nil, lstring(symval(q_d_gnuplot_file_args)), [file]),
      ),
    )
    |> ignore
  } else {
    princ(Str(plot.data)) |> ignore
  }
  cons(list1(q_mlist), cons(file, output_file))
}

///|
fn d_tcl_output(lis : Value, i : Value, skip? : Value = Fix(2L)) -> Value raise {
  if !fixnump(i) {
    merr("tcl_ouput: second argument must be an integer; found ~M", [i])
    |> ignore
  }
  if !d_listp(lis).truthy() {
    merr("tcl_output: first argument must be a list; found ~M", [lis]) |> ignore
  }
  let out = standard_output
  format(out, "~% {", []) |> ignore
  if d_listp(second(lis)).truthy() {
    for v in lis.iter() {
      format(out, "~,,,,,,'eg ", [nth(to_int(i), v)]) |> ignore
    }
  } else {
    let mut v = nthcdr(to_int(i), lis)
    while v.truthy() {
      format(out, "~,,,,,,'eg ", [car(v)]) |> ignore
      v = nthcdr(to_int(skip), v)
    }
  }
  format(out, "~% }", [])
}

///|
fn tcl_output_list(st : Value, lis : Value) -> Value raise {
  if lis is Nil {
    Nil
  } else if atom(car(lis)) {
    princ(Str(" {  "), stream=st) |> ignore
    let mut n = 0
    for v in lis.iter() {
      n = n + 1
      if n % 5 == 0 {
        terpri(stream=st)
      }
      format(st, "~,,,,,,'eg ", [v]) |> ignore
    }
    format(st, " }~%", [])
  } else {
    tcl_output_list(st, car(lis)) |> ignore
    tcl_output_list(st, cdr(lis))
  }
}

///|
/// Outputs the 3 coordinates of a grid of points.  If the grid option is
/// [grid,m,n], the points form a matrix with n+1 rows (x dirention) and m+1
/// columns (ydirection), stored in the array 'points' inside de structure
/// st, one row after another.  The points coordinates are written into 3
/// Tcl lists, each one with n+1 sublists with the coordinates of the m+1
/// points on each row. The first list has the x coordinates, the second one
/// the y coordinates and the third one has the z coordinates.
fn output_points_tcl(st : Value, ar : Value, m : Value) -> Value raise {
  format(st, "~%{matrix_mesh", []) |> ignore
  // x y z are done separately:
  let len = length(ar)
  let mv = to_int(m)
  for off in 0..=2 {
    let mut i = off
    format(st, "~%{", []) |> ignore
    while i < len {
      format(st, "~%{", []) |> ignore
      for _ in 0..=mv {
        if floatp(aref1(ar, i)) {
          format(st, "~,,,,,,'eg ", [aref1(ar, i)]) |> ignore
        } else {
          format(st, "~a ", [symval(q_ear_missing_data_indicator)]) |> ignore
        }
        i = i + 3
      }
      format(st, "}", []) |> ignore
    }
    format(st, "~%}", []) |> ignore
  }
  format(st, "~%}", [])
}
