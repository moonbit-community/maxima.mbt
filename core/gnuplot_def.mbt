// Port of src/gnuplot_def.lisp: routines for Maxima's interface to gnuplot
// (the methods of the gnuplot-plot class and the gnuplot_pipes process).
//
// The Gnuplot process of the gnuplot_pipes format is started with the
// runtime's output pipes (popen): *GNUPLOT-STREAM* holds the pipe handle.

///|
/// Given a list of valid colors (see plotcolors.lisp) and an object c that
/// can be a real number or a string, produces a gnuplot color specification
/// for c; when c is real, its nearest integer is assigned to one of the
/// numbers in the list, using modulo length of the list.
fn gnuplot_color(colors : Value, c : Value) -> Value raise {
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
  format(Nil, "rgb ~s", [rgb_color(c)])
}

///|
fn gnuplot_pointtype(type_ : Value) -> Value raise {
  let n = match type_ {
    Sym(s) =>
      match s.name {
        "$bullet" => 7
        "$circle" => 6
        "$plus" => 1
        "$times" => 2
        "$asterisk" => 3
        "mbox" => 5
        "$square" => 4
        "$triangle" => 9
        "$delta" => 8
        "$wedge" => 11
        "$nabla" => 10
        "$diamond" => 13
        "$lozenge" => 12
        _ => 7
      }
    _ => 7
  }
  int(n)
}

///|
fn gnuplot_pointtypes(types : Value, n : Value) -> Value raise {
  let n = if integerp(n) { n } else { round1(n) }
  let types = if listp(types) { types } else { list1(types) }
  gnuplot_pointtype(
    nth(to_int(num_mod(num_sub(n, Fix(1L)), int(length(types)))), types),
  )
}

///|
/// style is a list starting with one of the symbols: points, lines,
/// linespoints or dots,
/// The meaning of the numbers that follow the symbol are:
///
///   lines, linewidth, color
///   points, radius, color, pointtype
///   linespoints, linewidth, radius, color, pointtype, pointinterval
///   dots, color
///
/// linewidth and radius are measured in the same units and can be
/// floating-point numbers.
///
/// type must be an integer
/// color can be an integer, used as index to get one of the colors defined
/// by the color option, or a 6-digit hexadecimal number #rrggbb
fn gnuplot_curve_style(
  style : Value,
  colors : Value,
  types : Value,
  i : Value,
) -> Value raise {
  let style = if listp(style) { style } else { list1(style) }
  let colors = if listp(colors) { colors } else { list1(colors) }
  let st = make_string_output_stream()
  let f = (ctl : String, args : Array[Value]) => format(st, ctl, args) |> ignore
  let kind = first(style)
  if eq(kind, q_d_dots) {
    f("with dots", [])
    if second(style).truthy() {
      f(" lt ~d", [gnuplot_color(colors, second(style))])
    } else {
      f(" lt ~d", [gnuplot_color(colors, i)])
    }
  } else if eq(kind, q_d_impulses) {
    f("with impulses", [])
    if integerp(second(style)) {
      f(" lt ~d", [gnuplot_color(colors, second(style))])
    } else {
      f(" lt ~d", [gnuplot_color(colors, i)])
    }
  } else if eq(kind, q_d_lines) {
    f("with lines", [])
    if realp(second(style)) {
      f(" lw ~f", [second(style)])
    }
    if third(style).truthy() {
      f(" lt ~d", [gnuplot_color(colors, third(style))])
    } else {
      f(" lt ~d", [gnuplot_color(colors, i)])
    }
  } else if eq(kind, q_d_points) {
    f("with points", [])
    if realp(second(style)) {
      f(" ps ~f", [num_div(second(style), Fix(2L))])
    } else {
      f(" ps 1.5", [])
    }
    if third(style).truthy() {
      f(" lt ~d", [gnuplot_color(colors, third(style))])
    } else {
      f(" lt ~d", [gnuplot_color(colors, i)])
    }
    if integerp(fourth(style)) {
      f(" pt ~d", [gnuplot_pointtypes(types, fourth(style))])
    } else {
      f(" pt ~d", [gnuplot_pointtypes(types, i)])
    }
  } else if eq(kind, q_d_linespoints) {
    f("with linespoints", [])
    if realp(second(style)) {
      f(" lw ~f", [second(style)])
    }
    if realp(third(style)) {
      f(" ps ~f", [num_div(third(style), Fix(2L))])
    } else {
      f(" ps 1.5", [])
    }
    if fourth(style).truthy() {
      f(" lt ~d", [gnuplot_color(colors, fourth(style))])
    } else {
      f(" lt ~d", [gnuplot_color(colors, i)])
    }
    if integerp(fifth(style)) {
      f(" pt ~d", [gnuplot_pointtypes(types, fifth(style))])
    } else {
      f(" pt ~d", [gnuplot_pointtypes(types, i)])
    }
    if integerp(nth(5, style)) {
      f(" pointinterval ~d", [nth(5, style)])
    }
  } else {
    f("with lines lt ~d", [gnuplot_color(colors, i)])
  }
  Str(get_output_stream_string(st))
}

///|
/// Given a valid palette, it returns its definition for Gnuplot.
fn gnuplot_palette(palette : Value) -> Value raise {
  let mut type_ : Value = Nil
  let mut colors : Value = Nil
  let mut hue : Value = Nil
  let mut sat : Value = Nil
  let mut val : Value = Nil
  let mut range : Value = Nil
  if atom(palette) {
    if getf(symval(q_ear_plot_palettes), palette).truthy() {
      colors = cdr(getf(symval(q_ear_plot_palettes), palette))
    } else {
      colors = list2(palette, palette)
    }
  } else {
    type_ = car(palette)
    if eq(type_, q_d_gradient) {
      colors = cdr(palette)
    } else if eq(type_, q_d_hue) ||
      eq(type_, q_d_saturation) ||
      eq(type_, q_d_value) {
      let vs = cdr(palette)
      hue = first(vs)
      sat = second(vs)
      val = third(vs)
      range = fourth(vs)
    } else {
      colors = palette
    }
  }
  let st = make_string_output_stream()
  let wraps = (x : Value) => num_lt(num_add(x, range), Fix(0L)) ||
    num_gt(num_add(x, range), Fix(1L))
  if eq(type_, q_d_hue) {
    let fun = if wraps(hue) {
      format(Nil, "~,3f+~,3f*gray-floor(~,3f+~,3f*gray)", [hue, range, hue, range])
    } else {
      format(Nil, "~,3f+~,3f*gray", [hue, range])
    }
    format(st, "model HSV functions ~a, ~,3f, ~,3f", [fun, sat, val]) |> ignore
  } else if eq(type_, q_d_saturation) {
    let fun = if wraps(sat) {
      format(Nil, "~,3f+~,3f*gray-floor(~,3f+~,3f*gray)", [sat, range, sat, range])
    } else {
      format(Nil, "~,3f+~,3f*gray", [sat, range])
    }
    format(st, "model HSV functions ~,3f, ~a, ~,3f", [hue, fun, val]) |> ignore
  } else if eq(type_, q_d_value) {
    let fun = if wraps(val) {
      format(Nil, "~,3f+~,3f*gray", [val, range])
    } else {
      format(Nil, "~,3f+~,3f*gray-floor(~,3f+~,3f*gray)", [val, range, val, range])
    }
    format(st, "model HSV functions ~,3f, ~,3f, ~a", [hue, sat, fun]) |> ignore
  } else {
    let n = length(colors)
    let mut map : Value = Nil
    for i in 0..<n {
      let c = rgb_color(nth(i, colors))
      map = cons(
        if c.truthy() { c } else { Str("#ffffff") },
        cons(num_div(int(i), int(n - 1)), map),
      )
    }
    // prints map with the format:  nj, "cj", ...,n1, "c1"
    let fun = format(Nil, "~{~f ~s~^, ~}", [reverse(map)])
    // outputs the string: defined (nj, "cj", ...,n1, "c1")
    format(st, "defined (~a)", [fun]) |> ignore
  }
  Str(get_output_stream_string(st))
}

///|
fn gnuplot_plot3d_command(
  file : Value,
  palette : Value,
  gstyles : Value,
  meshcolor : Value,
  titles : Value,
  n : Value,
) -> Value raise {
  let mut style : Value = Str("with pm3d")
  let out = make_string_output_stream()
  format(out, "splot ", []) |> ignore
  let nv = to_int(n)
  for i in 1..=nv {
    if palette is Nil {
      if gstyles.truthy() {
        if !listp(gstyles) {
          // (nth n gstyles) of a single style string
          raise LispError::SimpleError(
            "The value\n  " +
            prin1_to_string(gstyles) +
            "\nis not of type\n  LIST",
          )
        }
        style = ensure_string(nth(i % length(gstyles), gstyles))
      } else {
        style = format(Nil, "with lines lc rgb ~s", [rgb_color(meshcolor)])
      }
    }
    if i > 1 {
      format(out, ", ", []) |> ignore
    }
    let title = if titles.truthy() {
      nth(i % length(titles), titles)
    } else {
      Str("")
    }
    format(out, "~s title ~s ~a", [file, title, style]) |> ignore
  }
  format(out, "~%", []) |> ignore
  Str(get_output_stream_string(out))
}

///|
fn gnuplot_terminal_and_file(plot_options : Value) -> Value raise {
  let gstrings : Value = if getf(plot_options, q_d_gnuplot_strings).truthy() {
    Str("enhanced")
  } else {
    Str("noenhanced")
  }
  let mut terminal_command : Value = Nil
  let mut out_file : Value = Nil
  let mut preserve_file : Value = t
  let opt = (k : Value) => getf(plot_options, k)
  let term = opt(q_d_gnuplot_term)
  if opt(q_d_svg_file).truthy() {
    terminal_command = if opt(q_d_gnuplot_svg_term_command).truthy() {
      opt(q_d_gnuplot_svg_term_command)
    } else {
      format(Nil, "set term svg font \",14\" ~a", [gstrings])
    }
    out_file = opt(q_d_svg_file)
  } else if opt(q_d_png_file).truthy() {
    terminal_command = if opt(q_d_gnuplot_png_term_command).truthy() {
      opt(q_d_gnuplot_png_term_command)
    } else {
      format(Nil, "set term pngcairo font \",12\" ~a", [gstrings])
    }
    out_file = opt(q_d_png_file)
  } else if opt(q_d_pdf_file).truthy() {
    terminal_command = if opt(q_d_gnuplot_pdf_term_command).truthy() {
      opt(q_d_gnuplot_pdf_term_command)
    } else {
      format(
        Nil,
        "set term pdfcairo color solid lw 3 size 17.2 cm, 12.9 cm font \",18\" ~a",
        [gstrings],
      )
    }
    out_file = opt(q_d_pdf_file)
  } else if opt(q_d_ps_file).truthy() {
    terminal_command = if opt(q_d_gnuplot_ps_term_command).truthy() {
      opt(q_d_gnuplot_ps_term_command)
    } else {
      format(
        Nil,
        "set term postscript eps color solid lw 2 size 16.4 cm, 12.3 cm font \",24\" ~a",
        [gstrings],
      )
    }
    out_file = opt(q_d_ps_file)
  } else if eq(term, q_d_ps) {
    terminal_command = if opt(q_d_gnuplot_ps_term_command).truthy() {
      opt(q_d_gnuplot_ps_term_command)
    } else {
      format(
        Nil,
        "set term postscript eps color solid lw 2 size 16.4 cm, 12.3 cm font \",24\" ~a",
        [gstrings],
      )
    }
    out_file = if opt(q_d_gnuplot_out_file).truthy() {
      opt(q_d_gnuplot_out_file)
    } else {
      format(Nil, "~a.ps", [random_name(Fix(16L))])
    }
  } else if eq(term, q_d_dumb) {
    terminal_command = if opt(q_d_gnuplot_dumb_term_command).truthy() {
      opt(q_d_gnuplot_dumb_term_command)
    } else {
      Str("set term dumb 79 22")
    }
    out_file = if opt(q_d_gnuplot_out_file).truthy() {
      opt(q_d_gnuplot_out_file)
    } else {
      format(Nil, "~a.txt", [random_name(Fix(16L))])
    }
  } else if eq(term, q_d_default) {
    terminal_command = if opt(q_d_gnuplot_default_term_command).truthy() {
      opt(q_d_gnuplot_default_term_command)
    } else if opt(q_d_window).truthy() {
      format(Nil, "set term GNUTERM ~d ~a~%", [opt(q_d_window), gstrings])
    } else {
      format(Nil, "set term GNUTERM ~a~%", [gstrings])
    }
  } else if term.truthy() {
    terminal_command = format(Nil, "set term ~(~a~)", [ensure_string(term)])
    if opt(q_d_gnuplot_out_file).truthy() {
      out_file = opt(q_d_gnuplot_out_file)
    } else {
      preserve_file = Nil
      out_file = format(Nil, "maxplot.~(~a~)", [get_gnuplot_term(term)])
    }
  }
  if out_file.truthy() {
    out_file = plot_file_path(
      out_file,
      preserve_file~,
      plot_options~,
    )
    // plots that create a file work better in gnuplot than gnuplot_pipes
    if eq(opt(q_d_plot_format), q_d_gnuplot_pipes) {
      plot__putf(plot_options, q_d_plot_format, q_d_gnuplot) |> ignore
    }
  }
  list2(terminal_command, out_file)
}

///|
/// The tics option FORMAT clause of PLOT-PREAMBLE for OPT (named NAME).
fn gnuplot_def__tics(
  dest : Value,
  plot_options : Value,
  opt : Value,
  name : String,
) -> Unit raise {
  if memq(opt, plot_options).truthy() {
    let tics = getf(plot_options, opt)
    if tics is Cons(_) {
      format(dest, "set " + name + " ~{~f~^, ~}~%", [tics]) |> ignore
    } else if tics.truthy() {
      format(dest, "set " + name + " ~f~%", [tics]) |> ignore
    } else {
      format(dest, "unset " + name + "~%", []) |> ignore
    }
  }
}

///|
/// Method PLOT-PREAMBLE of gnuplot-plot.
fn gnuplot_def__plot_preamble(plot : PlotObj, plot_options : Value) -> Value raise {
  let opt = (k : Value) => getf(plot_options, k)
  let palette = opt(q_d_palette)
  let meshcolor = if memq(q_d_mesh_lines_color, plot_options).truthy() {
    opt(q_d_mesh_lines_color)
  } else {
    q_d_black
  }
  let lighting = opt(q_d_lighting)
  // sets-up terminal command and output file name
  let terminal_file = gnuplot_terminal_and_file(plot_options)
  let dest = make_string_output_stream()
  let f = (ctl : String, args : Array[Value]) => format(dest, ctl, args)
  |> ignore
  let type_is = (s : String) => lstring(opt(q_d_type)) == s
  // record Maxima version and date-time
  f("# Created by Maxima ~a~%", [symval(q_ear_autoconf_version)])
  f("# ~a~%", [d_timedate()])
  // reset initial state
  f("reset~%unset output~%unset multiplot~%set clip two~%", [])
  // user's preamble
  if opt(q_d_gnuplot_preamble).truthy() &&
    length(opt(q_d_gnuplot_preamble)) > 0 {
    f("~a~%", [opt(q_d_gnuplot_preamble)])
  }
  // Don't round numbers with absolute value less than 1e-8 to zero
  f("set zero 0.0~%", [])
  // prints terminal and output commands
  if first(terminal_file).truthy() {
    f("~a~%", [first(terminal_file)])
  }
  if second(terminal_file).truthy() {
    f("set output ~s~%", [second(terminal_file)])
  }
  // background color
  f(
    "set obj 1 rectangle behind from screen 0.0,0.0 to screen 1.0,1.0~%",
    [],
  )
  // options specific to plot3d
  f("set obj 1 fc rgb ~s fs solid 1.0 noborder~%", [
    rgb_color(opt(q_d_background_color)),
  ])
  if type_is("plot3d") {
    f("set xyplane relative 0~%", [])
    if palette.truthy() {
      if meshcolor.truthy() {
        f(
          "if (GPVAL_VERSION < 5.0) set style line 100 lt rgb ~s lw 1; set pm3d hidden3d 100~%",
          [rgb_color(meshcolor)],
        )
        f(
          "if ((GPVAL_VERSION >= 5.0) && (GPVAL_VERSION < 6.0)) set pm3d hidden3d 100 border lw 0.5 lt rgb ~s~%",
          [rgb_color(meshcolor)],
        )
        f(
          "if (GPVAL_VERSION >= 6.0) set pm3d hidden3d border lw 0.5 lt rgb ~s~%",
          [rgb_color(meshcolor)],
        )
        if !opt(q_d_gnuplot_4_0).truthy() {
          f("set pm3d depthorder", [])
          if lighting.truthy() {
            f(" lighting~%", [])
          } else {
            f("~%", [])
          }
        }
      } else {
        f("set pm3d depthorder", [])
        if lighting.truthy() {
          f(" lighting~%", [])
        } else {
          f("~%", [])
        }
      }
      f("unset hidden3d~%", [])
      f("set palette ~a~%", [gnuplot_palette(palette)])
    } else {
      f("unset pm3d~%", [])
    }
    let elev = opt(q_d_elevation)
    let azim = opt(q_d_azimuth)
    if elev.truthy() || azim.truthy() {
      if elev.truthy() {
        f("set view ~d", [elev])
      } else {
        f("set view ", [])
      }
      if azim.truthy() {
        f(", ~d", [azim])
      }
      f("~%", [])
    }
  }
  // color_bar can be used by plot3d or plot2d
  if !opt(q_d_color_bar).truthy() {
    f("unset colorbox~%", [])
  }
  // ----- BEGIN GNUPLOT 4.0 WORK-AROUND -----
  // When the expression plotted is constant, Gnuplot 4.0 fails with a
  // division by 0.  Explicitly assigning cbrange prevents the error. Also
  // set zrange to match cbrange.
  if floatp(opt(q_d_const_expr)) {
    let c = opt(q_d_const_expr)
    f("set cbrange [~a : ~a]~%", [num_sub(c, Fix(1L)), num_add(c, Fix(1L))])
    f("set zrange [~a : ~a]~%", [num_sub(c, Fix(1L)), num_add(c, Fix(1L))])
  }
  // -----  END GNUPLOT 4.0 WORK-AROUND  -----
  // logarithmic plots
  if opt(q_d_logx).truthy() {
    f("set log x~%", [])
  }
  if opt(q_d_logy).truthy() {
    f("set log y~%", [])
  }
  // axes labels and legend
  if opt(q_d_xlabel).truthy() {
    f("set xlabel ~s~%", [opt(q_d_xlabel)])
  }
  if opt(q_d_ylabel).truthy() {
    f("set ylabel ~s~%", [opt(q_d_ylabel)])
  }
  if opt(q_d_zlabel).truthy() {
    f("set zlabel ~s~%", [opt(q_d_zlabel)])
  }
  if memq(q_d_legend, plot_options).truthy() && opt(q_d_legend) is Nil {
    f("unset key~%", [])
  }
  // plotting box
  if memq(q_mbox, plot_options).truthy() && !opt(q_mbox).truthy() {
    f("unset border~%", [])
    if opt(q_d_axes).truthy() && type_is("plot2d") {
      f("set xtics axis~%set ytics axis~%set ztics axis~%", [])
    } else {
      f("unset xtics~%unset ytics~%unset ztics~%", [])
    }
  } else {
    f("set border 4095~%", [])
  }
  // 2d grid (specific to plot2d)
  if type_is("plot2d") {
    f("set grid front~%", [])
    if opt(q_d_grid2d).truthy() {
      f("set grid~%", [])
    } else {
      f("unset grid~%", [])
    }
    // plot size and aspect ratio for plot2d
    if opt(q_d_same_xy).truthy() {
      f("set size ratio -1~%", [])
    } else if opt(q_d_yx_ratio).truthy() {
      f("set size ratio ~f~%", [opt(q_d_yx_ratio)])
    } else if !opt(q_d_xy_scale).truthy() {
      // emit the default only if there is no xy_scale specified.
      f("set size ratio 0.75~%", [])
    }
    if opt(q_d_xy_scale).truthy() && listp(opt(q_d_xy_scale)) {
      f("set size ~{~f~^, ~}~%", [opt(q_d_xy_scale)])
    }
  }
  // plot size and aspect ratio for plot3d
  if type_is("plot3d") {
    if opt(q_d_same_xy).truthy() {
      f("set view equal xy~%", [])
    }
    if opt(q_d_same_xyz).truthy() {
      f("set view equal xyz~%", [])
    }
    if opt(q_d_zmin).truthy() {
      f("set xyplane at ~f~%", [opt(q_d_zmin)])
    }
  }
  // axes tics
  gnuplot_def__tics(dest, plot_options, q_d_xtics, "xtics")
  gnuplot_def__tics(dest, plot_options, q_d_ytics, "ytics")
  gnuplot_def__tics(dest, plot_options, q_d_ztics, "ztics")
  gnuplot_def__tics(dest, plot_options, q_d_color_bar_tics, "cbtics")
  // axes ranges and style
  if opt(q_d_x).truthy() && listp(opt(q_d_x)) {
    f("set xrange [~{~,,,,,,'eg~^ : ~}]~%", [opt(q_d_x)])
  }
  if opt(q_d_y).truthy() && listp(opt(q_d_y)) {
    f("set yrange [~{~,,,,,,'eg~^ : ~}]~%", [opt(q_d_y)])
  }
  if opt(q_d_z).truthy() && listp(opt(q_d_z)) {
    f("set zrange [~{~,,,,,,'eg~^ : ~}]~%", [opt(q_d_z)])
  }
  if type_is("plot2d") && memq(q_d_axes, plot_options).truthy() {
    let axes = opt(q_d_axes)
    if axes.truthy() {
      if eq(axes, q_d_x) {
        f("set xzeroaxis~%", [])
      } else if eq(axes, q_d_y) {
        f("set yzeroaxis~%", [])
      } else if eq(axes, q_d_solid) {
        f("set zeroaxis lt -1~%", [])
      } else {
        f("set zeroaxis~%", [])
      }
    }
  }
  // title and labels
  if opt(q_d_title).truthy() {
    f("set title \"~a\"~%", [opt(q_d_title)])
  }
  if opt(q_d_label).truthy() {
    for label in opt(q_d_label).iter() {
      if listp(label) && length(label) == 4 {
        f("set label ~s at ~{~f~^, ~}~%", [cadr(label), cddr(label)])
      }
    }
  }
  // identifier for missing data
  f("set datafile missing ~s~%", [symval(q_ear_missing_data_indicator)])
  plot.data = plot.data + get_output_stream_string(dest)
  // returns a list with the name of the file created, or nil
  if second(terminal_file) is Nil {
    Nil
  } else {
    list1(second(terminal_file))
  }
}

///|
/// The y range of the points of POINTS-LISTS whose x is within the range
/// of OPTIONS, enlarged by 5% on each side: the "set yrange" line written
/// by the PLOT2D-COMMAND methods, or None.
fn plot__auto_yrange(points_lists : Value, options : Value) -> (Value, Value)? raise {
  let mut ymin : Value = Nil
  let mut ymax : Value = Nil
  let mut xmin : Value = Flo(-1.7976931348623157e308)
  let mut xmax : Value = Flo(1.7976931348623157e308)
  if getf(options, q_d_x).truthy() {
    xmin = first(getf(options, q_d_x))
    xmax = second(getf(options, q_d_x))
  }
  for points_list in points_lists.iter() {
    let len = length(points_list)
    let mut i = 0
    // (dotimes (i (/ (length points-list) 2)) ...)
    while 2 * i < len {
      let x = nth(i * 2, points_list)
      let y = nth(1 + i * 2, points_list)
      if numberp(x) && num_ge(x, xmin) && num_le(x, xmax) {
        if numberp(y) {
          if numberp(ymin) {
            if numberp(ymax) {
              if num_lt(y, ymin) {
                ymin = y
              }
              if num_gt(y, ymax) {
                ymax = y
              }
            } else if num_lt(y, ymin) {
              ymax = ymin
              ymin = y
            } else {
              ymax = y
            }
          } else if numberp(ymax) {
            if num_gt(y, ymax) {
              ymin = ymax
              ymax = y
            } else {
              ymin = y
            }
          } else {
            ymin = y
          }
        }
      }
      i = i + 1
    }
  }
  if numberp(ymin) && numberp(ymax) && num_lt(ymin, ymax) {
    let nmin = num_sub(num_mul(Flo(1.05), ymin), num_mul(Flo(0.05), ymax))
    let nmax = num_sub(num_mul(Flo(1.05), ymax), num_mul(Flo(0.05), ymin))
    Some((nmin, nmax))
  } else {
    None
  }
}

///|
/// The legend of the PLOT2D-COMMAND methods: drop the legends of the
/// functions with no points.
fn plot__prune_legends(points_lists : Value, options : Value) -> Unit raise {
  let legends = getf(options, q_d_legend)
  if legends.truthy() {
    let mut legends_new : Value = Nil
    for i in 0..<length(legends) {
      if cdr(nth(i, points_lists)).truthy() {
        legends_new = cons(nth(i, legends), legends_new)
      }
    }
    plot__putf(options, q_d_legend, reverse(legends_new)) |> ignore
  }
}

///|
/// The title of the I-th function V of the PLOT2D-COMMAND methods.
fn plot__plot_name(v : Value, fun : Value, options : Value, legend : Value, i : Int) -> Value raise {
  if memq(q_d_legend, options).truthy() {
    if first(legend).truthy() {
      ensure_string(nth((i - 1) % length(legend), legend))
    } else {
      Nil
    }
  } else if length(fun) == 2 {
    Nil
  } else {
    let pn = make_string_output_stream()
    if atom(v) {
      format(pn, "~a", [d_sconcat(list1(v))]) |> ignore
    } else if eq(second(v), q_d_parametric) {
      format(pn, "~a, ~a", [
        d_sconcat(list1(third(v))),
        d_sconcat(list1(fourth(v))),
      ])
      |> ignore
    } else if eq(second(v), q_d_discrete) {
      format(pn, "discrete~a", [int(i)]) |> ignore
    } else {
      format(pn, "~a", [d_sconcat(list1(v))]) |> ignore
    }
    let plot_name : Value = Str(get_output_stream_string(pn))
    if length(plot_name) > 50 {
      format(Nil, "fun~a", [int(i)])
    } else {
      plot_name
    }
  }
}

///|
/// Method PLOT2D-COMMAND of gnuplot-plot.
fn gnuplot_def__plot2d_command(
  plot : PlotObj,
  fun : Value,
  options : Value,
  range : Value,
) -> Unit raise {
  // Compute points to plot for each element of FUN.  If no plottable points
  // are found, end with an error.
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
        f("set yrange [~,,,,,,'eg: ~,,,,,,'eg]~%", [ymin, ymax])
      None => ()
    }
  }
  // user's commands; may overule any of the previous settings
  if getf(options, q_d_gnuplot_postamble).truthy() &&
    length(getf(options, q_d_gnuplot_postamble)) > 0 {
    f("~a~%", [getf(options, q_d_gnuplot_postamble)])
  }
  // plot command
  f("plot", [])
  if getf(options, q_d_x).truthy() {
    f(" [~{~,,,,,,'eg~^ : ~}]", [getf(options, q_d_x)])
  }
  if getf(options, q_d_y).truthy() {
    if !getf(options, q_d_x).truthy() {
      f(" []", [])
    }
    f(" [~{~,,,,,,'eg~^ : ~}]", [getf(options, q_d_y)])
  }
  let mut legend = getf(options, q_d_legend)
  let mut colors = getf(options, q_d_color)
  let types = getf(options, q_d_point_type)
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
      if d_listp(car(points_list)).truthy() {
        for level in cdar(points_list).iter() {
          let style = style_for(i)
          i = i + 1
          let plot_name = ensure_string(level)
          if i > 1 {
            f(",", [])
          }
          f(" '-'", [])
          f(" title ~s ", [plot_name])
          f(lstring(gnuplot_curve_style(style, colors, types, int(i))), [])
        }
        break
      }
      let style = style_for(i)
      i = i + 1
      // label the expression according to the legend, unless it is "false"
      // or there is only one expression
      let plot_name = plot__plot_name(v, fun, options, legend, i)
      if i > 1 {
        f(",", [])
      }
      f(" '-'", [])
      if plot_name.truthy() {
        f(" title ~s ", [plot_name])
      } else {
        f(" notitle ", [])
      }
      f(lstring(gnuplot_curve_style(style, colors, types, int(i))), [])
    }
  }
  // Parses points data
  f("~%", [])
  let mut in_discontinuity = false
  let mut points = false
  let x0 = first(getf(options, q_d_x))
  let y0 = first(getf(options, q_d_y))
  let write_points = (pts : Value) => {
    let mut p = pts
    while p is Cons(_) {
      let v = car(p)
      let w = cadr(p)
      if eq(v, q_moveto) {
        // A blank line means a discontinuity
        if !in_discontinuity {
          f("~%", [])
          in_discontinuity = true
        }
      } else {
        f("~,,,,,,'eg ~,,,,,,'eg ~%", [v, w])
        points = true
        in_discontinuity = false
      }
      p = cddr(p)
    }
  }
  for points_list in points_lists.iter() {
    if points_list.truthy() {
      // case "contour" with several plots in one list
      if d_listp(car(points_list)).truthy() {
        for level in cdr(points_list).iter() {
          write_points(cdr(level))
          if !points && x0.truthy() && y0.truthy() {
            f("~,,,,,,'eg ~,,,,,,'eg ~%", [x0, y0])
          }
          f("e~%", [])
        }
        break
      }
      // other cases with only one plot per list
      write_points(points_list)
      if !points && x0.truthy() && y0.truthy() {
        f("~,,,,,,'eg ~,,,,,,'eg ~%", [x0, y0])
      }
    }
    if points_list.truthy() {
      f("e~%", [])
    }
  }
  plot.data = plot.data + get_output_stream_string(st)
}

///|
/// Method PLOT3D-COMMAND of gnuplot-plot.
fn gnuplot_def__plot3d_command(
  plot : PlotObj,
  functions : Value,
  options : Value,
  titles : Value,
) -> Unit raise {
  let n = length(functions)
  let pstream = make_string_output_stream()
  with_special(q_d_pstream, pstream, () => {
    // user's commands; may overule any of the previous settings
    if getf(options, q_d_gnuplot_postamble).truthy() &&
      length(getf(options, q_d_gnuplot_postamble)) > 0 {
      format(pstream, "~a~%", [getf(options, q_d_gnuplot_postamble)]) |> ignore
    }
    // gnuplot command to produce the 3d plot
    format(pstream, "~a", [
      gnuplot_plot3d_command(
        Str("-"),
        getf(options, q_d_palette),
        getf(options, q_d_gnuplot_curve_styles),
        {
          let m = getf(options, q_d_mesh_lines_color)
          if m.truthy() { m } else { Str("#000000") }
        },
        titles,
        int(n),
      ),
    ])
    |> ignore
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
      if trans.truthy() {
        funcall(trans, [points]) |> ignore
      }
      if getf(options, q_d_transform_xy).truthy() {
        mfuncall(getf(options, q_d_transform_xy), list1(points)) |> ignore
      }
      output_points(points, m=first(getf(options, q_d_grid))) |> ignore
      format(pstream, "e~%", []) |> ignore
    }
  })
  plot.data = plot.data + get_output_stream_string(pstream)
}

///|
/// The function of the surface F = (fun xrange yrange) of the PLOT3D-COMMAND
/// methods and its transformation: a parametric surface is plotted as
/// $zero_fun transformed by make_transform; other functions are coerced
/// (with function name FNAME) and checked at the middle of the domain.
fn plot__surface_fun(f : Value, fname : String?) -> (Value, Value) raise {
  let fun = first(f)
  let xrange = second(f)
  let yrange = third(f)
  if d_listp(fun).truthy() {
    let trans = d_make_transform(
      list4(list1(q_mlist), second(xrange), second(yrange), q_d_z),
      second(fun),
      third(fun),
      fourth(fun),
    )
    (q_d_zero_fun, trans)
  } else {
    let x0 = third(xrange)
    let x1 = fourth(xrange)
    let y0 = third(yrange)
    let y1 = fourth(yrange)
    let xmid = num_add(x0, num_div(num_sub(x1, x0), Fix(2L)))
    let ymid = num_add(y0, num_div(num_sub(y1, y0), Fix(2L)))
    let lvars = list3(list1(q_mlist), second(xrange), second(yrange))
    let fun = match fname {
      Some(nm) => coerce_float_fun(fun, list2(lvars, Str(nm)))
      None => coerce_float_fun(fun, list1(lvars))
    }
    // Evaluate FUN at the middle point of the range.  Looking at a single
    // point is somewhat unreliable.  Call FUN with numerical arguments
    // (symbolic arguments may fail due to trouble computing real/imaginary
    // parts for complicated expressions, or it may be a numerical function)
    if cdr(d_listofvars(funcall(fun, [xmid, ymid]))).truthy() {
      mtell(
        list1(
          Str(
            "plot3d: expected <expr. of v1 and v2>, [v1,min,max], [v2,min,max]~%",
          ),
        ),
      )
      |> ignore
      mtell(list1(Str("plot3d: keep going and hope for the best.~%"))) |> ignore
    }
    (fun, Nil)
  }
}

///|
/// Method PLOT-SHIPOUT of gnuplot-plot.
fn gnuplot_def__plot_shipout(
  plot : PlotObj,
  options : Value,
  output_file : Value,
) -> Value raise {
  let fmt = getf(options, q_d_plot_format)
  if eq(fmt, q_d_gnuplot) {
    let file = plot_set_gnuplot_script_file_name(options)
    write_file(lstring(file), plot.data)
    gnuplot_process(options, file~, out_file=output_file) |> ignore
    cons(list1(q_mlist), cons(file, output_file))
  } else if eq(fmt, q_d_gnuplot_pipes) {
    send_gnuplot_command(Str(plot.data)) |> ignore
    if output_file.truthy() {
      send_gnuplot_command(Str("unset output")) |> ignore
      cons(list1(q_mlist), output_file)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn gnuplot_process(
  plot_options : Value,
  file? : Value = Nil,
  out_file? : Value = Nil,
) -> Value raise {
  let gnuplot_term = getf(plot_options, q_d_gnuplot_term)
  let run_viewer = getf(plot_options, q_d_run_viewer)
  let gnuplot_preamble = string_downcase(
    lstring(getf(plot_options, q_d_gnuplot_preamble)),
  )
  // creates the output file, when there is one to be created
  if out_file.truthy() && !eq(gnuplot_term, q_d_default) {
    d_system(
      list2(
        symval(q_d_gnuplot_command),
        format(Nil, lstring(symval(q_d_gnuplot_file_args)), [file]),
      ),
    )
    |> ignore
  }
  // displays contents of the output file, when gnuplot-term is dumb, or
  // runs gnuplot when gnuplot-term is default
  if run_viewer.truthy() {
    if eq(gnuplot_term, q_d_default) {
      // the options given to gnuplot will be different when the user
      // redirects the output by using "set output" in the preamble
      let args = if gnuplot_preamble.contains("set out") {
        symval(q_d_gnuplot_file_args)
      } else {
        symval(q_d_gnuplot_view_args)
      }
      d_system(
        list2(
          symval(q_d_gnuplot_command),
          format(Nil, lstring(args), [file]),
        ),
      )
      |> ignore
    } else if eq(gnuplot_term, q_d_dumb) {
      if out_file.truthy() {
        d_printfile(car(out_file)) |> ignore
      } else {
        merr("plotting: option 'gnuplot_out_file' not defined.", []) |> ignore
      }
    }
  }
  Nil
}

// gnuplot_pipes functions. They allow the use of Gnuplot through a pipe in
// order to keep it active (this makes it possible for instance, to rotate
// a 3d surface with the mouse)

///|
/// Quote S for /bin/sh.
fn gnuplot_def__shell_quote(s : String) -> String {
  "'" + s.replace_all(old="'", new="'\\''") + "'"
}

///|
fn start_gnuplot_process(path : Value) -> Value raise {
  let p = lstring(path)
  // (sb-ext:run-program path nil :input :stream :output *error-output*
  //                    :wait nil :search t)
  let (status, _) = shell_command_output(
    "command -v " + gnuplot_def__shell_quote(p) + " >/dev/null 2>&1",
  )
  if status != 0 {
    raise LispError::SimpleError(
      "Couldn't execute \"" + p + "\": No such file or directory",
    )
  }
  let h = open_output_pipe(
    "exec " + gnuplot_def__shell_quote(p) + " 1>&2",
  )
  if h >= 0 {
    set(q_ear_gnuplot_stream, int(h)) |> ignore
  }
  if symval(q_ear_gnuplot_stream) is Nil {
    merr(
      "plotting: I tried to execute ~s but *GNUPLOT-STREAM* is still null.~%",
      [path],
    )
    |> ignore
  }
  // set mouse must be the first command send to gnuplot
  send_gnuplot_command(Str("set mouse"))
}

///|
fn check_gnuplot_process() -> Value raise {
  if symval(q_ear_gnuplot_stream) is Nil {
    start_gnuplot_process(symval(q_d_gnuplot_command))
  } else {
    Nil
  }
}

///|
fn d_gnuplot_close() -> Value raise {
  stop_gnuplot_process() |> ignore
  Str("")
}

///|
fn d_gnuplot_start() -> Value raise {
  check_gnuplot_process() |> ignore
  Str("")
}

///|
fn d_gnuplot_restart() -> Value raise {
  d_gnuplot_close() |> ignore
  d_gnuplot_start()
}

///|
fn d_gnuplot_send(command : Value) -> Value raise {
  send_gnuplot_command(command)
}

///|
fn stop_gnuplot_process() -> Value raise {
  let s = symval(q_ear_gnuplot_stream)
  if s.truthy() {
    close_output_pipe(to_int(s)) |> ignore
    set(q_ear_gnuplot_stream, Nil)
  } else {
    Nil
  }
}

///|
fn send_gnuplot_command(command : Value, recursive? : Value = Nil) -> Value raise {
  if symval(q_ear_gnuplot_stream) is Nil {
    start_gnuplot_process(symval(q_d_gnuplot_command)) |> ignore
  }
  if command is Nil {
    return Nil
  }
  let text = lstring(format(Nil, "~a ~%", [command]))
  let h = to_int(symval(q_ear_gnuplot_stream))
  if pipe_write_string(h, text) {
    return Nil
  }
  let e = LispError::SimpleError(
    "Couldn't write to the Gnuplot process: Broken pipe",
  )
  // allow gnuplot to restart if stream-error, or just an error is signaled
  // only try to restart once, to prevent an infinite loop
  if recursive.truthy() {
    raise e
  }
  format(
    error_output,
    "WARNING: ~a~%Trying new stream.~%",
    [Str("Couldn't write to the Gnuplot process: Broken pipe")],
  )
  |> ignore
  close_output_pipe(h) |> ignore
  set(q_ear_gnuplot_stream, Nil) |> ignore
  send_gnuplot_command(command, recursive=t)
}

///|
fn d_gnuplot_reset() -> Value raise {
  send_gnuplot_command(Str("unset output")) |> ignore
  send_gnuplot_command(Str("reset"))
}

///|
fn d_gnuplot_replot(s? : Value = Nil) -> Value raise {
  if symval(q_ear_gnuplot_stream) is Nil {
    merr("gnuplot_replot: Gnuplot is not running.", []) |> ignore
  }
  if s is Nil {
    send_gnuplot_command(Str("replot")) |> ignore
  } else if stringp(s) {
    send_gnuplot_command(s) |> ignore
    send_gnuplot_command(Str("replot")) |> ignore
  } else {
    merr(
      "gnuplot_replot: argument, if present, must be a string; found: ~M",
      [s],
    )
    |> ignore
  }
  Str("")
}

///|
/// Returns a file name where the Gnuplot commands will be saved.
fn plot_set_gnuplot_script_file_name(options : Value) -> Value raise {
  let gnuplot_term = getf(options, q_d_gnuplot_term)
  let gnuplot_out_file = getf(options, q_d_gnuplot_out_file)
  let fmt = getf(options, q_d_plot_format)
  if (eq(fmt, q_d_gnuplot_pipes) || eq(fmt, q_d_gnuplot)) &&
    eq(gnuplot_term, q_d_default) &&
    gnuplot_out_file.truthy() {
    plot_file_path(gnuplot_out_file, preserve_file=t, plot_options=options)
  } else {
    plot_file_path(
      format(Nil, "~a.~a", [
        random_name(Fix(16L)),
        ensure_string(getf(options, q_d_plot_format)),
      ]),
      preserve_file=Nil,
      plot_options=options,
    )
  }
}

///|
fn init_gnuplot_def() -> Unit raise {
  defmvar(
    q_d_gnuplot_command,
    val=Str("gnuplot"),
    list([
      kw("setting-predicate"),
      list2(q_string_predicate, Str("must be a string")),
    ]),
  )
  |> ignore
}
