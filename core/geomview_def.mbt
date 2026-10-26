// Port of src/geomview_def.lisp: routines for Maxima's interface to
// geomview (the methods of the geomview-plot class).

///|
/// Given a valid palette, it returns its definition for Geomview.
fn geomview_palette(palette : Value) -> Value raise {
  let mut colors : Value = Nil
  let hex = (l : Value) => mapcar(c => hex_to_numeric_list(c), l)
  if atom(palette) {
    if getf(symval(q_ear_plot_palettes), palette).truthy() {
      colors = hex(
        mapcar(c => rgb_color(c), cdr(getf(symval(q_ear_plot_palettes), palette))),
      )
    } else {
      colors = rgb_color(palette)
      if !colors.truthy() {
        colors = Str("#ffffff")
      }
    }
  } else {
    let kind = car(palette)
    if eq(kind, q_d_gradient) {
      colors = hex(mapcar(c => rgb_color(c), cdr(palette)))
    } else if eq(kind, q_d_hue) ||
      eq(kind, q_d_saturation) ||
      eq(kind, q_d_value) {
      let mut h = second(palette)
      let mut s = third(palette)
      let mut v = fourth(palette)
      let d = num_div(fifth(palette), Flo(6.0))
      colors = cons(hex_to_numeric_list(d_hsv(h, s, v)), colors)
      for _ in 0..<6 {
        if eq(kind, q_d_hue) {
          h = num_mod(num_add(h, d), Fix(1L))
        } else if eq(kind, q_d_saturation) {
          s = num_mod(num_add(s, d), Fix(1L))
        } else {
          v = num_mod(num_add(v, d), Fix(1L))
        }
        colors = cons(hex_to_numeric_list(d_hsv(h, s, v)), colors)
      }
      colors = reverse(colors)
    } else {
      colors = hex(mapcar(c => rgb_color(c), palette))
    }
  }
  colors
}

///|
/// Interpolate within a list of colors, given as lists with three elements
/// between 0 and 1 (red, blue and green), according to the value of z,
/// between 0 and 1, where 0 gives the first color and 1 the last one.
fn geomview_z_color(z : Value, colors : Value) -> Value raise {
  let l = length(colors)
  let (n, r) = num_floor(num_mul(z, int(l - 1)))
  if num_eq(n, int(l - 1)) {
    nth(to_int(n), colors)
  } else {
    let c1 = nth(to_int(n), colors)
    let c2 = nth(to_int(n) + 1, colors)
    plotcolors__map2(
      (a, b) => num_add(a, b),
      c1,
      mapcar(
        x => num_mul(r, x),
        plotcolors__map2((a, b) => num_sub(a, b), c2, c1),
      ),
    )
  }
}

///|
/// Method PLOT-PREAMBLE of geomview-plot.
fn geomview_def__plot_preamble(plot : PlotObj, options : Value) -> Value raise {
  let bgcolor = getf(options, q_d_background_color)
  let st = make_string_output_stream()
  let f = (ctl : String, args : Array[Value]) => format(st, ctl, args) |> ignore
  // record Maxima version and date-time
  f("# Created by Maxima ~a~%", [symval(q_ear_autoconf_version)])
  f("# ~a~%", [d_timedate()])
  f("(ui-panel tools off)~%(bbox-draw targetgeom no)~%", [])
  if bgcolor.truthy() {
    f("(backcolor targetcam  ~{~,6f~^ ~})~%", [
      hex_to_numeric_list(rgb_color(bgcolor)),
    ])
  } else {
    f("(backcolor targetcam 1 1 1)~%", [])
  }
  f("(camera targetcam {perspective 0})~%", [])
  f("(geometry plot3d {~%", [])
  f("INST~%transform~%", [])
  geomview_matrix(st, getf(options, q_d_azimuth), getf(options, q_d_elevation))
  |> ignore
  plot.data = get_output_stream_string(st)
  Nil
}

///|
/// Method PLOT3D-COMMAND of geomview-plot.
fn geomview_def__plot3d_command(
  plot : PlotObj,
  functions : Value,
  options : Value,
  titles : Value,
) -> Unit raise {
  ignore(titles)
  let palette = getf(options, q_d_palette)
  let nxint = first(getf(options, q_d_grid))
  let nyint = second(getf(options, q_d_grid))
  let meshcolor = getf(options, q_d_mesh_lines_color)
  let lighting = getf(options, q_d_lighting)
  let colors = if palette.truthy() { geomview_palette(palette) } else { Nil }
  let st = make_string_output_stream()
  let f = (ctl : String, args : Array[Value]) => format(st, ctl, args) |> ignore
  // generate the mesh points for each surface in the functions stack
  for sf in functions.iter() {
    let fun0 = first(sf)
    let xrange = second(sf)
    let yrange = third(sf)
    let xvar = second(xrange)
    let yvar = second(yrange)
    let x0 = third(xrange)
    let x1 = fourth(xrange)
    let y0 = third(yrange)
    let y1 = fourth(yrange)
    let mut type_ = ""
    let mut texture = ""
    let mut material = ""
    f("geom {~%LIST~%{~%", [])
    if palette.truthy() {
      if listp(colors) {
        type_ = "COFF"
      } else {
        type_ = "OFF"
        material = lstring(
          format(Nil, "diffuse ~{~,6f~^ ~}", [hex_to_numeric_list(colors)]),
        )
      }
      texture = if lighting.truthy() { "+smooth" } else { "+csmooth" }
      if meshcolor.truthy() {
        texture = texture + " +edge"
        material = material +
          lstring(
            format(Nil, " edgecolor ~{~,6f~^ ~}", [
              hex_to_numeric_list(rgb_color(meshcolor)),
            ]),
          )
      }
    } else {
      type_ = "OFF"
      texture = "-face +edge"
      if meshcolor.truthy() {
        material = material +
          lstring(
            format(Nil, " edgecolor ~{~,6f~^ ~}", [
              hex_to_numeric_list(rgb_color(meshcolor)),
            ]),
          )
      }
      // (else the result of (concatenate 'string material " edgecolor 0 0
      // 0") is discarded)
    }
    f("appearance { ~a material {~a} {linewidth 2}}~%", [
      Str(texture),
      Str(material),
    ])
    let (fun, trans) = if d_listp(fun0).truthy() {
      let lvars = list4(list1(q_mlist), xvar, yvar, q_d_z)
      (
        q_d_zero_fun,
        d_make_transform(lvars, second(fun0), third(fun0), fourth(fun0)),
      )
    } else {
      let lvars = list3(list1(q_mlist), xvar, yvar)
      let fun = coerce_float_fun(fun0, list1(lvars))
      check_3dfun(
        fun,
        num_add(x0, num_div(num_sub(x1, x0), Fix(2L))),
        num_add(y0, num_div(num_sub(y1, y0), Fix(2L))),
      )
      |> ignore
      (fun, Nil)
    }
    let (points, points_count) = draw3d(fun, x0, x1, y0, y1, nxint, nyint)
    if trans.truthy() {
      funcall(trans, [points]) |> ignore
    }
    if getf(options, q_d_transform_xy).truthy() {
      mfuncall(getf(options, q_d_transform_xy), list1(points)) |> ignore
    }
    let faces = polygons(vertices_matrix(points, nxint, nyint))
    // Finds the minimum and maximum values of x, y and z
    let mut maxx : Value = Flo(-1.7976931348623157e308)
    let mut minx : Value = Flo(1.7976931348623157e308)
    let mut maxy = maxx
    let mut miny = minx
    let mut maxz = maxx
    let mut minz = minx
    let len = length(points)
    let mut i = 0
    while i < len {
      let x = elt(points, i)
      let y = elt(points, i + 1)
      let z = elt(points, i + 2)
      if floatp(x) {
        if num_lt(x, minx) {
          minx = x
        }
        if num_gt(x, maxx) {
          maxx = x
        }
      }
      if floatp(y) {
        if num_lt(y, miny) {
          miny = y
        }
        if num_gt(y, maxy) {
          maxy = y
        }
      }
      if floatp(z) {
        if num_lt(z, minz) {
          minz = z
        }
        if num_gt(z, maxz) {
          maxz = z
        }
      }
      i = i + 3
    }
    // Outputs the points coordinates, normalized from 0 to 1
    f(type_, [])
    f(" ~a ~a 0~%", [points_count, int(length(faces))])
    let rangex = num_sub(maxx, minx)
    let rangey = num_sub(maxy, miny)
    let rangez = num_sub(maxz, minz)
    let mut i = 0
    while i < len {
      let mut pt : Value = Nil
      for n in 0..<3 {
        pt = cons(elt(points, i + n), pt)
      }
      if length(remove(t, pt)) == 3 {
        pt = list3(
          num_div(num_sub(third(pt), minx), rangex),
          num_div(num_sub(second(pt), miny), rangey),
          num_div(num_sub(first(pt), minz), rangez),
        )
        f("~{~,6f~^ ~}", [pt])
        if type_ == "COFF" {
          f(" ~{~,6f ~}1~%", [geomview_z_color(third(pt), colors)])
        } else {
          f("~%", [])
        }
      }
      i = i + 3
    }
    for face in faces.iter() {
      f("~d ~{~d~^ ~}~%", [int(length(face)), face])
    }
    f("}~%", [])
  }
  if !(memq(q_mbox, options).truthy() && !getf(options, q_mbox).truthy()) {
    geomview_bbox(st) |> ignore
  }
  f("}~%})~%(zoom targetcam 1.5)~%", [])
  plot.data = plot.data + get_output_stream_string(st)
}

///|
/// Method PLOT-SHIPOUT of geomview-plot.
fn geomview_def__plot_shipout(
  plot : PlotObj,
  options : Value,
  output_file : Value,
) -> Value raise {
  ignore(options)
  let file = plot_file_path(format(Nil, "maxout~d.gcl", [int(process_id())]))
  write_file(lstring(file), plot.data)
  d_system(
    list2(symval(q_d_geomview_command), format(Nil, " ~s &", [file])),
  )
  |> ignore
  cons(list1(q_mlist), cons(file, output_file))
}

///|
/// Evaluate FUN at the middle point of the range.  Looking at a single
/// point is somewhat unreliable.  Call FUN with numerical arguments
/// (symbolic arguments may fail due to trouble computing real/imaginary
/// parts for complicated expressions, or it may be a numerical function)
fn check_3dfun(fun : Value, x : Value, y : Value) -> Value raise {
  if cdr(d_listofvars(mfuncall(fun, list2(x, y)))).truthy() {
    mtell(
      list1(
        Str(
          "plot3d: expected <expr. of v1 and v2>, [v1,min,max], [v2,min,max]~%",
        ),
      ),
    )
    |> ignore
    mtell(list1(Str("plot3d: keep going and hope for the best.~%")))
  } else {
    Nil
  }
}

///|
fn geomview_matrix(st : Value, az : Value, el : Value) -> Value raise {
  if floatp(az) && floatp(el) {
    let p = coerce_float(q_d__pctpi)
    let a = num_mul(num_div(az, Flo(180.0)), p)
    let e = num_mul(num_div(el, Flo(180.0)), p)
    let ca = lcos(a)
    let sa = lsin(a)
    let ce = lcos(e)
    let se = lsin(e)
    format(st, "{~,7f ~,7f ~,7f 0~%", [
      ca,
      num_neg(num_mul(sa, ce)),
      num_mul(sa, se),
    ])
    |> ignore
    format(st, " ~,7f ~,7f ~,7f 0~%", [
      sa,
      num_mul(ca, ce),
      num_neg(num_mul(ca, se)),
    ])
    |> ignore
    format(st, " 0 ~,7f ~,7f 0~%", [se, ce]) |> ignore
    format(st, " 0 0 0 1}~%", [])
  } else {
    format(st, "{0.8660254 -0.25 0.4330127 0~%", []) |> ignore
    format(st, " 0.5 0.4330127 -0.75 0~%", []) |> ignore
    format(st, " 0 0.8660254 0.5 0~%", []) |> ignore
    format(st, " 0 0 0 1}~%", [])
  }
}

///|
fn geomview_bbox(st : Value) -> Value raise {
  let f = (ctl : String) => format(st, ctl, []) |> ignore
  f("# bounding box~%LIST~%{ appearance {linewidth 2}~%VECT~%")
  f("4 16 0 10 2 2 2 0 0 0 0~%")
  f("0 0 0 0 1 0 1 1 0 1 0 0 0 0 0~%")
  f("0 0 1 1 0 1 1 1 1 0 1 1 0 0 1~%")
  f("0 1 0 0 1 1 1 0 0 1 0 1 1 1 0 1 1 1~%}~%")
  f("# x, y and z labels~%LIST~%{ appearance {linewidth 2}~%VECT~%")
  f("5 13 0 2 2 2 3 4 0 0 0 0 0~%")
  f("# letter x~%")
  f("0.47 0 -0.03 0.53 0 -0.09 0.53 0 -0.03 0.47 0 -0.09~%")
  f("# letter y~%")
  f("0 0.5 -0.06 0 0.5 -0.09 0 0.47 -0.03 0 0.5 -0.06 0 0.53 -0.03~%")
  f("# letter z~%")
  f("-0.09 0 0.53 -0.03 0 0.53 -0.09 0 0.47 -0.03 0 0.47~%}~%")
  Nil
}
