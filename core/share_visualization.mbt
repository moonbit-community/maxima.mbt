// Port of share/dynamics/visualization.lisp: scene, 3D scenes rendered by
// Xmaxima with VTK (Jaime E. Villate).

///|
/// translates Maxima scene object's option values into Xmaxima input syntax
fn tcl_vtk_option_value(name : Value, values : Value) -> Value raise {
  let values = if d_listp(car(values)).truthy() { cdar(values) } else { values }
  let st = make_string_output_stream()
  format(st, "{~a", [name]) |> ignore
  for num in values.iter() {
    if plotcolorp(num).truthy() {
      format(st, "~{ ~d~}", [hexrgb_to_decimal(rgb_color(num))]) |> ignore
    } else if integerp(num) {
      format(st, " ~d", [num]) |> ignore
    } else if floatp(num) {
      format(st, " ~f", [num]) |> ignore
    } else if d_numberp(num).truthy() {
      format(st, " ~f ", [coerce_float(num)]) |> ignore
    } else if d_constantp(num).truthy() &&
      d_freeof(list2(q_d__pcti, num)).truthy() &&
      !(eq(num, t) || num is Nil) &&
      !d_listp(num).truthy() {
      format(st, " ~f ", [coerce_float(num)]) |> ignore
    } else if d_listp(num).truthy() {
      format(st, "~a", [tcl_output_number_list(num)]) |> ignore
    } else {
      merr(
        "scene: Wrong value for option ~M~%Expecting a number; found: ~M",
        [name, num],
      )
      |> ignore
    }
  }
  format(st, "} ", []) |> ignore
  Str(get_output_stream_string(st))
}

///|
/// converts a Maxima list into a floating-point Tcl list string
fn tcl_output_number_list(maxlist : Value) -> Value raise {
  let st = make_string_output_stream()
  format(st, "{ ", []) |> ignore
  for num in cdr(maxlist).iter() {
    if floatp(num) {
      format(st, "~f ", [num]) |> ignore
    } else if d_numberp(num).truthy() {
      format(st, "~f ", [coerce_float(num)]) |> ignore
    } else if d_constantp(num).truthy() &&
      d_freeof(list2(q_d__pcti, num)).truthy() &&
      !(eq(num, t) || num is Nil) &&
      !d_listp(num).truthy() {
      format(st, "~f ", [coerce_float(num)]) |> ignore
    } else if d_listp(num).truthy() {
      format(st, "~a", [tcl_output_number_list(num)]) |> ignore
    } else {
      merr("scene: Wrong value in animation list: ~M", [num]) |> ignore
    }
  }
  format(st, "} ", []) |> ignore
  Str(get_output_stream_string(st))
}

///|
/// converts a hexadecimal rgb color string into list of numbers from 0 to 1
fn hexrgb_to_decimal(color : Value) -> Value raise {
  let s = lstring(color)
  let n = s.length()
  list3(
    num_div(plotcolors__parse_hex(lstring(subseq(color, 1, end=3))), Flo(255.0)),
    num_div(plotcolors__parse_hex(lstring(subseq(color, 3, end=5))), Flo(255.0)),
    num_div(plotcolors__parse_hex(lstring(subseq(color, 5, end=n))), Flo(255.0)),
  )
}

///|
/// parses a scene option into a command-line option passed to Xmaxima
fn scene_option_to_tcl(option : Value) -> Value raise {
  let mut option = option
  let name = car(option)
  let realp_ = plot__pred("realp", v => realp(v))
  let nm = match name {
    Sym(s) => s.name
    _ => ""
  }
  match nm {
    "$azimuth" => {
      if cadr(option).truthy() {
        rplaca(cdr(option), parse_azimuth(cadr(option))) |> ignore
      }
      check_option(option, realp_, Str("a real number"), count=Fix(1L)) |> ignore
    }
    "$elevation" => {
      if cadr(option).truthy() {
        rplaca(cdr(option), parse_elevation(cadr(option))) |> ignore
      }
      check_option(option, realp_, Str("a real number"), count=Fix(1L)) |> ignore
    }
    "$tstep" => {
      let v = check_option(option, realp_, Str("a real number"), count=Fix(1L))
      option = list2(name, v)
    }
    "$width" | "$height" => {
      let v = check_option(
        option,
        plot__pred("naturalp", v => naturalp(v).truthy()),
        Str("a natural number"),
        count=Fix(1L),
      )
      option = list2(name, v)
    }
    "$restart" => {
      let v = check_option_boole(option)
      option = list2(name, if v.truthy() { Fix(1L) } else { Fix(0L) })
    }
    "$background" => {
      let v = check_option(
        option,
        plot__pred("plotcolorp", v => plotcolorp(v).truthy()),
        Str("a color"),
      )
      option = cons(name, hexrgb_to_decimal(rgb_color(v)))
    }
    "$windowtitle" | "$windowname" => {
      let v = check_option(
        option,
        plot__pred("string", v => {
          plot__string_designator(v) |> ignore
          true
        }),
        Str("a string"),
        count=Fix(1L),
      )
      option = list2(name, v)
    }
    _ => merr("scene: Unknown option ~M", [name]) |> ignore
  }
  let vv = mapcar(a => if symbolp(a) { ensure_string(a) } else { a }, option)
  let st = make_string_output_stream()
  format(st, "-~(~a~) ", [first(vv)]) |> ignore
  format(st, "{~{~a~^ ~}}", [cdr(vv)]) |> ignore
  Str(get_output_stream_string(st))
}

///|
/// (cdr (assoc key alist)) for an alist of (symbol . string) pairs.
fn visualization__lookup(key : Value, alist : Array[(Value, String)]) -> String? {
  for p in alist {
    if eq(p.0, key) {
      return Some(p.1)
    }
  }
  None
}

///|
fn d_scene(arguments : Value) -> Value raise {
  let mut objects : Array[Value] = []
  let mut options : Array[Value] = []
  let lf = "\n"
  let classes = [
    (q_d_cube, "Cube"),
    (q_d_sphere, "Sphere"),
    (q_d_cylinder, "Cylinder"),
    (q_d_cone, "Cone"),
  ]
  // VTK methods for the objects in classes
  let cmethods = [
    (q_d_center, "Center"),
    (q_d_radius, "Radius"),
    (q_d_height, "Height"),
    (q_d_resolution, "Resolution"),
    (q_d_latlongtessellation, "LatLongTessellation"),
    (q_d_thetaresolution, "ThetaResolution"),
    (q_d_phiresolution, "PhiResolution"),
    (q_d_starttheta, "StartTheta"),
    (q_d_endtheta, "EndTheta"),
    (q_d_startphi, "StartTheta"),
    (q_d_endphi, "EndTheta"),
    (q_d_capping, "Capping"),
    (q_d_direction, "Direction"),
    (q_d_xlength, "XLength"),
    (q_d_ylength, "YLength"),
    (q_d_zlength, "ZLength"),
    (q_d_bounds, "Bounds"),
    (q_d_angle, "Angle"),
  ]
  // VTK methods for properties
  let pmethods = [
    (q_d_color, "Color"),
    (q_d_opacity, "Opacity"),
    (q_d_ambient, "Ambient"),
    (q_d_ambientcolor, "AmbientColor"),
    (q_d_specular, "Specular"),
    (q_d_specularcolor, "SpecularColor"),
    (q_d_diffuse, "Diffuse"),
    (q_d_diffusecolor, "DiffuseColor"),
    (q_d_edgevisibility, "EdgeVisibility"),
    (q_d_edgecolor, "EdgeColor"),
    (q_d_linewidth, "LineWidth"),
    (q_d_pointsize, "PointSize"),
    (q_d_lightning, "Lightning"),
    (q_d_shading, "Shading"),
    (q_d_texture, "Texture"),
    (q_d_representation, "Representation"),
    (q_d_points, "RepresentationToPoints"),
    (q_d_wireframe, "RepresentationToWireframe"),
    (q_d_surface, "RepresentationToSurface"),
    (q_d_interpolation, "Interpolation"),
    (q_d_flat, "InterpolationToFlat"),
    (q_d_gourand, "InterpolationToGourand"),
    (q_d_phong, "InterpolationToPhong"),
    (q_d_stipplepattern, "LineStipplePattern"),
    (q_d_stipplerepeat, "LineStippleRepeatFactor"),
    (q_d_frontculling, "FrontFaceCulling"),
    (q_d_backculling, "BackFaceCulling"),
  ]
  // VTK methods for actors
  let amethods = [
    (q_d_origin, "Origin"),
    (q_d_scale, "Scale"),
    (q_d_position, "Position"),
    (q_d_orientation, "Orientation"),
    (q_d_usertransform, "UserTransform"),
  ]
  // separates arguments between objects and options
  for v0 in arguments.iter() {
    let v = if listp(v0) { cdr(v0) } else { list1(v0) }
    if visualization__lookup(car(v), classes) is Some(_) {
      objects.push(v)
    } else {
      options.push(v)
    }
  }
  // sets up output file name to pass to Xmaxima
  let file = plot_temp_file(format(Nil, "maxout~d.xmaxima", [getpid()]))
  // parses objects
  let mut objs = ""
  for v in objects {
    let mut copts = ""
    let mut popts = ""
    let mut aopts = ""
    let mut animate = ""
    let vtkname = visualization__lookup(car(v), classes).unwrap_or("")
    // parses object properties
    for w in cdr(v).iter() {
      if !d_listp(w).truthy() {
        merr("scene: Wrong option; expecting a list; found:  ~M", [w]) |> ignore
      }
      match visualization__lookup(second(w), cmethods) {
        Some(prop) =>
          copts = copts + lstring(tcl_vtk_option_value(Str(prop), cddr(w)))
        None =>
          match visualization__lookup(second(w), pmethods) {
            Some(prop) =>
              popts = popts + lstring(tcl_vtk_option_value(Str(prop), cddr(w)))
            None =>
              match visualization__lookup(second(w), amethods) {
                Some(prop) =>
                  aopts = aopts +
                    lstring(tcl_vtk_option_value(Str(prop), cddr(w)))
                None =>
                  if eql(second(w), q_d_animate) {
                    match visualization__lookup(third(w), amethods) {
                      Some(prop) =>
                        animate = "{" +
                          prop +
                          " 0 " +
                          lstring(tcl_output_number_list(fourth(w))) +
                          "}"
                      None =>
                        merr("scene: ~M cannot be animated.", [third(w)])
                        |> ignore
                    }
                  } else if eql(second(w), q_d_track) {
                    animate = "{Position 1 " +
                      lstring(tcl_output_number_list(third(w))) +
                      "}"
                  } else {
                    mtell(list2(Str("scene: Ignored option: ~M"), second(w)))
                    |> ignore
                  }
              }
          }
      }
    }
    // save object name and properties in string objs
    objs = objs +
      "{" +
      vtkname +
      lf +
      "{" +
      copts +
      "}" +
      lf +
      "{" +
      popts +
      "}" +
      lf +
      "{" +
      aopts +
      "}" +
      lf +
      animate +
      "}" +
      lf
  }
  // parse scene options and copy them to string opts
  let mut opts = " "
  for v in options {
    opts = opts + " " + lstring(scene_option_to_tcl(v))
  }
  let data = if symval(q_d_show_openplot).truthy() {
    format(Nil, "scene ~a -objects {~a}~%", [Str(opts), Str(objs)])
  } else {
    format(Nil, "{scene ~a -objects {~a}}", [Str(opts), Str(objs)])
  }
  ignore(data)
  ignore(file)
  // (show-open-plot data file): SHOW-OPEN-PLOT is not defined in Maxima
  raise LispError::SimpleError("The function SHOW-OPEN-PLOT is undefined.")
}
