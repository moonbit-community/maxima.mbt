// Port of share/draw/vtk.lisp: the VTK renderer of the draw package. It
// writes a Python script that builds the scene with the VTK library.  The
// port cannot run programs, so the script is written but never executed
// (draw_vtk skips the ($system "python ...") call).

// ---------------------------------------------------------------------------
// Private helpers

///|
/// `(format nil ctl args...)` as a MoonBit string.
fn share_draw_vtk__f(ctl : String, args : Array[Value]) -> String raise {
  format_to_string(ctl, args)
}

///|
/// A name built from PREFIX and the incremented counter COUNTER
/// (`(format nil "prefix~a" (incf counter))`).
fn share_draw_vtk__name(prefix : String, counter : Value) -> Value raise {
  let v = num_add(symval(counter), Fix(1L))
  set(counter, v) |> ignore
  format(Nil, prefix + "~a", [v])
}

///|
/// *draw-enhanced3d-type* as an Int.
fn share_draw_vtk__e3d() -> Int raise {
  to_int(symval(q_ear_draw_enhanced3d_type))
}

///|
/// *draw-isolines-type* as an Int.
fn share_draw_vtk__iso() -> Int raise {
  to_int(symval(q_ear_draw_isolines_type))
}

///|
/// (funcall *draw-enhanced3d-fun* args...)
fn share_draw_vtk__e3d_fun(args : Array[Value]) -> Value raise {
  funcall(symval(q_ear_draw_enhanced3d_fun), args)
}

///|
/// (funcall *draw-isolines-fun* args...)
fn share_draw_vtk__iso_fun(args : Array[Value]) -> Value raise {
  funcall(symval(q_ear_draw_isolines_fun), args)
}

///|
/// A Lisp list of fixnums.
fn share_draw_vtk__ints(xs : Array[Int]) -> Value {
  list(xs.map(x => int(x)))
}

///|
/// Maxima's $sin, $cos, ... applied to a number.
fn share_draw_vtk__m(op : Value, x : Value) -> Value raise {
  ftake(op, [x])
}

///|
/// (subsetp l1 l2 :test #'like)
fn share_draw_vtk__subsetp_like(l1 : Value, l2 : Value) -> Bool raise {
  every(x => some(y => like(x, y).truthy(), l2), l1)
}

///|
/// (count t l)
fn share_draw_vtk__count_t(l : Value) -> Int {
  let mut n = 0
  for x in l.iter() {
    if eq(x, t) {
      n = n + 1
    }
  }
  n
}

///|
/// (string-trim " " key)
fn share_draw_vtk__trim_key(key : Value) -> String {
  string_trim(" ", lstring(key))
}

///|
/// The line stipple pattern of a line type, or NIL.
fn share_draw_vtk__stipple(line_type : Value) -> Value {
  if eql(line_type, Fix(0L)) {
    Str("0x0001")
  } else if eql(line_type, Fix(1L)) {
    Str("0xFFFF")
  } else if eql(line_type, Fix(2L)) {
    Str("0xFF00")
  } else if eql(line_type, Fix(6L)) {
    Str("0xFE10")
  } else {
    Nil
  }
}

///|
/// Translate some gnuplot line type codes into vtk codes.
fn share_draw_vtk__vtk_linetype(linetype : Value) -> Value {
  if eql(linetype, Fix(0L)) {
    Fix(3L)
  } else if eql(linetype, Fix(6L)) {
    Fix(4L)
  } else {
    linetype
  }
}

///|
/// (round (* 255 c))
fn share_draw_vtk__c255(c : Value) -> Value raise {
  round1(num_mul(Fix(255L), c))
}

///|
/// Common tail of the surface objects: the code coloring with enhanced3d
/// and drawing the isolines.
fn share_draw_vtk__surface_tail(
  str : StringBuilder,
  mapper_name : Value,
  source_name : Value,
  points_name : Value,
  filter_name : Value,
  lookup_table_name : Value,
  scalars : Value,
  scalars2 : Value,
  linewidth : Value,
) -> Unit raise {
  if share_draw_vtk__e3d() > 0 {
    str.write_string(
      share_draw_vtk__f("~a.SetLookupTable(~a)~%", [mapper_name, lookup_table_name]),
    )
    str.write_string(
      share_draw_vtk__f("~a.SetScalarModeToUsePointFieldData()~%", [mapper_name]),
    )
    str.write_string(share_draw_vtk__f("~a.ScalarVisibilityOn()~%~%", [mapper_name]))
    let floatarray_name = get_floatarray_name()
    str.write_string(
      share_draw_vtk__f("~a~%", [
        vtkfloatarray_code(floatarray_name, source_name, scalars),
      ]),
    )
    // remove next string if we want isolines and solid color when
    // enhanced3d is not active
    str.write_string(
      share_draw_vtk__f("~a.SelectColorArray(\"name~a\")~%", [
        mapper_name, floatarray_name,
      ]),
    )
    sethash(
      symval(q_ear_vtk_extract_counter),
      symval(q_ear_enhanced3d_or_isolines_code),
      format(Nil, "rescalearray(~a,~a)~%", [points_name, floatarray_name]),
    )
    |> ignore
  }
  if share_draw_vtk__iso() > 0 {
    let floatarray2_name = get_floatarray_name()
    str.write_string(
      share_draw_vtk__f("~a~%", [
        vtkfloatarray_code(floatarray2_name, source_name, scalars2),
      ]),
    )
    let filter2_name = get_filter_name()
    str.write_string(
      share_draw_vtk__f("~a~%", [vtkcontourfilter_code(filter2_name, filter_name)]),
    )
    let mapper2_name = get_mapper_name()
    str.write_string(
      share_draw_vtk__f("~a", [
        vtkpolydatamapper_isoline_code(mapper2_name, source_name, floatarray2_name),
      ]),
    )
    str.write_string(
      share_draw_vtk__f("~a~%", [vtkactor_isoline_code(get_actor_name(), linewidth)]),
    )
    str.write_string(
      share_draw_vtk__f("~a~%", [
        vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
      ]),
    )
    sethash(
      symval(q_ear_vtk_extract_counter),
      symval(q_ear_enhanced3d_or_isolines_code),
      format(Nil, "rescalearray(~a,~a)~%", [points_name, floatarray2_name]),
    )
    |> ignore
  }
}

///|
/// Common middle part of the surface objects: polydata, points, cells,
/// transform, mapper, actor and extractor.
fn share_draw_vtk__surface_body(
  str : StringBuilder,
  source_name : Value,
  points_name : Value,
  cellarray_name : Value,
  trans_name : Value,
  filter_name : Value,
  mapper_name : Value,
  actor_name : Value,
  x : Value,
  y : Value,
  z : Value,
  cells : Value,
  color : Value,
  opacity : Value,
  linewidth : Value,
  wiredsurface : Value,
) -> Unit raise {
  str.write_string(share_draw_vtk__f("~a=vtk.vtkPolyData()~%", [source_name]))
  str.write_string(
    share_draw_vtk__f("~a~%", [vtkpoints_code(points_name, source_name, x, y, z)]),
  )
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkcellarray_code(cellarray_name, source_name, Fix(2L), cells),
    ]),
  )
  str.write_string(share_draw_vtk__f("~a~%", [vtktransform_code(trans_name)]))
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtktransformpolydatafilter_code(filter_name, source_name, trans_name, t),
    ]),
  )
  str.write_string(
    share_draw_vtk__f("~a~%", [vtkpolydatamapper_code(mapper_name, filter_name, Nil)]),
  )
  str.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [points_name]))
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkactor_code(actor_name, Nil, color, opacity, linewidth, wiredsurface),
    ]),
  )
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, t),
    ]),
  )
}

///|
/// (let ((lut (check-lookup-table))) (format str "~a~%" (cadr lut)) (car lut))
fn share_draw_vtk__lut(str : StringBuilder) -> Value raise {
  let lut = check_lookup_table()
  let name = car(lut)
  str.write_string(share_draw_vtk__f("~a~%", [cadr(lut)]))
  name
}

// ---------------------------------------------------------------------------
// Names

///|
fn get_appenddata_name() -> Value raise {
  share_draw_vtk__name("appenddata", q_ear_vtk_appenddata_counter)
}

///|
fn get_extract_name() -> Value raise {
  share_draw_vtk__name("extract", q_ear_vtk_extract_counter)
}

///|
fn get_outline_name() -> Value raise {
  share_draw_vtk__name("outline", q_ear_vtk_outline_counter)
}

///|
fn get_outlineactor_name() -> Value raise {
  share_draw_vtk__name("outlineactor", q_ear_vtk_outlineactor_counter)
}

///|
fn get_textproperty_name() -> Value raise {
  share_draw_vtk__name("textproperty", q_ear_vtk_textproperty_counter)
}

///|
fn get_cubeaxesactor2d_name() -> Value raise {
  share_draw_vtk__name("cubeaxesactor2d", q_ear_vtk_cubeaxesactor2d_counter)
}

///|
fn get_camera_name() -> Value raise {
  share_draw_vtk__name("camera", q_ear_vtk_camera_counter)
}

///|
fn get_renderer_name() -> Value raise {
  share_draw_vtk__name("renderer", q_ear_vtk_renderer_counter)
}

///|
fn get_source_name() -> Value raise {
  share_draw_vtk__name("source", q_ear_vtk_source_counter)
}

///|
fn get_mapper_name() -> Value raise {
  share_draw_vtk__name("mapper", q_ear_vtk_mapper_counter)
}

///|
fn get_actor_name() -> Value raise {
  share_draw_vtk__name("actor", q_ear_vtk_actor_counter)
}

///|
fn get_labelactor_name() -> Value raise {
  share_draw_vtk__name("labelactor", q_ear_vtk_labelactor_counter)
}

///|
fn get_trans_name() -> Value raise {
  share_draw_vtk__name("trans", q_ear_vtk_trans_counter)
}

///|
fn get_filter_name() -> Value raise {
  share_draw_vtk__name("filter", q_ear_vtk_filter_counter)
}

///|
fn get_floatarray_name() -> Value raise {
  share_draw_vtk__name("floatarray", q_ear_vtk_floatarray_counter)
}

///|
fn get_data_file_name() -> Value raise {
  let v = num_add(symval(q_ear_vtk_data_file_counter), Fix(1L))
  set(q_ear_vtk_data_file_counter, v) |> ignore
  format(Nil, "data~a.vtk", [v])
}

///|
fn get_points_name() -> Value raise {
  share_draw_vtk__name("points", q_ear_vtk_points_counter)
}

///|
fn get_glyphpoints_name() -> Value raise {
  share_draw_vtk__name("glyphpoints", q_ear_vtk_glyphpoints_counter)
}

///|
fn get_polydata_name() -> Value raise {
  share_draw_vtk__name("polydata", q_ear_vtk_polydata_counter)
}

///|
fn get_cellarray_name() -> Value raise {
  share_draw_vtk__name("cellarray", q_ear_vtk_cellarray_counter)
}

///|
fn get_polydatamapper_name() -> Value raise {
  share_draw_vtk__name("polydatamapper", q_ear_vtk_polydatamapper_counter)
}

///|
fn get_solidsource_name() -> Value raise {
  share_draw_vtk__name("solidsource", q_ear_vtk_solidsource_counter)
}

///|
fn get_triangle_name() -> Value raise {
  share_draw_vtk__name("triangle", q_ear_vtk_triangle_counter)
}

///|
fn get_label_name() -> Value raise {
  share_draw_vtk__name("label", q_ear_vtk_label_counter)
}

///|
fn get_chart_name() -> Value raise {
  share_draw_vtk__name("chart", q_ear_vtk_chart_counter)
}

///|
fn get_table_name() -> Value raise {
  share_draw_vtk__name("table", q_ear_vtk_table_counter)
}

///|
fn get_arrayx_name() -> Value raise {
  share_draw_vtk__name("arrayX", q_ear_vtk_arrayx_counter)
}

///|
fn get_arrayy_name() -> Value raise {
  share_draw_vtk__name("arrayY", q_ear_vtk_arrayy_counter)
}

///|
fn get_isolines_name() -> Value raise {
  share_draw_vtk__name("isolines", q_ear_vtk_isolines_counter)
}

// ---------------------------------------------------------------------------
// Python code builders

///|
fn scenebounds() -> Value raise {
  let xrange = get_option(q_d_xrange)
  let yrange = get_option(q_d_yrange)
  let zrange = get_option(q_d_zrange)
  let code = (if xrange.truthy() {
      share_draw_vtk__f("mib[0]=~a~%mxb[1]=~a~%", [car(xrange), cadr(xrange)])
    } else {
      ""
    }) +
    (if yrange.truthy() {
      share_draw_vtk__f("mib[2]=~a~%mxb[3]=~a~%", [car(yrange), cadr(yrange)])
    } else {
      ""
    }) +
    (if zrange.truthy() {
      share_draw_vtk__f("mib[4]=~a~%mxb[5]=~a~%", [car(zrange), cadr(zrange)])
    } else {
      ""
    })
  format(Nil, "~a~%~a~%~a~%~a~%~a~%~a~%~a~%~a~a~%~%", [
    Str("if sys.version_info[0] < 3:"),
    Str("    trb = zip(*bounds)"),
    Str("else:"),
    Str("    trb = list(zip(*bounds))"),
    Str("mib = [min(i) for i in trb]"),
    Str("mxb = [max(i) for i in trb]"),
    Str("ranges = vtk.vtkBox()"),
    Str(code),
    Str("ranges.SetBounds(mib[0],mxb[1],mib[2],mxb[3],mib[4],mxb[5])"),
  ])
}

///|
let share_draw_vtk__rescalearray_lines : Array[String] = [
  "def rescalearray( pts, arr ):", "   mini = 1.0", "   maxi = 0.0", "   n = arr.GetNumberOfTuples()",
  "   for i in range(0, n):", "       v = pts.GetPoint(i)", "       f = arr.GetValue(i)",
  "       if (v[0] >= mib[0] and v[0] <= mxb[1] and", "           v[1] >= mib[2] and v[1] <= mxb[3] and",
  "           v[2] >= mib[4] and v[2] <= mxb[5]):", "           if f < mini:", "              mini = f",
  "           if f > maxi:", "              maxi = f", "   if maxi > mini:", "      for i in range(0, n):",
  "          arr.SetValue(i, (arr.GetValue(i)-mini)/(maxi-mini))", "   return;",
]

///|
fn vtkappendpolydata_code(an : Value, fe : Value, fl : Value) -> Value raise {
  let str = StringBuilder::new()
  let table = symval(q_ear_enhanced3d_or_isolines_code)
  if hash_table_count(table) > 0 {
    // (format str (format nil "~V@{~a~:*~}~%" 18 "~a~%") ...): the 18
    // lines, each followed by a newline, then a newline.
    for line in share_draw_vtk__rescalearray_lines {
      str.write_string(line)
      str.write_string("\n")
    }
    str.write_string("\n")
  }
  str.write_string(share_draw_vtk__f("~a=vtk.vtkAppendPolyData()~%", [an]))
  let mut n = to_int(fe)
  while n <= to_int(symval(q_ear_vtk_extract_counter)) {
    let nv = int(n)
    str.write_string(share_draw_vtk__f("~%extract~a.SetImplicitFunction(ranges)~%", [nv]))
    str.write_string(
      share_draw_vtk__f("extract~a.SetInputConnection(filter~a.GetOutputPort())~%", [
        nv, nv,
      ]),
    )
    str.write_string(
      share_draw_vtk__f("mapper~a.SetInputConnection(extract~a.GetOutputPort())~%", [
        nv, nv,
      ]),
    )
    if gethash(nv, table).truthy() {
      str.write_string(share_draw_vtk__f("~a", [gethash(nv, table)]))
      remhash(nv, table) |> ignore
    }
    str.write_string(share_draw_vtk__f("actor~a.SetMapper(mapper~a)~%", [nv, nv]))
    str.write_string(
      share_draw_vtk__f("~a.AddInputConnection(extract~a.GetOutputPort())~%", [an, nv]),
    )
    n = n + 1
  }
  let mut n = to_int(fl)
  while n <= to_int(symval(q_ear_vtk_label_counter)) {
    str.write_string(
      share_draw_vtk__f("~a.AddInputConnection(label~a.GetOutputPort())~%", [
        an,
        int(n),
      ]),
    )
    n = n + 1
  }
  str.write_string(share_draw_vtk__f("~%~a.Update()~%~%", [an]))
  Str(str.to_string())
}

///|
fn vtkoutlinefilter_code(on : Value, an : Value) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkOutlineFilter()~%", [on]) +
    share_draw_vtk__f("~a.SetInputConnection(~a.GetOutputPort())~%", [on, an]),
  )
}

///|
fn vtkpolydatamapper_code(mn : Value, fn_ : Value, con : Value) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkPolyDataMapper()~%", [mn]) +
    (if con.truthy() {
      share_draw_vtk__f("~a.SetInputConnection(~a.GetOutputPort())~%", [mn, fn_])
    } else {
      ""
    }),
  )
}

///|
/// Isolines mapper.
fn vtkpolydatamapper_isoline_code(
  mn : Value,
  sn : Value,
  fn_ : Value,
) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkPolyDataMapper()~%", [mn]) +
    share_draw_vtk__f("~a.GetPointData().SetActiveScalars(\"name~a\")~%", [sn, fn_]) +
    share_draw_vtk__f("~a.ScalarVisibilityOn()~%", [mn]),
  )
}

///|
fn vtkextractpolydatageometry_code(
  en : Value,
  cell : Value,
  poin : Value,
) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkExtractPolyDataGeometry()~%", [en]) +
    (if cell.truthy() {
      share_draw_vtk__f("~a.ExtractBoundaryCellsOn()~%", [en])
    } else {
      share_draw_vtk__f("~a.ExtractBoundaryCellsOff()~%", [en])
    }) +
    (if poin.truthy() {
      share_draw_vtk__f("~a.PassPointsOn()~%", [en])
    } else {
      share_draw_vtk__f("~a.PassPointsOff()~%", [en])
    }),
  )
}

///|
fn vtktextproperty_code(tn : Value) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkTextProperty()~%", [tn]) +
    share_draw_vtk__f("~a.SetColor(0,0,0)~%", [tn]),
  )
}

///|
fn vtkcubeaxesactor2d_code(can : Value, adn : Value, tn : Value) -> Value raise {
  let s = StringBuilder::new()
  s.write_string(share_draw_vtk__f("~a=vtk.vtkCubeAxesActor2D()~%", [can]))
  s.write_string(
    share_draw_vtk__f("~a.SetInputConnection(~a.GetOutputPort())~%", [can, adn]),
  )
  s.write_string(share_draw_vtk__f("~a.SetLabelFormat(\"%6.4g\")~%", [can]))
  s.write_string(share_draw_vtk__f("~a.SetFlyModeToOuterEdges()~%", [can]))
  s.write_string(share_draw_vtk__f("~a.SetFontFactor(0.8)~%", [can]))
  s.write_string(share_draw_vtk__f("~a.SetAxisTitleTextProperty(~a)~%", [can, tn]))
  s.write_string(share_draw_vtk__f("~a.SetAxisLabelTextProperty(~a)~%", [can, tn]))
  s.write_string(
    share_draw_vtk__f("~a.SetXLabel(\"~a\")~%", [can, get_option(q_d_xlabel)]),
  )
  s.write_string(
    share_draw_vtk__f("~a.SetYLabel(\"~a\")~%", [can, get_option(q_d_ylabel)]),
  )
  s.write_string(
    share_draw_vtk__f("~a.SetZLabel(\"~a\")~%~%", [can, get_option(q_d_zlabel)]),
  )
  Str(s.to_string())
}

///|
fn vtkrenderer3d_code(
  rn : Value,
  an : Value,
  on : Value,
  bgcol : Value,
  cn : Value,
  rv : Value,
  rh : Value,
  fa : Value,
  fl : Value,
) -> Value raise {
  let k : Value = Flo(0.0174532925199433) // %pi/180
  let rvk = num_mul(k, rv)
  let rhk = num_mul(k, rh)
  let x = num_mul(share_draw_vtk__m(q_p_sin, rvk), share_draw_vtk__m(q_p_sin, rhk))
  let y = num_neg(
    num_mul(share_draw_vtk__m(q_p_sin, rvk), share_draw_vtk__m(q_p_cos, rhk)),
  )
  let z = share_draw_vtk__m(q_p_cos, rvk)
  let colist = share_draw__hex_to_numeric_list(bgcol)
  let str = StringBuilder::new()
  str.write_string(share_draw_vtk__f("~a=vtk.vtkCamera()~%", [cn]))
  str.write_string(share_draw_vtk__f("~a.SetPosition(~a,~a,~a)~%", [cn, x, y, z]))
  str.write_string(share_draw_vtk__f("~a=vtk.vtkRenderer()~%", [rn]))
  str.write_string(
    share_draw_vtk__f("~a.SetBackground(~a,~a,~a)~%", [
      rn,
      first(colist),
      second(colist),
      third(colist),
    ]),
  )
  for n in to_int(fa)..=to_int(symval(q_ear_vtk_actor_counter)) {
    str.write_string(share_draw_vtk__f("~a.AddActor(actor~a)~%", [rn, int(n)]))
  }
  for n in to_int(fl)..=to_int(symval(q_ear_vtk_labelactor_counter)) {
    str.write_string(share_draw_vtk__f("~a.AddActor(labelactor~a)~%", [rn, int(n)]))
  }
  str.write_string(share_draw_vtk__f("~a.SetCamera(~a.GetActiveCamera())~%", [an, rn]))
  if get_option(q_d_axis_3d).truthy() {
    str.write_string(share_draw_vtk__f("~a.AddActor(~a)~%", [rn, on])) // add box
    str.write_string(share_draw_vtk__f("~a.AddViewProp(~a)~%", [rn, an])) // add axes tics
  }
  str.write_string(share_draw_vtk__f("~a.SetActiveCamera(~a)~%", [rn, cn]))
  str.write_string(share_draw_vtk__f("~a.ResetCamera()~%~%", [rn]))
  Str(str.to_string())
}

///|
fn vtkrenderer2d_code(cn : Value, rn : Value) -> Value raise {
  let colist = share_draw__hex_to_numeric_list(get_option(q_d_background_color))
  let xrange = get_option(q_d_xrange)
  let yrange = get_option(q_d_yrange)
  let str = StringBuilder::new()
  if yrange.truthy() {
    str.write_string(share_draw_vtk__f("~a.GetAxis(0).SetBehavior(1)~%", [cn]))
    str.write_string(
      share_draw_vtk__f("~a.GetAxis(0).SetRange(~a,~a)~%~%", [
        cn,
        first(yrange),
        second(yrange),
      ]),
    )
  }
  if xrange.truthy() {
    str.write_string(share_draw_vtk__f("~a.GetAxis(1).SetBehavior(1)~%", [cn]))
    str.write_string(
      share_draw_vtk__f("~a.GetAxis(1).SetRange(~a,~a)~%~%", [
        cn,
        first(xrange),
        second(xrange),
      ]),
    )
  }
  str.write_string(
    share_draw_vtk__f("scene~a=vtk.vtkContextScene()~%scene~a.AddItem(~a)~%", [
      cn, cn, cn,
    ]),
  )
  str.write_string(
    share_draw_vtk__f("actor~a=vtk.vtkContextActor()~%actor~a.SetScene(scene~a)~%", [
      cn, cn, cn,
    ]),
  )
  str.write_string(
    share_draw_vtk__f("~a.SetShowLegend(~a)~%", [
      cn,
      if num_gt(symval(q_ear_vtk_2dkey_counter), Fix(0L)) {
        Fix(1L)
      } else {
        Fix(0L)
      },
    ]),
  )
  str.write_string(
    share_draw_vtk__f("~a.GetAxis(0).SetTitle(\"~a\")~%", [cn, get_option(q_d_ylabel)]),
  )
  str.write_string(
    share_draw_vtk__f("~a.GetAxis(1).SetTitle(\"~a\")~%", [cn, get_option(q_d_xlabel)]),
  )
  if get_option(q_d_logx).truthy() {
    str.write_string(share_draw_vtk__f("~a.GetAxis(1).SetLogScale(1)~%", [cn]))
  }
  if get_option(q_d_logy).truthy() {
    str.write_string(share_draw_vtk__f("~a.GetAxis(0).SetLogScale(1)~%", [cn]))
  }
  let mut pos = get_option(q_d_key_pos)
  if pos.truthy() {
    // (mfunction-call $split pos): $split (stringproc) is not defined when
    // vtk.lisp is compiled, so the macro expands to (mfunction-call-aux
    // '$split '(pos) nil), which EVALs the unevaluated form POS.
    pos = rest(mfunction_call_aux(q_d_split, list1(sym("pos")), Nil))
    let vp = first(pos)
    let hp = second(pos)
    let vps = lstring(vp)
    let hps = lstring(hp)
    str.write_string(
      share_draw_vtk__f("~a.GetLegend().SetVerticalAlignment(~a)~%", [
        cn,
        if vps == "top" {
          Fix(3L)
        } else if vps == "center" {
          Fix(1L)
        } else if vps == "bottom" {
          Fix(4L)
        } else {
          Nil
        },
      ]),
    )
    str.write_string(
      share_draw_vtk__f("~a.GetLegend().SetHorizontalAlignment(~a)~%", [
        cn,
        if hps == "left" {
          Fix(0L)
        } else if hps == "center" {
          Fix(1L)
        } else if hps == "right" {
          Fix(2L)
        } else {
          Nil
        },
      ]),
    )
  }
  str.write_string(share_draw_vtk__f("~a=vtk.vtkRenderer()~%", [rn]))
  str.write_string(
    share_draw_vtk__f("~a.SetBackground(~a,~a,~a)~%", [
      rn,
      first(colist),
      second(colist),
      third(colist),
    ]),
  )
  str.write_string(share_draw_vtk__f("~a.AddActor(actor~a)~%", [rn, cn]))
  str.write_string(share_draw_vtk__f("scene~a.SetRenderer(~a)~%", [cn, rn]))
  Str(str.to_string())
}

///|
fn vtkchartxy_code(cn : Value) -> Value raise {
  let str = StringBuilder::new()
  str.write_string(share_draw_vtk__f("~a = vtk.vtkChartXY()~%", [cn]))
  str.write_string(
    share_draw_vtk__f("~a.GetAxis(0).SetGridVisible(~a)~%", [
      cn,
      if eql(first(get_option(q_d_grid)), Fix(0L)) {
        Fix(0L)
      } else {
        Fix(1L)
      },
    ]),
  )
  str.write_string(
    share_draw_vtk__f("~a.GetAxis(1).SetGridVisible(~a)~%~%", [
      cn,
      if eql(second(get_option(q_d_grid)), Fix(0L)) {
        Fix(0L)
      } else {
        Fix(1L)
      },
    ]),
  )
  Str(str.to_string())
}

///|
fn vtkcellarray_code(
  cn : Value,
  pn : Value,
  celldim : Value,
  ind : Value,
) -> Value raise {
  let str = StringBuilder::new()
  str.write_string(share_draw_vtk__f("~a=vtk.vtkCellArray()~%", [cn]))
  for c in ind.iter() {
    str.write_string(share_draw_vtk__f("~a.InsertNextCell(~a)~%", [cn, int(length(c))]))
    for i in c.iter() {
      str.write_string(share_draw_vtk__f("~a.InsertCellPoint(~a)~%", [cn, i]))
    }
  }
  str.write_string(
    share_draw_vtk__f("~a.~a(~a)~%", [
      pn,
      if eql(celldim, Fix(0L)) {
        Str("SetVerts")
      } else if eql(celldim, Fix(1L)) {
        Str("SetLines")
      } else {
        Str("SetPolys")
      },
      cn,
    ]),
  )
  Str(str.to_string())
}

///|
fn vtkfloatarray_code(
  fan : Value,
  sn : Value,
  values : Value,
  addarr? : Value = t,
) -> Value raise {
  let n = length(values)
  let str = StringBuilder::new()
  str.write_string(share_draw_vtk__f("~a=vtk.vtkFloatArray()~%", [fan]))
  for k in 0..<n {
    str.write_string(
      share_draw_vtk__f("~a.InsertNextValue(~a)~%", [fan, aref1(values, k)]),
    )
  }
  str.write_string(share_draw_vtk__f("~a.SetName(\"name~a\")~%", [fan, fan]))
  str.write_string(
    share_draw_vtk__f("~a.GetPointData().~a(~a)~%", [
      sn,
      if addarr.truthy() {
        Str("AddArray")
      } else {
        Str("SetScalars")
      },
      fan,
    ]),
  )
  Str(str.to_string())
}

///|
fn vtkglyph3d_code(fn_ : Value, sn : Value, pdn : Value) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkGlyph3D()~%", [fn_]) +
    share_draw_vtk__f("~a.SetInputData(~a)~%", [fn_, sn]) +
    share_draw_vtk__f("~a.~a~%", [fn_, pdn]) +
    share_draw_vtk__f("~a.ScalingOff()~%", [fn_]),
  )
}

///|
fn vtkpoints_code(
  pn : Value,
  sn : Value,
  x : Value,
  y : Value,
  z : Value,
) -> Value raise {
  let n = length(x)
  let str = StringBuilder::new()
  str.write_string(share_draw_vtk__f("~a=vtk.vtkPoints()~%", [pn]))
  str.write_string(share_draw_vtk__f("~a.SetNumberOfPoints(~a)~%", [pn, int(n)]))
  for k in 0..<n {
    str.write_string(
      share_draw_vtk__f("~a.InsertPoint(~a,~a,~a,~a)~%", [
        pn,
        int(k),
        aref1(x, k),
        aref1(y, k),
        aref1(z, k),
      ]),
    )
  }
  if sn.truthy() {
    str.write_string(share_draw_vtk__f("~a.SetPoints(~a)~%", [sn, pn]))
  }
  Str(str.to_string())
}

///|
fn vtktransform_code(tn : Value) -> Value raise {
  format(Nil, "~a=vtk.vtkTransform()~%", [tn])
}

///|
fn vtktransformfilter_code(fn_ : Value, sn : Value, tn : Value) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkTransformFilter()~%", [fn_]) +
    share_draw_vtk__f("~a.SetInputConnection(~a.GetOutputPort())~%", [fn_, sn]) +
    share_draw_vtk__f("~a.SetTransform(~a)~%", [fn_, tn]),
  )
}

///|
fn vtktransformpolydatafilter_code(
  fn_ : Value,
  sn : Value,
  tn : Value,
  ds : Value,
) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkTransformPolyDataFilter()~%", [fn_]) +
    (if ds.truthy() {
      share_draw_vtk__f("~a.SetInputData(~a)~%", [fn_, sn])
    } else {
      share_draw_vtk__f("~a.SetInputConnection(~a.GetOutputPort())~%", [fn_, sn])
    }) +
    share_draw_vtk__f("~a.SetTransform(~a)~%", [fn_, tn]),
  )
}

///|
fn vtkactor_code(
  an : Value,
  mn : Value,
  col : Value,
  op : Value,
  lw : Value,
  ws : Value,
) -> Value raise {
  let colist = share_draw__hex_to_numeric_list(col)
  Str(
    share_draw_vtk__f("~a=vtk.vtkActor()~%", [an]) +
    (if mn.truthy() {
      share_draw_vtk__f("~a.SetMapper(~a)~%", [an, mn])
    } else {
      ""
    }) +
    share_draw_vtk__f("~a.GetProperty().SetColor(~a,~a,~a)~%", [
      an,
      first(colist),
      second(colist),
      third(colist),
    ]) +
    share_draw_vtk__f("~a.GetProperty().SetOpacity(~a)~%", [an, op]) +
    share_draw_vtk__f("~a.GetProperty().SetLineWidth(~a)~%", [an, lw]) +
    (if ws.truthy() {
      share_draw_vtk__f(
        "~a.GetProperty().EdgeVisibilityOn()~%~a.GetProperty().SetEdgeColor(0,0,0)~%",
        [an, an],
      )
    } else {
      share_draw_vtk__f("~%", [])
    }),
  )
}

///|
/// Isolines actor.
fn vtkactor_isoline_code(an : Value, lw : Value) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkActor()~%", [an]) +
    share_draw_vtk__f("# ~a.GetProperty().SetColor(1.0,0.0,0.0)~%", [an]) +
    share_draw_vtk__f("~a.GetProperty().SetLineWidth(~a)~%", [an, lw]),
  )
}

///|
/// Glyph actor.
fn vtkactor_glyph_code(an : Value, col : Value, op : Value) -> Value raise {
  let colist = share_draw__hex_to_numeric_list(col)
  Str(
    share_draw_vtk__f("~a=vtk.vtkActor()~%", [an]) +
    share_draw_vtk__f("~a.GetProperty().SetColor(~a,~a,~a)~%", [
      an,
      first(colist),
      second(colist),
      third(colist),
    ]) +
    share_draw_vtk__f("~a.GetProperty().SetOpacity(~a)~%", [an, op]),
  )
}

///|
fn vtktubefilter_code(tn : Value, fn_ : Value, lt : Value) -> Value raise {
  Str(
    share_draw_vtk__f("~a=vtk.vtkTubeFilter()~%", [tn]) +
    share_draw_vtk__f("~a.SetInputConnection(~a.GetOutputPort())~%", [tn, fn_]) +
    share_draw_vtk__f("~a.SetNumberOfSides(~a)~%", [tn, num_neg(lt)]) +
    share_draw_vtk__f("~a.SetRadius(~a)~%", [tn, get_option(q_d_line_width)]),
  )
}

///|
fn vtkcontourfilter_code(in_ : Value, fn_ : Value) -> Value raise {
  let str = StringBuilder::new()
  let contours = get_option(q_d_isolines_levels)
  str.write_string(share_draw_vtk__f("~a=vtk.vtkContourFilter()~%", [in_]))
  str.write_string(
    share_draw_vtk__f("~a.SetInputConnection(~a.GetOutputPort())~%", [in_, fn_]),
  )
  if numberp(contours) {
    // number of isolines
    str.write_string(
      share_draw_vtk__f("~a.GenerateValues(~a,~a.GetOutput().GetScalarRange())~%", [
        in_, contours, fn_,
      ]),
    )
  } else if stringp(contours) &&
    string_search("incremental", lstring(contours)) >= 0 {
    // list with min, step, max
    str.write_string(share_draw_vtk__f("u = [~a]~%", [subseq(contours, 12)]))
    str.write_string(
      share_draw_vtk__f(
        "~a.GenerateValues(int(round((u[2]-u[0]) / u[1])),u[0],u[2])~%",
        [in_],
      ),
    )
  } else {
    // set of user specified contour values
    str.write_string(share_draw_vtk__f("u = [~a]~%", [subseq(contours, 9)]))
    str.write_string(share_draw_vtk__f("for i in range(0, len(u)):~%", []))
    str.write_string(share_draw_vtk__f("   ~a.SetValue(i,u[i])~%", [in_]))
  }
  Str(str.to_string())
}

///|
fn vtkrendererwindow_code(ns : Value) -> Value raise {
  let dim = get_option(q_d_dimensions)
  let ncol = get_option(q_d_columns)
  let str = StringBuilder::new()
  let mut alloc = reverse(symval(q_ear_allocations))
  let mut nilcounter = 0
  let mut nnil = 0
  for a in alloc.iter() {
    if a is Nil {
      nnil = nnil + 1
    }
  }
  let nrow = num_ceiling(int(nnil), b=ncol).0
  let mut dx : Value = Nil
  let mut dy : Value = Nil
  if num_gt(nrow, Fix(0L)) {
    dx = num_div(Flo(1.0), ncol)
    dy = num_div(Flo(1.0), nrow)
  }
  // place scenes on the graphic window
  for counter in 1..=to_int(ns) {
    let thisalloc = car(alloc)
    alloc = cdr(alloc)
    let (x1, y1, x2, y2) = if thisalloc.truthy() {
      // user defined scene allocation
      let x1 = first(thisalloc)
      let y1 = second(thisalloc)
      (x1, y1, num_add(x1, third(thisalloc)), num_add(y1, fourth(thisalloc)))
    } else {
      // automatic scene allocation
      nilcounter = nilcounter + 1
      let x1 = num_mul(num_mod(int(nilcounter - 1), ncol), dx)
      let y1 = num_mul(
        num_sub(nrow, num_ceiling(int(nilcounter), b=ncol).0),
        dy,
      )
      (x1, y1, num_add(x1, dx), num_add(y1, dy))
    }
    str.write_string(
      share_draw_vtk__f("renderer~a.SetViewport(~a,~a,~a,~a)~%", [
        int(counter),
        x1,
        y1,
        x2,
        y2,
      ]),
    )
  }
  str.write_string(
    share_draw_vtk__f("renWin=vtk.vtkRenderWindow()~%renWin.SetMultiSamples(0)~%", []),
  )
  str.write_string(share_draw_vtk__f("renWin.SetSize(~a,~a)~%", [car(dim), cadr(dim)]))
  for k in 1..=to_int(ns) {
    str.write_string(share_draw_vtk__f("renWin.AddRenderer(renderer~a)~%", [int(k)]))
  }
  Str(str.to_string())
}

///|
/// Code for file output.
fn vtk_terminal() -> Value raise {
  let terminal = get_option(q_d_terminal)
  let filename = get_option(q_d_file_name)
  let offscreenterms = list([
    q_d_png, q_d_pngcairo, q_d_jpg, q_d_eps, q_d_eps_color, q_d_tiff, q_d_pnm,
  ])
  let mut extension = ""
  let mut classformat = ""
  if member(terminal, offscreenterms).truthy() {
    if eq(terminal, q_d_png) || eq(terminal, q_d_pngcairo) {
      extension = "png"
      classformat = "vtkPNGWriter"
    } else if eq(terminal, q_d_jpg) {
      extension = "jpg"
      classformat = "vtkJPEGWriter"
    } else if eq(terminal, q_d_tiff) {
      extension = "tif"
      classformat = "vtkTIFFWriter"
    } else if eq(terminal, q_d_pnm) {
      extension = "pnm"
      classformat = "vtkPNMWriter"
    } else if eq(terminal, q_d_eps) || eq(terminal, q_d_eps_color) {
      extension = "eps"
      classformat = "vtkPostScriptWriter"
    }
    format(Nil, "~a~%~a~%~a~%~a~%~a~a()~%~a~%~a(\"~a.~a\")~%~a~%~a~%", [
      Str("renWin.OffScreenRenderingOn()"),
      Str("renWin.Render()"),
      Str("w2if=vtk.vtkWindowToImageFilter()"),
      Str("w2if.SetInput(renWin)"),
      Str("writer=vtk."),
      Str(classformat),
      Str("writer.SetInputConnection(w2if.GetOutputPort())"),
      Str("writer.SetFileName"),
      filename,
      Str(extension),
      Str("writer.Write()"),
      Str("exit()"),
    ])
  } else if eq(terminal, q_d_vrml) {
    format(Nil, "~a~%~a~%~a(\"~a.~a\")~%~a~%~a~%~a~%", [
      Str("vrml=vtk.vtkVRMLExporter()"),
      Str("vrml.SetInput(renWin)"),
      Str("vrml.SetFileName"),
      filename,
      Str("wrl"),
      Str("vrml.SetSpeed(5.5)"),
      Str("vrml.Write()"),
      Str("exit()"),
    ])
  } else if eq(terminal, q_d_obj) {
    format(Nil, "~a~%~a~%~a(\"~a\")~%~a~%~a~%", [
      Str("obj=vtk.vtkOBJExporter()"),
      Str("obj.SetInput(renWin)"),
      Str("obj.SetFilePrefix"),
      filename,
      Str("obj.Write()"),
      Str("exit()"),
    ])
  } else if eq(terminal, q_d_screen) {
    format(Nil, "~a~%~a~%~a~%~a~%~a~%~a~%~a~%", [
      Str("iren=vtk.vtkRenderWindowInteractor()"),
      Str("iren.SetRenderWindow(renWin)"),
      Str("iren.Initialize()"),
      Str("renderer1.ResetCamera()"),
      Str("renderer1.GetActiveCamera().Zoom(1.01)"),
      Str("renWin.Render()"),
      Str("iren.Start()"),
    ])
  } else if eq(terminal, q_d_stl) {
    format(Nil, "~a~%~a~%~a~%~a~%~a~a~a~%~a~%~a~%", [
      Str("triangulator=vtk.vtkTriangleFilter()"),
      Str("triangulator.SetInputConnection(appenddata1.GetOutputPort())"),
      Str("stl=vtk.vtkSTLWriter()"),
      Str("stl.SetInputConnection(triangulator.GetOutputPort())"),
      Str("stl.SetFileName(\""),
      filename,
      Str(".stl\")"),
      Str("stl.Write()"),
      Str("exit()"),
    ])
  } else if eq(terminal, q_d_ply) {
    format(Nil, "~a~%~a~%~a~%~a~%~a~a~a~%~a~%~a~%", [
      Str("triangulator=vtk.vtkTriangleFilter()"),
      Str("triangulator.SetInputConnection(appenddata1.GetOutputPort())"),
      Str("stl=vtk.vtkPLYWriter()"),
      Str("stl.SetInputConnection(triangulator.GetOutputPort())"),
      Str("stl.SetFileName(\""),
      filename,
      Str("\")"),
      Str("stl.Write()"),
      Str("exit()"),
    ])
  } else {
    merr("draw: unknown terminal for vtk", [])
  }
}

///|
/// Checks if lookup table is already created. Returns its position number
/// in *lookup-tables*.
fn lookup_table_exists(pal : Value) -> Value raise {
  let pos = position_if(z => equal(pal, z), symval(q_ear_lookup_tables))
  // a missing table gives position -1, so the result is 0
  int(pos + 1)
}

///|
/// Writes python code for color transform functions.
fn color_transform_function(c : Value, n : Value, f : Value) -> Value raise {
  let pf = if num_lt(f, Fix(0L)) { num_neg(f) } else { f }
  let exprs = [
    "x = 0", "x = 0.5", "x = 1", "x = x", "x = x*x", "x = x*x*x", "x = x*x*x*x", "x = math.sqrt(x)",
    "x = math.sqrt(math.sqrt(x))", "x = math.sin(1.570796326794897*x)", "x = math.cos(1.570796326794897*x)",
    "x = math.fabs(x-0.5)", "x = (2.0*x-1.0)*(2.0*x-1.0)", "x = math.sin(3.141592653589793*x)",
    "x = math.fabs(math.cos(3.141592653589793*x))", "x = math.sin(6.283185307179586*x)",
    "x = math.cos(6.283185307179586*x)", "x = math.fabs(math.sin(6.283185307179586*x))",
    "x = math.fabs(math.cos(6.283185307179586*x))", "x = math.fabs(math.sin(12.56637061435917*x))",
    "x = math.fabs(math.cos(12.56637061435917*x))", "x = 3.0*x", "x = 3.0*x-1.0", "x = 3.0*x-2.0",
    "x = math.fabs(3.0*x-1.0)", "x = math.fabs(3.0*x-2.0)", "x = 1.5*x-0.5", "x = 1.5*x-1.0",
    "x = math.fabs(1.5*x-0.5)", "x = math.fabs(1.5*x-1.0)", "x = interval(x,0.25,0.57)/0.32-0.78125",
    "x = 2*interval(x,0.42,0.92)-0.84",
    "if x <= 0.42:\n    x = 4.0*x\n  elif x <= 0.92:\n    x = -2.0*x+1.84\n  else:\n    x = x/0.08-11.5",
    "x = math.fabs(2.0*x-0.5)", "x = 2*x", "x = 2.0*x-0.5", "x = 2.0*x-1.0",
  ]
  let mut expr : Value = Nil
  for i in 0..<exprs.length() {
    if eql(pf, int(i)) {
      expr = Str(exprs[i])
      break
    }
  }
  Str(
    share_draw_vtk__f("def f~a~a (k):~%", [c, n]) +
    share_draw_vtk__f("  x = unitscale(k)~%", []) +
    share_draw_vtk__f("  ~a~%", [expr]) +
    share_draw_vtk__f("  return interval(x,0,1)~%~%", []),
  )
}

///|
/// Creates lookup table. See info for option 'palette'. Returns list with
/// lookup table name and the string.
fn check_lookup_table() -> Value raise {
  let mut palette = get_option(q_d_palette)
  let mut lut = ""
  if equal(palette, q_d_gray) {
    palette = share_draw_vtk__ints([3, 3, 3])
  } else if equal(palette, q_d_color) {
    palette = share_draw_vtk__ints([7, 5, 15])
  }
  let lutn = int(length(symval(q_ear_lookup_tables)) + 1)
  set(q_ear_lookup_tables, append(symval(q_ear_lookup_tables), list1(palette)))
  |> ignore
  let palette_name = format(Nil, "lut~a", [lutn])
  if listp(palette) &&
    length(palette) == 3 &&
    every(x => integerp(x) && num_le(num_abs(x), Fix(36L)), palette) {
    // build lookup table with transform functions; if
    // *unitscale-already-defined* is null, write the functions 'unitscale'
    // and 'interval'
    if symval(q_ear_unitscale_already_defined) is Nil {
      lut = share_draw_vtk__f("import math~%~%", []) +
        share_draw_vtk__f("def unitscale (k):~%", []) +
        share_draw_vtk__f("  return k/255.0~%~%", []) +
        share_draw_vtk__f("def interval (x,x0,x1):~%", []) +
        share_draw_vtk__f("  if x <= x0:~%", []) +
        share_draw_vtk__f("    return 0~%", []) +
        share_draw_vtk__f("  if x >= x1:~%", []) +
        share_draw_vtk__f("    return 1~%", []) +
        share_draw_vtk__f("  return x~%~%", [])
      set(q_ear_unitscale_already_defined, t) |> ignore
    }
    // write r-g-b transform functions
    lut = lut +
      lstring(color_transform_function(Str("R"), lutn, car(palette))) +
      lstring(color_transform_function(Str("G"), lutn, cadr(palette))) +
      lstring(color_transform_function(Str("B"), lutn, caddr(palette)))
    // create lookup table
    lut = lut +
      share_draw_vtk__f("~a=vtk.vtkLookupTable()~%", [palette_name]) +
      share_draw_vtk__f("~a.SetNumberOfColors(256)~%", [palette_name]) +
      share_draw_vtk__f("~a.Build()~%", [palette_name]) +
      share_draw_vtk__f("for i in range (0,256):~%", []) +
      share_draw_vtk__f("  ~a.SetTableValue(i,fR~a(i),fG~a(i),fB~a(i),1)~%~%", [
        palette_name, lutn, lutn, lutn,
      ])
    list2(palette_name, Str(lut))
  } else if listp(palette) &&
    every(x => listp(x) && length(x) == 3, palette) {
    // build user defined lookup table without transparency
    let n = length(palette)
    let s = StringBuilder::new()
    s.write_string(share_draw_vtk__f("~a=vtk.vtkLookupTable()~%", [palette_name]))
    s.write_string(
      share_draw_vtk__f("~a.SetNumberOfColors(~a)~%", [palette_name, int(n)]),
    )
    for k in 0..<n {
      let triplete = nth(k, palette)
      s.write_string(
        share_draw_vtk__f("~a.SetTableValue(~a,~a,~a,~a,1)~%", [
          palette_name,
          int(k),
          car(triplete),
          cadr(triplete),
          caddr(triplete),
        ]),
      )
    }
    list2(palette_name, Str(s.to_string()))
  } else if listp(palette) &&
    every(x => listp(x) && length(x) == 4, palette) {
    // build user defined lookup table with transparency
    let n = length(palette)
    let s = StringBuilder::new()
    s.write_string(share_draw_vtk__f("~a=vtk.vtkLookupTable()~%", [palette_name]))
    s.write_string(
      share_draw_vtk__f("~a.SetNumberOfColors(~a)~%", [palette_name, int(n)]),
    )
    for k in 0..<n {
      let triplete = nth(k, palette)
      s.write_string(
        share_draw_vtk__f("~a.SetTableValue(~a,~a,~a,~a,~a)~%", [
          palette_name,
          int(k),
          car(triplete),
          cadr(triplete),
          caddr(triplete),
          cadddr(triplete),
        ]),
      )
    }
    list2(palette_name, Str(s.to_string()))
  } else {
    Nil
  }
}

///|
fn build_surface_grid(nx : Value, ny : Value) -> Value raise {
  let nx = to_int(nx)
  let ny = to_int(ny)
  let mut poly : Value = Nil
  for f in 0..<(ny - 1) {
    let cont = f * nx
    for c in 0..<(nx - 1) {
      poly = cons(
        share_draw_vtk__ints([cont + c, cont + c + 1, cont + nx + c + 1, cont + nx + c]),
        poly,
      )
    }
  }
  reverse(poly)
}

// ---------------------------------------------------------------------------
// OBJECT BUILDERS

///|
/// Checks of a center/direction argument: a list of three floats.
fn share_draw_vtk__list3_floats(x : Value) -> Bool raise {
  d_listp(x).truthy() &&
  share_draw__mlength(x) == 3 &&
  every(z => floatp(z), rest(x))
}

///|
/// Checks of a length argument: a float greater than zero.
fn share_draw_vtk__positive_float(x : Value) -> Bool raise {
  floatp(x) && !num_le(x, Flo(0.0))
}

///|
/// 3d: cone(center, radius, height, direction)
fn vtk3d_cone(cen : Value, rad : Value, hei : Value, dir : Value) -> Value raise {
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let capping = rest(get_option(q_d_capping))
  let source_name = get_source_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let fcen = d_float(cen)
  let fhei = d_float(hei)
  let frad = d_float(rad)
  let fdir = d_float(dir)
  if !share_draw_vtk__list3_floats(fcen) {
    merr("draw3d: cone center must be a list of three numbers", []) |> ignore
  }
  if !share_draw_vtk__positive_float(frad) {
    merr("draw3d: cone radius must be a number greater than zero", []) |> ignore
  }
  if !share_draw_vtk__positive_float(fhei) {
    merr("draw3d: cone height must be a number greater than zero", []) |> ignore
  }
  if !share_draw_vtk__list3_floats(fdir) {
    merr("draw3d: cone direction must be a list of three numbers", []) |> ignore
  }
  let capn : Value = if first(capping).truthy() { Fix(1L) } else { Fix(0L) }
  let s = StringBuilder::new()
  s.write_string(share_draw_vtk__f("~a=vtk.vtkConeSource()~%", [source_name]))
  s.write_string(share_draw_vtk__f("~a.SetHeight(~a)~%", [source_name, fhei]))
  s.write_string(share_draw_vtk__f("~a.SetRadius(~a)~%", [source_name, frad]))
  s.write_string(
    share_draw_vtk__f("~a.SetCenter(~a,~a,~a)~%", [
      source_name,
      cadr(fcen),
      caddr(fcen),
      cadddr(fcen),
    ]),
  )
  s.write_string(
    share_draw_vtk__f("~a.SetDirection(~a,~a,~a)~%", [
      source_name,
      cadr(fdir),
      caddr(fdir),
      cadddr(fdir),
    ]),
  )
  s.write_string(share_draw_vtk__f("~a.SetResolution(~a)~%", [source_name, Fix(30L)]))
  s.write_string(share_draw_vtk__f("~a.SetCapping(~a)~%", [source_name, capn]))
  s.write_string(lstring(vtktransform_code(trans_name)))
  s.write_string(
    lstring(
      vtktransformpolydatafilter_code(filter_name, source_name, trans_name, Nil),
    ),
  )
  s.write_string(lstring(vtkpolydatamapper_code(mapper_name, filter_name, t)))
  s.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name]))
  s.write_string(
    lstring(
      vtkactor_code(actor_name, mapper_name, color, opacity, linewidth, wiredsurface),
    ),
  )
  s.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
    ]),
  )
  Str(s.to_string())
}

///|
/// Rotates point (x,y,z) rad radians around the line with unitary direction
/// vector (u,v,w) containing point (a,b,c).
fn rotate(
  x : Value,
  y : Value,
  z : Value,
  a : Value,
  b : Value,
  c : Value,
  u : Value,
  v : Value,
  w : Value,
  rad : Value,
) -> Value raise {
  let m1 : Value = Fix(-1L)
  let cl_cos = lcos(rad)
  let msin = () => share_draw_vtk__m(q_p_sin, rad)
  let mcos = () => share_draw_vtk__m(q_p_cos, rad)
  let sq = (q : Value) => expt(q, Fix(2L))
  let x1 = num_sum([
    num_mul(cl_cos, x),
    num_mul(
      msin(),
      num_sum([
        num_prod([m1, c, v]),
        num_mul(b, w),
        num_prod([m1, w, y]),
        num_mul(v, z),
      ]),
    ),
    num_mul(
      num_add(Fix(1L), num_mul(m1, mcos())),
      num_add(
        num_mul(a, num_add(sq(v), sq(w))),
        num_prod([
          m1,
          u,
          num_sum([
            num_mul(b, v),
            num_mul(c, w),
            num_prod([m1, u, x]),
            num_prod([m1, v, y]),
            num_prod([m1, w, z]),
          ]),
        ]),
      ),
    ),
  ])
  let y1 = num_sum([
    num_mul(mcos(), y),
    num_mul(
      msin(),
      num_sum([
        num_mul(c, u),
        num_prod([m1, a, w]),
        num_mul(w, x),
        num_prod([m1, u, z]),
      ]),
    ),
    num_mul(
      num_add(Fix(1L), num_mul(m1, mcos())),
      num_add(
        num_mul(b, num_add(sq(u), sq(w))),
        num_prod([
          m1,
          v,
          num_sum([
            num_mul(a, u),
            num_mul(c, w),
            num_prod([m1, u, x]),
            num_prod([m1, v, y]),
            num_prod([m1, w, z]),
          ]),
        ]),
      ),
    ),
  ])
  let z1 = num_sum([
    num_mul(
      msin(),
      num_sum([
        num_prod([m1, b, u]),
        num_mul(a, v),
        num_prod([m1, v, x]),
        num_mul(u, y),
      ]),
    ),
    num_mul(mcos(), z),
    num_mul(
      num_add(Fix(1L), num_mul(m1, mcos())),
      num_add(
        num_mul(c, num_add(sq(u), sq(v))),
        num_prod([
          m1,
          w,
          num_sum([
            num_mul(a, u),
            num_mul(b, v),
            num_prod([m1, u, x]),
            num_prod([m1, v, y]),
            num_prod([m1, w, z]),
          ]),
        ]),
      ),
    ),
  ])
  list([x1, y1, z1])
}

///|
/// 3d: prism(center, n, edgepoint, height, direction)
fn vtk3d_prism(
  cen : Value,
  n : Value,
  edgp : Value,
  hei : Value,
  dir : Value,
) -> Value raise {
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let capping = rest(get_option(q_d_capping))
  let source_name = get_source_name()
  let points_name = get_points_name()
  let cellarray_name = get_cellarray_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let str = StringBuilder::new()
  let fcen = d_float(cen)
  let fedgp = d_float(edgp)
  let fhei = d_float(hei)
  let fdir = d_float(dir)
  let ang = num_div(Flo(6.283185307179586), n) // = 2*%pi/n
  if !share_draw_vtk__list3_floats(fcen) {
    merr("draw3d: prism center must be a list of three numbers", []) |> ignore
  }
  if !share_draw_vtk__list3_floats(fedgp) {
    merr("draw3d: point on prism edge must be a list of three numbers", [])
    |> ignore
  }
  if !share_draw_vtk__positive_float(fhei) {
    merr("draw3d: prism height must be a number greater than zero", []) |> ignore
  }
  if !share_draw_vtk__list3_floats(fdir) {
    merr("draw3d: cylinder direction must be a list of three numbers", [])
    |> ignore
  }
  // direction vector with module = height/2
  let c1 = cadr(fcen)
  let c2 = caddr(fcen)
  let c3 = cadddr(fcen)
  let p1 = cadr(fedgp)
  let p2 = caddr(fedgp)
  let p3 = cadddr(fedgp)
  let mut d1 = cadr(fdir)
  let mut d2 = caddr(fdir)
  let mut d3 = cadddr(fdir)
  let mut dirmod = lsqrt(
    num_sum([num_mul(d1, d1), num_mul(d2, d2), num_mul(d3, d3)]),
  )
  if num_eq(dirmod, Flo(0.0)) {
    d1 = Fix(0L)
    d2 = Fix(0L)
    d3 = Fix(1L)
    dirmod = Fix(1L)
  }
  let two_dirmod = num_mul(Fix(2L), dirmod)
  let du1 = num_div(num_mul(d1, fhei), two_dirmod)
  let du2 = num_div(num_mul(d2, fhei), two_dirmod)
  let du3 = num_div(num_mul(d3, fhei), two_dirmod)
  // intersection between edge and perpendicular plane passing through
  // center
  let m1 : Value = Fix(-1L)
  let den = num_mul(dirmod, dirmod)
  let v1 = num_div(
    num_sum([
      num_prod([c1, d1, d1]),
      num_prod([c2, d1, d2]),
      num_prod([c3, d1, d3]),
      num_prod([d2, d2, p1]),
      num_prod([d3, d3, p1]),
      num_prod([m1, d1, d2, p2]),
      num_prod([m1, d1, d3, p3]),
    ]),
    den,
  )
  let v2 = num_div(
    num_sum([
      num_prod([c1, d1, d2]),
      num_prod([c2, d2, d2]),
      num_prod([c3, d2, d3]),
      num_prod([m1, d1, d2, p1]),
      num_prod([d1, d1, p2]),
      num_prod([d3, d3, p2]),
      num_prod([m1, d2, d3, p3]),
    ]),
    den,
  )
  let v3 = num_div(
    num_sum([
      num_prod([c1, d1, d3]),
      num_prod([c2, d2, d3]),
      num_prod([c3, d3, d3]),
      num_prod([m1, d1, d3, p1]),
      num_prod([m1, d2, d3, p2]),
      num_prod([d1, d1, p3]),
      num_prod([d2, d2, p3]),
    ]),
    den,
  )
  // rotate n times 2 pi/n and save the vertices of the lateral rectangles
  let ncap = share_draw_vtk__count_t(capping)
  let ni = to_int(n)
  let size = (2 + ncap) * (ni + 1)
  let x = make_array([size], elt="flonum")
  let y = make_array([size], elt="flonum")
  let z = make_array([size], elt="flonum")
  let mut cnt = -1
  let put = (xv : Value, yv : Value, zv : Value) => {
    cnt = cnt + 1
    aset1(x, cnt, xv) |> ignore
    aset1(y, cnt, yv) |> ignore
    aset1(z, cnt, zv) |> ignore
  }
  for s in 0..=ni {
    // bottom capping?
    if equal(second(capping), t) {
      put(num_sub(c1, du1), num_sub(c2, du2), num_sub(c3, du3))
    }
    let v = rotate(
      v1,
      v2,
      v3,
      c1,
      c2,
      c3,
      num_div(d1, dirmod),
      num_div(d2, dirmod),
      num_div(d3, dirmod),
      num_mul(int(s), ang),
    )
    put(num_sub(first(v), du1), num_sub(second(v), du2), num_sub(third(v), du3))
    put(num_add(first(v), du1), num_add(second(v), du2), num_add(third(v), du3))
    // top capping?
    if equal(first(capping), t) {
      put(num_add(c1, du1), num_add(c2, du2), num_add(c3, du3))
    }
  }
  // python code
  str.write_string(share_draw_vtk__f("~a=vtk.vtkPolyData()~%", [source_name]))
  str.write_string(
    share_draw_vtk__f("~a~%", [vtkpoints_code(points_name, source_name, x, y, z)]),
  )
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkcellarray_code(
        cellarray_name,
        source_name,
        Fix(2L),
        build_surface_grid(int(2 + ncap), int(ni + 1)),
      ),
    ]),
  )
  str.write_string(share_draw_vtk__f("~a~%", [vtktransform_code(trans_name)]))
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtktransformpolydatafilter_code(filter_name, source_name, trans_name, t),
    ]),
  )
  str.write_string(
    share_draw_vtk__f("~a~%", [vtkpolydatamapper_code(mapper_name, filter_name, t)]),
  )
  str.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name]))
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkactor_code(actor_name, mapper_name, color, opacity, linewidth, wiredsurface),
    ]),
  )
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
    ]),
  )
  Str(str.to_string())
}

///|
/// 3d: cylinder(center, radius, height, direction)
fn vtk3d_cylinder(
  cen : Value,
  rad : Value,
  hei : Value,
  dir : Value,
) -> Value raise {
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let capping = rest(get_option(q_d_capping))
  let source_name = get_source_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let fcen = d_float(cen)
  let frad = d_float(rad)
  let fhei = d_float(hei)
  let fdir = d_float(dir)
  if !share_draw_vtk__list3_floats(fcen) {
    merr("draw3d: cylinder center must be a list of three numbers", []) |> ignore
  }
  if !share_draw_vtk__positive_float(fhei) {
    merr("draw3d: cylinder height must be a number greater than zero", [])
    |> ignore
  }
  if !share_draw_vtk__positive_float(frad) {
    merr("draw3d: cylinder radius must be a number greater than zero", [])
    |> ignore
  }
  if !share_draw_vtk__list3_floats(fdir) {
    merr("draw3d: cylinder direction must be a list of three numbers", [])
    |> ignore
  }
  let capn : Value = if first(capping).truthy() { Fix(1L) } else { Fix(0L) }
  let a = cadr(fdir)
  let b = caddr(fdir)
  let c = cadddr(fdir)
  let dirmod = lsqrt(num_sum([num_mul(a, a), num_mul(b, b), num_mul(c, c)]))
  let r2d : Value = Flo(57.29577951308232)
  let (xrot, yrot, zrot) : (Value, Value, Value) = if num_eq(dirmod, Flo(0.0)) {
    // we use the same default direction used by cones, which is the
    // positive X-direction
    (Flo(0.0), Flo(0.0), Flo(-90.0))
  } else if num_eq(b, Flo(0.0)) {
    (
      Flo(90.0),
      num_mul(
        r2d,
        share_draw_vtk__m(
          q_p_acos,
          num_div(c, lsqrt(num_add(num_mul(a, a), num_mul(c, c)))),
        ),
      ),
      Flo(0.0),
    )
  } else if num_lt(b, Flo(0.0)) {
    (
      num_mul(r2d, share_draw_vtk__m(q_p_asin, num_div(c, dirmod))),
      Flo(0.0),
      num_mul(
        r2d,
        num_add(
          Flo(-3.141592653589793),
          num_neg(share_draw_vtk__m(q_p_atan, num_div(a, b))),
        ),
      ),
    )
  } else {
    (
      num_mul(r2d, share_draw_vtk__m(q_p_asin, num_div(c, dirmod))),
      Flo(0.0),
      num_mul(r2d, num_neg(share_draw_vtk__m(q_p_atan, num_div(a, b)))),
    )
  }
  // python code
  let s = StringBuilder::new()
  s.write_string(share_draw_vtk__f("~a=vtk.vtkCylinderSource()~%", [source_name]))
  s.write_string(share_draw_vtk__f("~a.SetHeight(~a)~%", [source_name, fhei]))
  s.write_string(share_draw_vtk__f("~a.SetRadius(~a)~%", [source_name, frad]))
  s.write_string(share_draw_vtk__f("~a.SetResolution(~a)~%", [source_name, Fix(30L)]))
  s.write_string(share_draw_vtk__f("~a.SetCapping(~a)~%", [source_name, capn]))
  s.write_string(lstring(vtktransform_code(trans_name)))
  s.write_string(
    share_draw_vtk__f("~a.Translate(~a,~a,~a)~%", [
      trans_name,
      cadr(fcen),
      caddr(fcen),
      cadddr(fcen),
    ]),
  )
  // rotations are made in reverse order as indicated here
  s.write_string(share_draw_vtk__f("~a.RotateZ(~a)~%", [trans_name, zrot])) // azimuth
  s.write_string(share_draw_vtk__f("~a.RotateY(~a)~%", [trans_name, yrot]))
  s.write_string(share_draw_vtk__f("~a.RotateX(~a)~%", [trans_name, xrot])) // elevation
  s.write_string(
    lstring(
      vtktransformpolydatafilter_code(filter_name, source_name, trans_name, Nil),
    ),
  )
  s.write_string(lstring(vtkpolydatamapper_code(mapper_name, filter_name, t)))
  s.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name]))
  s.write_string(
    lstring(
      vtkactor_code(actor_name, mapper_name, color, opacity, linewidth, wiredsurface),
    ),
  )
  s.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
    ]),
  )
  Str(s.to_string())
}

///|
/// 3d: cube(xlength, ylength, zlength, center)
fn vtk3d_cube(
  xlen : Value,
  ylen : Value,
  zlen : Value,
  cen : Value,
) -> Value raise {
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let source_name = get_source_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let fxlen = d_float(xlen)
  let fylen = d_float(ylen)
  let fzlen = d_float(zlen)
  let fcen = d_float(cen)
  if !share_draw_vtk__positive_float(fxlen) {
    merr("draw3d: cube x-length must be a number greater than zero", [])
    |> ignore
  }
  if !share_draw_vtk__positive_float(fylen) {
    merr("draw3d: cube y-length must be a number greater than zero", [])
    |> ignore
  }
  if !share_draw_vtk__positive_float(fzlen) {
    merr("draw3d: cube z-length must be a number greater than zero", [])
    |> ignore
  }
  if !share_draw_vtk__list3_floats(fcen) {
    merr("draw3d: cube center must be a list of three floats", []) |> ignore
  }
  let s = StringBuilder::new()
  s.write_string(share_draw_vtk__f("~a=vtk.vtkCubeSource()~%", [source_name]))
  s.write_string(share_draw_vtk__f("~a.SetXLength(~a)~%", [source_name, fxlen]))
  s.write_string(share_draw_vtk__f("~a.SetYLength(~a)~%", [source_name, fylen]))
  s.write_string(share_draw_vtk__f("~a.SetZLength(~a)~%", [source_name, fzlen]))
  s.write_string(
    share_draw_vtk__f("~a.SetCenter(~a,~a,~a)~%", [
      source_name,
      cadr(fcen),
      caddr(fcen),
      cadddr(fcen),
    ]),
  )
  s.write_string(lstring(vtktransform_code(trans_name)))
  s.write_string(
    lstring(
      vtktransformpolydatafilter_code(filter_name, source_name, trans_name, Nil),
    ),
  )
  s.write_string(lstring(vtkpolydatamapper_code(mapper_name, filter_name, t)))
  s.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name]))
  s.write_string(
    lstring(
      vtkactor_code(actor_name, mapper_name, color, opacity, linewidth, wiredsurface),
    ),
  )
  s.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
    ]),
  )
  Str(s.to_string())
}

///|
/// 3d: sphere(center, radius)
fn vtk3d_sphere(cen : Value, rad : Value) -> Value raise {
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let source_name = get_source_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let frad = d_float(rad)
  let fcen = d_float(cen)
  if !share_draw_vtk__list3_floats(fcen) {
    merr("draw3d: sphere center must be a list of three numbers", []) |> ignore
  }
  if !share_draw_vtk__positive_float(frad) {
    merr("draw3d: sphere radius must be a number greater than zero", [])
    |> ignore
  }
  let s = StringBuilder::new()
  s.write_string(share_draw_vtk__f("~a=vtk.vtkSphereSource()~%", [source_name]))
  s.write_string(share_draw_vtk__f("~a.SetRadius(~a)~%", [source_name, frad]))
  s.write_string(
    share_draw_vtk__f("~a.SetCenter(~a,~a,~a)~%", [
      source_name,
      cadr(fcen),
      caddr(fcen),
      cadddr(fcen),
    ]),
  )
  s.write_string(
    share_draw_vtk__f("~a.SetThetaResolution(~a)~%", [source_name, Fix(30L)]),
  )
  s.write_string(
    share_draw_vtk__f("~a.SetPhiResolution(~a)~%", [source_name, Fix(30L)]),
  )
  s.write_string(lstring(vtktransform_code(trans_name)))
  s.write_string(
    lstring(
      vtktransformpolydatafilter_code(filter_name, source_name, trans_name, Nil),
    ),
  )
  s.write_string(lstring(vtkpolydatamapper_code(mapper_name, filter_name, t)))
  s.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name]))
  s.write_string(
    lstring(
      vtkactor_code(actor_name, mapper_name, color, opacity, linewidth, wiredsurface),
    ),
  )
  s.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
    ]),
  )
  Str(s.to_string())
}

///|
/// 3d: parallelogram(origin, point1, point2). The parallelogram is defined
/// by one vertex and the two other adjacent vertices.
fn vtk3d_parallelogram(ori : Value, p1 : Value, p2 : Value) -> Value raise {
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let source_name = get_source_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let str = StringBuilder::new()
  let fori = share_draw__float_list(rest(ori))
  let fp1 = share_draw__float_list(rest(p1))
  let fp2 = share_draw__float_list(rest(p2))
  if !every(z => floatp(z), append(fori, append(fp1, fp2))) {
    merr("vtk3d: arguments to parallelogram must be lists of floats", [])
    |> ignore
  }
  // python code
  str.write_string(share_draw_vtk__f("~a=vtk.vtkPlaneSource()~%", [source_name]))
  let (xx, yy, zz) = share_draw__transform_point3(
    car(fori),
    cadr(fori),
    caddr(fori),
  )
  let a1 = xx
  let b1 = yy
  let c1 = zz
  str.write_string(
    share_draw_vtk__f("~a.SetOrigin(~a,~a,~a)~%", [source_name, xx, yy, zz]),
  )
  let (xx, yy, zz) = share_draw__transform_point3(car(fp1), cadr(fp1), caddr(fp1))
  if num_eq(a1, xx) && num_eq(b1, yy) && num_eq(c1, zz) {
    merr("vtk3d (parallelogram): three distinct vertices are needed.", [])
    |> ignore
  }
  let a2 = xx
  let b2 = yy
  let c2 = zz
  str.write_string(
    share_draw_vtk__f("~a.SetPoint1(~a,~a,~a)~%", [source_name, xx, yy, zz]),
  )
  let (xx, yy, zz) = share_draw__transform_point3(car(fp2), cadr(fp2), caddr(fp2))
  if (num_eq(a1, xx) && num_eq(b1, yy) && num_eq(c1, zz)) ||
    (num_eq(a2, xx) && num_eq(b2, yy) && num_eq(c2, zz)) {
    merr(
      "vtk3d: we need three distinct vertices to draw a parallelogram.",
      [],
    )
    |> ignore
  }
  str.write_string(
    share_draw_vtk__f("~a.SetPoint2(~a,~a,~a)~%", [source_name, xx, yy, zz]),
  )
  // (format nil "~a.SetXResolution(~a)~%" ...) in the Lisp code: computed
  // and discarded, so not written to the script.
  str.write_string(
    share_draw_vtk__f("~a.SetYResolution(~a)~%", [source_name, Fix(10L)]),
  )
  str.write_string(lstring(vtktransform_code(trans_name)))
  str.write_string(
    lstring(
      vtktransformpolydatafilter_code(filter_name, source_name, trans_name, Nil),
    ),
  )
  str.write_string(lstring(vtkpolydatamapper_code(mapper_name, filter_name, t)))
  str.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name]))
  str.write_string(
    lstring(
      vtkactor_code(actor_name, mapper_name, color, opacity, linewidth, wiredsurface),
    ),
  )
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
    ]),
  )
  Str(str.to_string())
}

///|
/// 3d: triangle(vertex1, vertex2, vertex3)
fn vtk3d_triangle(v1 : Value, v2 : Value, v3 : Value) -> Value raise {
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let points_name = get_points_name()
  let triangle_name = get_triangle_name()
  let polydata_name = get_polydata_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let str = StringBuilder::new()
  let fv1 = share_draw__float_list(rest(v1))
  let fv2 = share_draw__float_list(rest(v2))
  let fv3 = share_draw__float_list(rest(v3))
  if !every(z => floatp(z), append(fv1, append(fv2, fv3))) {
    merr("vtk3d (triangle): arguments must be lists of three numbers", [])
    |> ignore
  }
  // python code
  str.write_string(share_draw_vtk__f("~a=vtk.vtkPoints()~%", [points_name]))
  str.write_string(share_draw_vtk__f("~a.SetNumberOfPoints(3)~%", [points_name]))
  let fvs = [fv1, fv2, fv3]
  for i in 0..<3 {
    let fv = fvs[i]
    let (xx, yy, zz) = share_draw__transform_point3(car(fv), cadr(fv), caddr(fv))
    str.write_string(
      share_draw_vtk__f("~a.InsertPoint(~a,~a,~a,~a)~%", [
        points_name,
        int(i),
        xx,
        yy,
        zz,
      ]),
    )
  }
  str.write_string(share_draw_vtk__f("~a=vtk.vtkTriangle()~%", [triangle_name]))
  str.write_string(
    share_draw_vtk__f("~a.GetPointIds().SetId(0,0)~%", [triangle_name]),
  )
  str.write_string(
    share_draw_vtk__f("~a.GetPointIds().SetId(1,1)~%", [triangle_name]),
  )
  str.write_string(
    share_draw_vtk__f("~a.GetPointIds().SetId(2,2)~%", [triangle_name]),
  )
  str.write_string(share_draw_vtk__f("~a=vtk.vtkPolyData()~%", [polydata_name]))
  str.write_string(share_draw_vtk__f("~a.Allocate(1,1)~%", [polydata_name]))
  str.write_string(
    share_draw_vtk__f("~a.InsertNextCell(~a.GetCellType(),~a.GetPointIds())~%", [
      polydata_name, triangle_name, triangle_name,
    ]),
  )
  str.write_string(
    share_draw_vtk__f("~a.SetPoints(~a)~%", [polydata_name, points_name]),
  )
  str.write_string(lstring(vtktransform_code(trans_name)))
  str.write_string(
    lstring(
      vtktransformpolydatafilter_code(filter_name, polydata_name, trans_name, t),
    ),
  )
  str.write_string(share_draw_vtk__f("~a=vtk.vtkPolyDataMapper()~%", [mapper_name]))
  str.write_string(
    share_draw_vtk__f("~a.SetInputData(~a)~%", [mapper_name, polydata_name]),
  )
  str.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name]))
  str.write_string(
    lstring(
      vtkactor_code(actor_name, mapper_name, color, opacity, linewidth, wiredsurface),
    ),
  )
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
    ]),
  )
  Str(str.to_string())
}

///|
/// 3d: vector([x,y,z], [dx,dy,dz])
fn vtk3d_vector(arg1 : Value, arg2 : Value) -> Value raise {
  if !d_listp(arg1).truthy() ||
    share_draw__mlength(arg1) != 3 ||
    !d_listp(arg2).truthy() ||
    share_draw__mlength(arg2) != 3 {
    merr("vtk3d (vector): coordinates are not correct", []) |> ignore
  }
  let color = get_option(q_d_color)
  let head_length = get_option(q_d_head_length)
  let head_angle = get_option(q_d_head_angle)
  let line_width = get_option(q_d_line_width)
  let unit_vectors = get_option(q_d_unit_vectors)
  let opacity = get_option(q_d_opacity)
  let wiredsurface = get_option(q_d_wired_surface)
  let source_name = get_source_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let x = d_float(cadr(arg1))
  let y = d_float(caddr(arg1))
  let z = d_float(cadddr(arg1))
  let dx = d_float(cadr(arg2))
  let dy = d_float(caddr(arg2))
  let dz = d_float(cadddr(arg2))
  // unitary vector
  let mut module_ = lsqrt(
    num_sum([num_mul(dx, dx), num_mul(dy, dy), num_mul(dz, dz)]),
  )
  let ndx = num_div(dx, module_)
  let mut ndy = num_div(dy, module_)
  let mut ndz = num_div(dz, module_)
  // transform into unitary vector when unit_vectors=true
  if unit_vectors.truthy() {
    module_ = Fix(1L)
  }
  // head parameters
  let radians = num_mul(head_angle, Flo(0.0174532925199433))
  let tiplength = num_mul(
    head_length,
    d_float(share_draw_vtk__m(q_p_cos, radians)),
  )
  let radius = num_mul(head_length, d_float(share_draw_vtk__m(q_p_sin, radians)))
  // rotation angle
  let mut rotangle = num_mul(
    Flo(57.29577951308232),
    d_float(
      share_draw_vtk__m(
        q_p_asin,
        lsqrt(num_add(num_mul(ndz, ndz), num_mul(ndy, ndy))),
      ),
    ),
  )
  // check if rotation angle is obtuse
  if num_lt(ndx, Fix(0L)) {
    rotangle = num_sub(Flo(180.0), rotangle)
  }
  if num_eq(ndz, Flo(0.0)) && num_eq(ndy, Flo(0.0)) {
    ndy = Flo(0.0)
    ndz = Flo(-1.0)
  }
  let s = StringBuilder::new()
  s.write_string(share_draw_vtk__f("~a=vtk.vtkArrowSource()~%", [source_name]))
  s.write_string(
    share_draw_vtk__f("~a.SetTipResolution(~a)~%", [source_name, Fix(20L)]),
  )
  s.write_string(
    share_draw_vtk__f("~a.SetTipRadius(~a)~%", [
      source_name,
      num_div(radius, module_),
    ]),
  )
  s.write_string(
    share_draw_vtk__f("~a.SetTipLength(~a)~%", [
      source_name,
      num_div(tiplength, module_),
    ]),
  )
  s.write_string(
    share_draw_vtk__f("~a.SetShaftResolution(~a)~%", [source_name, Fix(10L)]),
  )
  s.write_string(
    share_draw_vtk__f("~a.SetShaftRadius(~a)~%", [
      source_name,
      num_div(line_width, module_),
    ]),
  )
  s.write_string(lstring(vtktransform_code(trans_name)))
  s.write_string(
    share_draw_vtk__f("~a.Translate(~a,~a,~a)~%", [trans_name, x, y, z]),
  )
  s.write_string(
    share_draw_vtk__f("~a.RotateWXYZ(~a,~a,~a,~a)~%", [
      trans_name,
      rotangle,
      Fix(0L),
      num_neg(ndz),
      ndy,
    ]),
  )
  s.write_string(
    share_draw_vtk__f("~a.Scale(~a,~a,~a)~%", [trans_name, module_, module_, module_]),
  )
  s.write_string(
    lstring(vtktransformfilter_code(filter_name, source_name, trans_name)),
  )
  s.write_string(lstring(vtkpolydatamapper_code(mapper_name, filter_name, t)))
  s.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name]))
  s.write_string(
    lstring(
      vtkactor_code(actor_name, mapper_name, color, opacity, line_width, wiredsurface),
    ),
  )
  s.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
    ]),
  )
  Str(s.to_string())
}

///|
/// A transform filter plus mapper, through a tube filter when the line
/// type is a tube (negative).
fn share_draw_vtk__line_filter(
  line_type : Value,
  source_name : Value,
  trans_name : Value,
  filter_name : Value,
  mapper_name : Value,
) -> String raise {
  if num_lt(line_type, Fix(0L)) {
    // line type is a tube
    lstring(
      vtktransformpolydatafilter_code(Str("auxfiltertube"), source_name, trans_name, t),
    ) +
    lstring(vtktubefilter_code(filter_name, Str("auxfiltertube"), line_type)) +
    lstring(vtkpolydatamapper_code(mapper_name, filter_name, t))
  } else {
    lstring(
      vtktransformpolydatafilter_code(filter_name, source_name, trans_name, t),
    ) +
    lstring(vtkpolydatamapper_code(mapper_name, filter_name, t))
  }
}

