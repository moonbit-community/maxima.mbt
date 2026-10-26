// Port of share/draw/vtk.lisp, part 2: the points, parametric, surface,
// label and tube objects, the scene builders and draw_vtk.

///|
/// 3D: points([[x1,y1,z1], [x2,y2,z2], [x3,y3,z3],...])
fn vtk3d_points(arg : Value) -> Value raise {
  let points_joined = get_option(q_d_points_joined)
  let point_type = get_option(q_d_point_type)
  let point_size = d_float(get_option(q_d_point_size))
  let line_type = get_option(q_d_line_type)
  let mut color = get_option(q_d_color)
  let mut opacity = get_option(q_d_opacity)
  let mut linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let source_name = get_source_name()
  let points_name = get_points_name()
  let floatarray_name = get_floatarray_name()
  let tmp = mapcar(z => rest(z), rest(arg))
  let mut output_string = ""
  let mut minscalar : Value = Flo(1.7976931348623157e308)
  let mut maxscalar : Value = Flo(-1.7976931348623157e308)
  let mut lookup_table_name : Value = Nil
  let mut scalars : Value = Nil
  let n = to_int(d_length(arg))
  // create array of points
  let x = share_draw__float_list(mapcar(z => first(z), tmp))
  let y = share_draw__float_list(mapcar(z => second(z), tmp))
  let z = share_draw__float_list(mapcar(z => third(z), tmp))
  let (x, y, z) = share_draw__transform_lists3(x, y, z)
  let ax = vector(list_to_array(x))
  let ay = vector(list_to_array(y))
  let az = vector(list_to_array(z))
  // check enhanced3d model
  check_enhanced3d_model(Str("points"), share_draw_vtk__ints([0, 1, 3])) |> ignore
  if share_draw_vtk__e3d() > 0 {
    scalars = make_array([n], elt="flonum")
    if share_draw_vtk__e3d() == 1 {
      for k in 0..<n {
        let newscalar = share_draw_vtk__e3d_fun([int(k)])
        if num_lt(newscalar, minscalar) {
          minscalar = newscalar
        }
        if num_gt(newscalar, maxscalar) {
          maxscalar = newscalar
        }
        aset1(scalars, k, newscalar) |> ignore
      }
    } else if share_draw_vtk__e3d() == 3 {
      for k in 0..<n {
        let newscalar = share_draw_vtk__e3d_fun([
          aref1(ax, k),
          aref1(ay, k),
          aref1(az, k),
        ])
        if num_lt(newscalar, minscalar) {
          minscalar = newscalar
        }
        if num_gt(newscalar, maxscalar) {
          maxscalar = newscalar
        }
        aset1(scalars, k, newscalar) |> ignore
      }
    }
    let slope = if num_lt(minscalar, maxscalar) {
      num_div(Flo(1.0), num_sub(maxscalar, minscalar))
    } else {
      Flo(0.0)
    }
    // rescale array of scalars to interval [0,1]
    for s in 0..<length(scalars) {
      aset1(scalars, s, num_mul(slope, num_sub(aref1(scalars, s), minscalar)))
      |> ignore
    }
    let lut = check_lookup_table()
    lookup_table_name = car(lut)
    output_string = lstring(cadr(lut))
  }
  // python code
  output_string = output_string +
    share_draw_vtk__f("~a=vtk.vtkPolyData()~%", [source_name]) +
    lstring(vtkpoints_code(points_name, source_name, ax, ay, az))
  if share_draw_vtk__e3d() > 0 {
    output_string = output_string +
      lstring(vtkfloatarray_code(floatarray_name, source_name, scalars, addarr=Nil))
  }
  if points_joined.truthy() {
    // true or impulses
    let trans_name = get_trans_name()
    let filter_name = get_filter_name()
    let mapper_name = get_mapper_name()
    get_polydata_name() |> ignore
    let cellarray_name = get_cellarray_name()
    let actor_name = get_actor_name()
    output_string = output_string +
      (if eql(points_joined, q_d_impulses) {
        let source_name2 = get_source_name()
        let points_name2 = get_points_name()
        let cellarray_name2 = get_cellarray_name()
        let s1 = share_draw_vtk__f("~a=vtk.vtkPolyData()~%", [source_name2])
        let xx = make_array([2 * n], elt="flonum")
        let yy = make_array([2 * n], elt="flonum")
        let zz = make_array([2 * n], elt="flonum")
        let mut ind = 0
        for k in 0..<n {
          aset1(xx, ind, aref1(ax, k)) |> ignore
          aset1(yy, ind, aref1(ay, k)) |> ignore
          aset1(zz, ind, Flo(0.0)) |> ignore
          ind = ind + 1
          aset1(xx, ind, aref1(ax, k)) |> ignore
          aset1(yy, ind, aref1(ay, k)) |> ignore
          aset1(zz, ind, aref1(az, k)) |> ignore
          ind = ind + 1
        }
        let s2 = lstring(vtkpoints_code(points_name2, source_name2, xx, yy, zz))
        let cells = Collector::new()
        for k in 0..<n {
          cells.add(share_draw_vtk__ints([2 * k, 2 * k + 1]))
        }
        let s3 = lstring(
          vtkcellarray_code(cellarray_name2, source_name2, Fix(1L), cells.result()),
        )
        let s4 = lstring(vtktransform_code(trans_name))
        s1 +
        s2 +
        s3 +
        s4 +
        share_draw_vtk__line_filter(
          line_type, source_name2, trans_name, filter_name, mapper_name,
        )
      } else {
        let idx = Collector::new()
        for k in 0..<n {
          idx.add(int(k))
        }
        let s1 = lstring(
          vtkcellarray_code(cellarray_name, source_name, Fix(1L), list1(idx.result())),
        )
        let s2 = lstring(vtktransform_code(trans_name))
        s1 +
        s2 +
        share_draw_vtk__line_filter(
          line_type, source_name, trans_name, filter_name, mapper_name,
        )
      })
    output_string = output_string +
      (if share_draw_vtk__e3d() > 0 {
        share_draw_vtk__f("~a.SetLookupTable(~a)~%", [mapper_name, lookup_table_name])
      } else {
        ""
      })
    output_string = output_string +
      share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name])
    output_string = output_string +
      share_draw_vtk__f("~a~%", [
        vtkactor_code(actor_name, Nil, color, opacity, linewidth, wiredsurface),
      ])
    output_string = output_string +
      share_draw_vtk__f("~a~%", [
        vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
      ])
    output_string = output_string +
      (if num_ge(line_type, Fix(0L)) {
        // when line type is not a tube, set line pattern
        share_draw_vtk__f("~a.GetProperty().SetLineStipplePattern(~a)~%~%", [
          actor_name,
          share_draw_vtk__stipple(line_type),
        ])
      } else {
        ""
      })
  }
  // draw glyphs according to point-type
  if num_ge(point_type, Fix(0L)) && num_le(point_type, Fix(5L)) {
    let glyphpoints_name = get_glyphpoints_name()
    let polydata_name = get_polydata_name()
    let cellarray_name = get_cellarray_name()
    let filter_name = get_filter_name()
    let mapper_name = get_mapper_name()
    let actor_name = get_actor_name()
    color = get_option(q_d_color)
    opacity = get_option(q_d_opacity)
    linewidth = get_option(q_d_line_width)
    let ps = point_size
    let mps = num_neg(point_size)
    let o : Value = Flo(0.0)
    let pt = to_int(point_type)
    let pts = match pt {
      0 =>
        vtkpoints_code(
          glyphpoints_name,
          Nil,
          vector([Flo(0.0)]),
          vector([Flo(0.0)]),
          vector([Flo(0.0)]),
        )
      1 =>
        vtkpoints_code(
          glyphpoints_name,
          Nil,
          vector([mps, ps, o, o]),
          vector([o, o, o, o]),
          vector([o, o, mps, ps]),
        )
      2 =>
        vtkpoints_code(
          glyphpoints_name,
          Nil,
          vector([ps, mps, mps, ps]),
          vector([o, o, o, o]),
          vector([ps, mps, ps, mps]),
        )
      3 =>
        vtkpoints_code(
          glyphpoints_name,
          Nil,
          vector([ps, mps, mps, ps, mps, ps, o, o]),
          vector([o, o, o, o, o, o, o, o]),
          vector([ps, mps, ps, mps, o, o, mps, ps]),
        )
      4 =>
        vtkpoints_code(
          glyphpoints_name,
          Nil,
          vector([ps, mps, mps, ps]),
          vector([o, o, o, o]),
          vector([ps, ps, mps, mps]),
        )
      _ =>
        vtkpoints_code(
          glyphpoints_name,
          Nil,
          vector([mps, ps, ps, mps]),
          vector([o, o, o, o]),
          vector([ps, ps, mps, mps]),
        )
    }
    output_string = output_string + lstring(pts)
    output_string = output_string +
      share_draw_vtk__f("~a=vtk.vtkPolyData()~%", [polydata_name])
    output_string = output_string +
      share_draw_vtk__f("~a.SetPoints(~a)~%", [polydata_name, glyphpoints_name])
    let ints2 = (cells : Array[Array[Int]]) => list(
      cells.map(c => share_draw_vtk__ints(c)),
    )
    output_string = output_string +
      (match pt {
        0 =>
          lstring(
            vtkcellarray_code(cellarray_name, polydata_name, Fix(0L), ints2([[0]])),
          )
        1 | 2 =>
          lstring(
            vtkcellarray_code(
              cellarray_name,
              polydata_name,
              Fix(1L),
              ints2([[0, 1], [2, 3]]),
            ),
          )
        3 =>
          lstring(
            vtkcellarray_code(
              cellarray_name,
              polydata_name,
              Fix(1L),
              ints2([[0, 1], [2, 3], [4, 5], [6, 7]]),
            ),
          )
        4 =>
          lstring(
            vtkcellarray_code(
              cellarray_name,
              polydata_name,
              Fix(1L),
              ints2([[0, 1], [1, 2], [2, 3], [3, 0]]),
            ),
          )
        5 =>
          lstring(
            vtkcellarray_code(
              cellarray_name,
              polydata_name,
              Fix(2L),
              ints2([[0, 1, 2, 3]]),
            ),
          )
        _ => ""
      })
    output_string = output_string +
      lstring(
        vtkglyph3d_code(
          filter_name,
          source_name,
          format(Nil, "SetSourceData(~a)", [polydata_name]),
        ),
      )
    output_string = output_string +
      share_draw_vtk__f("~a~%", [vtkpolydatamapper_code(mapper_name, filter_name, t)])
    output_string = output_string +
      (if share_draw_vtk__e3d() > 0 {
        share_draw_vtk__f("~a.SetLookupTable(~a)~%", [mapper_name, lookup_table_name])
      } else {
        ""
      })
    output_string = output_string +
      share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name])
    output_string = output_string +
      share_draw_vtk__f("~a~%", [
        vtkactor_code(actor_name, Nil, color, opacity, linewidth, Nil),
      ])
    output_string = output_string +
      share_draw_vtk__f("~a~%", [
        vtkextractpolydatageometry_code(get_extract_name(), t, t),
      ])
    Str(output_string)
  } else if num_ge(point_type, Fix(14L)) && num_le(point_type, Fix(17L)) {
    let solidsource_name = get_solidsource_name()
    let filter_name = get_filter_name()
    let mapper_name = get_mapper_name()
    let actor_name = get_actor_name()
    color = get_option(q_d_color)
    opacity = get_option(q_d_opacity)
    let half = num_div(point_size, Flo(2.0))
    output_string = output_string +
      (match to_int(point_type) {
        14 =>
          // sphere glyph
          share_draw_vtk__f("~a=vtk.vtkSphereSource()~%~a.SetRadius(~a)~%", [
            solidsource_name, solidsource_name, half,
          ])
        15 =>
          // cube glyph
          share_draw_vtk__f(
            "~a=vtk.vtkCubeSource()~%~a.SetXLength(~a)~%~a.SetYLength(~a)~%~a.SetZLength(~a)~%",
            [
              solidsource_name, solidsource_name, point_size, solidsource_name, point_size,
              solidsource_name, point_size,
            ],
          )
        16 =>
          // cylinder glyph
          share_draw_vtk__f(
            "~a=vtk.vtkCylinderSource()~%~a.SetRadius(~a)~%~a.SetHeight(~a)~%",
            [solidsource_name, solidsource_name, half, solidsource_name, point_size],
          )
        _ =>
          // cone glyph
          share_draw_vtk__f(
            "~a=vtk.vtkConeSource()~%~a.SetRadius(~a)~%~a.SetHeight(~a)~%",
            [solidsource_name, solidsource_name, half, solidsource_name, point_size],
          )
      })
    output_string = output_string +
      lstring(
        vtkglyph3d_code(
          filter_name,
          source_name,
          format(Nil, "SetSourceConnection(~a.GetOutputPort())", [solidsource_name]),
        ),
      )
    output_string = output_string +
      share_draw_vtk__f("~a~%", [vtkpolydatamapper_code(mapper_name, filter_name, t)])
    output_string = output_string +
      (if share_draw_vtk__e3d() > 0 {
        share_draw_vtk__f("~a.SetLookupTable(~a)~%", [mapper_name, lookup_table_name])
      } else {
        ""
      })
    output_string = output_string +
      share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name])
    output_string = output_string +
      share_draw_vtk__f("~a~%", [vtkactor_glyph_code(actor_name, color, opacity)])
    output_string = output_string +
      share_draw_vtk__f("~a~%", [
        vtkextractpolydatageometry_code(get_extract_name(), t, t),
      ])
    Str(output_string)
  } else {
    merr("vtk3d: not recognized point_type", [])
  }
}

///|
/// The x and y lists of the 2d points object (POINTS-LIST input formats).
fn share_draw_vtk__points2d_xy(arg1 : Value, arg2 : Value) -> (Value, Value) raise {
  let fl = share_draw__float_list
  let count_from_1 = (n : Int) => {
    let c = Collector::new()
    for xx in 1..=n {
      c.add(d_float(int(xx)))
    }
    c.result()
  }
  if d_listp(arg1).truthy() &&
    arg2 is Nil &&
    every(z => d_listp(z).truthy(), rest(arg1)) {
    // xy format
    let tmp = mapcar(z => rest(z), rest(arg1))
    (fl(mapcar(z => first(z), tmp)), fl(mapcar(z => second(z), tmp)))
  } else if d_matrixp(arg1).truthy() && length(cadr(arg1)) == 3 && arg2 is Nil {
    // two-column matrix
    let tmp = mapcar(z => rest(z), rest(arg1))
    (fl(mapcar(z => first(z), tmp)), fl(mapcar(z => second(z), tmp)))
  } else if d_listp(arg1).truthy() &&
    arg2 is Nil &&
    !some(z => d_listp(z).truthy(), rest(arg1)) {
    // y format
    (count_from_1(length(rest(arg1))), fl(rest(arg1)))
  } else if d_matrixp(arg1).truthy() && length(cadr(arg1)) == 2 && arg2 is Nil {
    // one-column matrix
    (count_from_1(length(rest(arg1))), fl(mapcar(z => second(z), rest(arg1))))
  } else if d_matrixp(arg1).truthy() &&
    share_draw__mlength(arg1) == 1 &&
    arg2 is Nil {
    // one-row matrix
    (count_from_1(length(cdadr(arg1))), fl(cdadr(arg1)))
  } else if d_listp(arg1).truthy() &&
    d_listp(arg2).truthy() &&
    length(arg1) == length(arg2) {
    // xx yy format
    (fl(rest(arg1)), fl(rest(arg2)))
  } else if d_matrixp(arg1).truthy() &&
    share_draw__mlength(arg1) == 2 &&
    arg2 is Nil {
    // two-row matrix
    (fl(cdadr(arg1)), fl(cdaddr(arg1)))
  } else {
    merr("draw (points2d): incorrect input format", []) |> ignore
    (Nil, Nil)
  }
}

///|
/// 2D: points([[x1,y1], [x2,y2], [x3,y3],...])
fn vtk2d_points(arg1 : Value, arg2? : Value = Nil) -> Value raise {
  let pointsjoined = get_option(q_d_points_joined)
  let pointtype = get_option(q_d_point_type)
  let pointsize = d_float(get_option(q_d_point_size))
  let linetype = get_option(q_d_line_type)
  let color = share_draw__hex_to_numeric_list(get_option(q_d_color))
  let linewidth = get_option(q_d_line_width)
  let key = get_option(q_d_key)
  let arrayx_name = get_arrayx_name()
  let arrayy_name = get_arrayy_name()
  let table_name = get_table_name()
  let str = StringBuilder::new()
  if share_draw_vtk__trim_key(key) != "" {
    set(q_ear_vtk_2dkey_counter, num_add(symval(q_ear_vtk_2dkey_counter), Fix(1L)))
    |> ignore
  }
  // check type of input
  let (x, y) = share_draw_vtk__points2d_xy(arg1, arg2)
  let n = length(x)
  let (x, y) = share_draw__transform_lists2(x, y)
  let ax = vector(list_to_array(x))
  let ay = vector(list_to_array(y))
  let c255 = () => [
    share_draw_vtk__c255(first(color)),
    share_draw_vtk__c255(second(color)),
    share_draw_vtk__c255(third(color)),
  ]
  // python code
  str.write_string(share_draw_vtk__f("~a=vtk.vtkFloatArray()~%", [arrayx_name]))
  str.write_string(
    share_draw_vtk__f("~a.SetName(\"~a\")~%", [arrayx_name, arrayx_name]),
  )
  str.write_string(share_draw_vtk__f("~a=vtk.vtkFloatArray()~%", [arrayy_name]))
  str.write_string(share_draw_vtk__f("~a.SetName(\"~a\")~%", [arrayy_name, key]))
  for i in 0..<n {
    str.write_string(
      share_draw_vtk__f("~a.InsertNextValue(~a)~%", [arrayx_name, aref1(ax, i)]),
    )
    str.write_string(
      share_draw_vtk__f("~a.InsertNextValue(~a)~%", [arrayy_name, aref1(ay, i)]),
    )
  }
  str.write_string(share_draw_vtk__f("~a=vtk.vtkTable()~%", [table_name]))
  str.write_string(share_draw_vtk__f("~a.AddColumn(~a)~%", [table_name, arrayx_name]))
  str.write_string(
    share_draw_vtk__f("~a.AddColumn(~a)~%~%", [table_name, arrayy_name]),
  )
  let chart = symval(q_ear_vtk_chart_counter)
  if equal(pointsjoined, t) {
    str.write_string(share_draw_vtk__f("line = chart~a.AddPlot(~a)~%", [chart, Fix(0L)]))
    str.write_string(share_draw_vtk__f("line.SetInputData(~a,0,1)~%", [table_name]))
    str.write_string(share_draw_vtk__f("line.SetColor(~a,~a,~a,255)~%", c255()))
    str.write_string(share_draw_vtk__f("line.SetWidth(~a)~%", [linewidth]))
    str.write_string(share_draw_vtk__f("#line.SetLegendVisibility(0)~%", []))
    str.write_string(share_draw_vtk__f("line.SetMarkerStyle(0)~%", []))
    str.write_string(
      share_draw_vtk__f("line.GetPen().SetLineType(~a)~%", [
        share_draw_vtk__vtk_linetype(linetype),
      ]),
    )
  } else if equal(pointsjoined, q_d_impulses) {
    for i in 0..<n {
      let tbl = get_table_name()
      let impx = get_arrayx_name()
      let impy = get_arrayy_name()
      let iv = int(i)
      str.write_string(share_draw_vtk__f("~a=vtk.vtkTable()~%", [tbl]))
      str.write_string(share_draw_vtk__f("~a=vtk.vtkFloatArray()~%", [impx]))
      str.write_string(share_draw_vtk__f("~a.SetNumberOfTuples(2)~%", [impx]))
      str.write_string(share_draw_vtk__f("~a.SetName(\"~a\")~%", [impx, impx]))
      str.write_string(share_draw_vtk__f("~a=vtk.vtkFloatArray()~%", [impy]))
      str.write_string(share_draw_vtk__f("~a.SetNumberOfTuples(2)~%", [impy]))
      str.write_string(share_draw_vtk__f("~a.SetName(\"~a\")~%", [impy, impy]))
      str.write_string(
        share_draw_vtk__f("~a.InsertValue(0,~a.GetColumn(0).GetValue(~a))~%", [
          impx, table_name, iv,
        ]),
      )
      str.write_string(
        share_draw_vtk__f("~a.InsertValue(1,~a.GetColumn(0).GetValue(~a))~%", [
          impx, table_name, iv,
        ]),
      )
      str.write_string(
        share_draw_vtk__f("~a.InsertValue(0,~a.GetColumn(1).GetValue(~a))~%", [
          impy, table_name, iv,
        ]),
      )
      str.write_string(share_draw_vtk__f("~a.InsertValue(1,0.0)~%", [impy]))
      str.write_string(share_draw_vtk__f("~a.AddColumn(~a)~%", [tbl, impx]))
      str.write_string(share_draw_vtk__f("~a.AddColumn(~a)~%", [tbl, impy]))
      str.write_string(
        share_draw_vtk__f("line = chart~a.AddPlot(0)~%", [
          symval(q_ear_vtk_chart_counter),
        ]),
      )
      str.write_string(share_draw_vtk__f("line.SetInputData(~a,0,1)~%", [tbl]))
      str.write_string(share_draw_vtk__f("line.SetColor(~a,~a,~a,255)~%", c255()))
      str.write_string(share_draw_vtk__f("line.SetWidth(~a)~%", [linewidth]))
      str.write_string(share_draw_vtk__f("#line.SetLegendVisibility(0)~%~%", []))
    }
  }
  str.write_string(
    share_draw_vtk__f("line = chart~a.AddPlot(~a)~%", [
      symval(q_ear_vtk_chart_counter),
      Fix(1L),
    ]),
  )
  str.write_string(share_draw_vtk__f("line.SetInputData(~a,0,1)~%", [table_name]))
  str.write_string(share_draw_vtk__f("line.SetColor(~a,~a,~a,255)~%", c255()))
  str.write_string(share_draw_vtk__f("line.SetWidth(~a)~%", [pointsize]))
  str.write_string(
    share_draw_vtk__f("#line.SetLegendVisibility(~a)~%", [
      if share_draw_vtk__trim_key(key) == "" {
        Fix(0L)
      } else {
        Fix(1L)
      },
    ]),
  )
  let pt_is = (vals : Array[Int]) => vals.iter().any(v => eql(pointtype, int(v)))
  let marker = if pt_is([-1, 0]) {
    0
  } else if pt_is([1]) {
    2
  } else if pt_is([2, 3]) {
    1
  } else if pt_is([4, 5, 15]) {
    3
  } else if pt_is([6, 7, 14]) {
    4
  } else if pt_is([12, 13]) {
    5
  } else {
    3
  }
  str.write_string(share_draw_vtk__f("line.SetMarkerStyle(~a)~%~%", [int(marker)]))
  Str(str.to_string())
}

///|
/// 3D: parametric(xfun,yfun,zfun,par1,parmin,parmax)
fn vtk3d_parametric(
  xfun : Value,
  yfun : Value,
  zfun : Value,
  par1 : Value,
  parmin : Value,
  parmax : Value,
) -> Value raise {
  let nticks = get_option(q_d_nticks)
  let color = get_option(q_d_color)
  let line_type = get_option(q_d_line_type)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let source_name = get_source_name()
  let points_name = get_points_name()
  let cellarray_name = get_cellarray_name()
  let floatarray_name = get_floatarray_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let b = bind(q_d_numer, t)
  defer unbind(b)
  let tmin = d_float(parmin)
  let tmax = d_float(parmax)
  let mut tt = tmin
  let eps = num_div(num_sub(tmax, tmin), num_sub(nticks, Fix(1L)))
  let str = StringBuilder::new()
  let mut count = -1
  let mut lookup_table_name : Value = Nil
  let mut scalars : Value = Nil
  check_enhanced3d_model(Str("parametric"), share_draw_vtk__ints([0, 1, 3, 99]))
  |> ignore
  if share_draw_vtk__e3d() == 99 {
    update_enhanced3d_expression(list2(list1(q_mlist), par1)) |> ignore
  }
  if num_lt(tmax, tmin) {
    merr("vtk3d (parametric): illegal range", []) |> ignore
  }
  let lv = list2(list1(q_mlist), par1)
  let f1 = share_draw__coerce_float_fun(xfun, lv)
  let f2 = share_draw__coerce_float_fun(yfun, lv)
  let f3 = share_draw__coerce_float_fun(zfun, lv)
  let nt = to_int(nticks)
  let x = make_array([nt], elt="flonum")
  let y = make_array([nt], elt="flonum")
  let z = make_array([nt], elt="flonum")
  if share_draw_vtk__e3d() > 0 {
    scalars = make_array([nt], elt="flonum")
  }
  for k in 0..<nt {
    let xx = funcall(f1, [tt])
    let yy = funcall(f2, [tt])
    let zz = funcall(f3, [tt])
    match share_draw_vtk__e3d() {
      1 | 99 => aset1(scalars, k, share_draw_vtk__e3d_fun([tt])) |> ignore
      3 => aset1(scalars, k, share_draw_vtk__e3d_fun([xx, yy, zz])) |> ignore
      _ => ()
    }
    let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
    count = count + 1
    aset1(x, count, xx) |> ignore
    aset1(y, count, yy) |> ignore
    aset1(z, count, zz) |> ignore
    tt = num_add(tt, eps)
  }
  if share_draw_vtk__e3d() > 0 {
    lookup_table_name = share_draw_vtk__lut(str)
  }
  // python code
  str.write_string(share_draw_vtk__f("~a=vtk.vtkPolyData()~%", [source_name]))
  str.write_string(
    share_draw_vtk__f("~a~%", [vtkpoints_code(points_name, source_name, x, y, z)]),
  )
  let idx = Collector::new()
  for k in 0..<nt {
    idx.add(int(k))
  }
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkcellarray_code(cellarray_name, source_name, Fix(1L), list1(idx.result())),
    ]),
  )
  str.write_string(share_draw_vtk__f("~a~%", [vtktransform_code(trans_name)]))
  if num_lt(line_type, Fix(0L)) {
    // line type is a tube
    str.write_string(
      share_draw_vtk__f("~a~%", [
        vtktransformpolydatafilter_code(
          Str("auxfiltertube"),
          source_name,
          trans_name,
          t,
        ),
      ]),
    )
  } else {
    str.write_string(
      share_draw_vtk__f("~a~%", [
        vtktransformpolydatafilter_code(filter_name, source_name, trans_name, t),
      ]),
    )
  }
  if num_lt(line_type, Fix(0L)) {
    str.write_string(
      share_draw_vtk__f("~a~%", [
        vtktubefilter_code(filter_name, Str("auxfiltertube"), line_type),
      ]),
    )
    str.write_string(
      share_draw_vtk__f("~a~%", [vtkpolydatamapper_code(mapper_name, filter_name, t)]),
    )
  } else {
    str.write_string(
      share_draw_vtk__f("~a~%", [vtkpolydatamapper_code(mapper_name, filter_name, t)]),
    )
  }
  str.write_string(share_draw_vtk__f("bounds.append(~a.GetBounds())~%", [mapper_name]))
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkactor_code(actor_name, Nil, color, opacity, linewidth, wiredsurface),
    ]),
  )
  str.write_string(
    share_draw_vtk__f("~a~%", [
      vtkextractpolydatageometry_code(get_extract_name(), Nil, Nil),
    ]),
  )
  if share_draw_vtk__e3d() > 0 {
    str.write_string(
      share_draw_vtk__f("~a~%", [
        vtkfloatarray_code(floatarray_name, source_name, scalars, addarr=Nil),
      ]),
    )
    str.write_string(
      share_draw_vtk__f("~a.SetLookupTable(~a)~%", [mapper_name, lookup_table_name]),
    )
    sethash(
      symval(q_ear_vtk_extract_counter),
      symval(q_ear_enhanced3d_or_isolines_code),
      format(Nil, "rescalearray(~a,~a)~%", [points_name, floatarray_name]),
    )
    |> ignore
  }
  if num_ge(line_type, Fix(0L)) {
    // when line type is not a tube, set line pattern
    str.write_string(
      share_draw_vtk__f("~a.GetProperty().SetLineStipplePattern(~a)~%~%", [
        actor_name,
        share_draw_vtk__stipple(line_type),
      ]),
    )
  }
  Str(str.to_string())
}

///|
/// 2D: parametric(xfun,yfun,par,parmin,parmax)
fn vtk2d_parametric(
  xfun : Value,
  yfun : Value,
  par : Value,
  parmin : Value,
  parmax : Value,
) -> Value raise {
  let nticks = get_option(q_d_nticks)
  let linewidth = get_option(q_d_line_width)
  let linetype = get_option(q_d_line_type)
  let color = share_draw__hex_to_numeric_list(get_option(q_d_color))
  let key = get_option(q_d_key)
  let arrayx_name = get_arrayx_name()
  let arrayy_name = get_arrayy_name()
  let table_name = get_table_name()
  let tmin = d_float(parmin)
  let tmax = d_float(parmax)
  let str = StringBuilder::new()
  let b1 = bind(q_d_numer, t)
  defer unbind(b1)
  let eps = num_div(num_sub(tmax, tmin), num_sub(d_float(nticks), Fix(1L)))
  let mut tt = d_float(parmin)
  let b2 = bind(share_draw__q_plot_realpart, symval(share_draw__q_plot_realpart))
  defer unbind(b2)
  if num_lt(tmax, tmin) {
    merr("draw2d (parametric): illegal range", []) |> ignore
  }
  if share_draw_vtk__trim_key(key) != "" {
    set(q_ear_vtk_2dkey_counter, num_add(symval(q_ear_vtk_2dkey_counter), Fix(1L)))
    |> ignore
  }
  if !share_draw_vtk__subsetp_like(
      append(rest(d_listofvars(xfun)), rest(d_listofvars(yfun))),
      list1(par),
    ) {
    merr("draw2d (parametric): non defined variable", []) |> ignore
  }
  set(share_draw__q_plot_realpart, get_option(q_d_draw_realpart)) |> ignore
  let lv = list2(list1(q_mlist), par)
  let f1 = share_draw__coerce_float_fun(xfun, lv)
  let f2 = share_draw__coerce_float_fun(yfun, lv)
  let result : Array[Value] = []
  while true {
    let xx = d_float(funcall(f1, [tt]))
    let yy = d_float(funcall(f2, [tt]))
    let (xx, yy) = share_draw__transform_point2(xx, yy)
    result.push(xx)
    result.push(yy)
    if num_ge(tt, tmax) {
      break
    }
    tt = num_add(tt, eps)
    if num_ge(tt, tmax) {
      tt = tmax
    }
  }
  // python code
  str.write_string(share_draw_vtk__f("~a=vtk.vtkFloatArray()~%", [arrayx_name]))
  str.write_string(
    share_draw_vtk__f("~a.SetName(\"~a\")~%", [arrayx_name, arrayx_name]),
  )
  str.write_string(share_draw_vtk__f("~a=vtk.vtkFloatArray()~%", [arrayy_name]))
  str.write_string(share_draw_vtk__f("~a.SetName(\"~a\")~%", [arrayy_name, key]))
  let mut i = 0
  while i < result.length() {
    str.write_string(
      share_draw_vtk__f("~a.InsertNextValue(~a)~%", [arrayx_name, result[i]]),
    )
    str.write_string(
      share_draw_vtk__f("~a.InsertNextValue(~a)~%", [arrayy_name, result[i + 1]]),
    )
    i = i + 2
  }
  str.write_string(share_draw_vtk__f("~a=vtk.vtkTable()~%", [table_name]))
  str.write_string(share_draw_vtk__f("~a.AddColumn(~a)~%", [table_name, arrayx_name]))
  str.write_string(share_draw_vtk__f("~a.AddColumn(~a)~%", [table_name, arrayy_name]))
  str.write_string(
    share_draw_vtk__f("line=chart~a.AddPlot(0)~%", [symval(q_ear_vtk_chart_counter)]),
  )
  str.write_string(share_draw_vtk__f("line.SetInputData(~a,0,1)~%", [table_name]))
  str.write_string(
    share_draw_vtk__f("line.SetColor(~a,~a,~a,255)~%", [
      share_draw_vtk__c255(first(color)),
      share_draw_vtk__c255(second(color)),
      share_draw_vtk__c255(third(color)),
    ]),
  )
  str.write_string(share_draw_vtk__f("line.SetWidth(~a)~%", [linewidth]))
  str.write_string(
    share_draw_vtk__f("#line.SetLegendVisibility(~a)~%", [
      if share_draw_vtk__trim_key(key) == "" {
        Fix(0L)
      } else {
        Fix(1L)
      },
    ]),
  )
  str.write_string(
    share_draw_vtk__f("line.GetPen().SetLineType(~a)~%~%", [
      share_draw_vtk__vtk_linetype(linetype),
    ]),
  )
  Str(str.to_string())
}

///|
/// 2D: polar(radius,ang,minang,maxang)
fn vtk2d_polar(
  radius : Value,
  ang : Value,
  minang : Value,
  maxang : Value,
) -> Value raise {
  vtk2d_parametric(
    list([list2(q_mtimes, q_simp), radius, list2(list2(q_p_cos, q_simp), ang)]),
    list([list2(q_mtimes, q_simp), radius, list2(list2(q_p_sin, q_simp), ang)]),
    ang,
    minang,
    maxang,
  )
}

///|
/// 3D: parametric_surface(xfun,yfun,zfun,par1,par1min,par1max,par2,par2min,par2max)
fn vtk3d_parametric_surface(
  xfun : Value,
  yfun : Value,
  zfun : Value,
  par1 : Value,
  par1min : Value,
  par1max : Value,
  par2 : Value,
  par2min : Value,
  par2max : Value,
) -> Value raise {
  let xu_grid = get_option(q_d_xu_grid)
  let yv_grid = get_option(q_d_yv_grid)
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let umin = d_float(par1min)
  let umax = d_float(par1max)
  let vmin = d_float(par2min)
  let vmax = d_float(par2max)
  let epsu = num_div(num_sub(umax, umin), xu_grid)
  let epsv = num_div(num_sub(vmax, vmin), yv_grid)
  let source_name = get_source_name()
  let points_name = get_points_name()
  let cellarray_name = get_cellarray_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let str = StringBuilder::new()
  let mut scalars2_count = -1
  let mut scalars_count = -1
  let nx = to_int(xu_grid) + 1
  let ny = to_int(yv_grid) + 1
  let b = bind(q_d_numer, t)
  defer unbind(b)
  let mut count = -1
  let mut scalars : Value = Nil
  let mut scalars2 : Value = Nil
  let mut lookup_table_name : Value = Nil
  check_enhanced3d_model(Str("parametric_surface"), share_draw_vtk__ints([0, 2, 3, 99]))
  |> ignore
  check_isolines_model(Str("parametric_surface"), share_draw_vtk__ints([0, 2, 3, 99]))
  |> ignore
  if share_draw_vtk__e3d() == 99 {
    update_enhanced3d_expression(list([list1(q_mlist), par1, par2])) |> ignore
  }
  if share_draw_vtk__iso() == 99 {
    update_isolines_expression(list([list1(q_mlist), par1, par2])) |> ignore
  }
  if num_lt(umax, umin) || num_lt(vmax, vmin) {
    merr("vtk3d (parametric_surface): illegal range", []) |> ignore
  }
  let lv = list([list1(q_mlist), par1, par2])
  let f1 = share_draw__coerce_float_fun(xfun, lv)
  let f2 = share_draw__coerce_float_fun(yfun, lv)
  let f3 = share_draw__coerce_float_fun(zfun, lv)
  let x = make_array([nx * ny], elt="flonum")
  let y = make_array([nx * ny], elt="flonum")
  let z = make_array([nx * ny], elt="flonum")
  if share_draw_vtk__e3d() > 0 {
    scalars = make_array([nx * ny], elt="flonum")
  }
  if share_draw_vtk__iso() > 0 {
    scalars2 = make_array([nx * ny], elt="flonum")
  }
  let mut vv = vmin
  for _j in 0..<ny {
    let mut uu = umin
    for _i in 0..<nx {
      let xx = funcall(f1, [uu, vv])
      let yy = funcall(f2, [uu, vv])
      let zz = funcall(f3, [uu, vv])
      // geometric transformation
      let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
      count = count + 1
      aset1(x, count, xx) |> ignore
      aset1(y, count, yy) |> ignore
      aset1(z, count, zz) |> ignore
      // check texture model
      match share_draw_vtk__e3d() {
        2 | 99 => {
          scalars_count = scalars_count + 1
          aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([uu, vv])) |> ignore
        }
        3 => {
          scalars_count = scalars_count + 1
          aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([xx, yy, zz]))
          |> ignore
        }
        _ => ()
      }
      // check isolines model
      match share_draw_vtk__iso() {
        2 | 99 => {
          scalars2_count = scalars2_count + 1
          aset1(scalars2, scalars2_count, share_draw_vtk__iso_fun([uu, vv]))
          |> ignore
        }
        3 => {
          scalars2_count = scalars2_count + 1
          aset1(scalars2, scalars2_count, share_draw_vtk__iso_fun([xx, yy, zz]))
          |> ignore
        }
        _ => ()
      }
      uu = num_add(uu, epsu)
    }
    vv = num_add(vv, epsv)
  }
  if share_draw_vtk__e3d() > 0 {
    lookup_table_name = share_draw_vtk__lut(str)
  }
  // python code
  share_draw_vtk__surface_body(
    str,
    source_name,
    points_name,
    cellarray_name,
    trans_name,
    filter_name,
    mapper_name,
    actor_name,
    x,
    y,
    z,
    build_surface_grid(int(nx), int(ny)),
    color,
    opacity,
    linewidth,
    wiredsurface,
  )
  share_draw_vtk__surface_tail(
    str, mapper_name, source_name, points_name, filter_name, lookup_table_name,
    scalars, scalars2, linewidth,
  )
  Str(str.to_string())
}

///|
/// spherical(radius,az,minazi,maxazi,zen,minzen,maxzen)
fn vtk3d_spherical(
  radius : Value,
  azi : Value,
  minazi : Value,
  maxazi : Value,
  zen : Value,
  minzen : Value,
  maxzen : Value,
) -> Value raise {
  let ms = list2(q_mtimes, q_simp)
  vtk3d_parametric_surface(
    list([
      ms,
      radius,
      list2(list2(q_p_sin, q_simp), zen),
      list2(list2(q_p_cos, q_simp), azi),
    ]),
    list([
      ms,
      radius,
      list2(list2(q_p_sin, q_simp), zen),
      list2(list2(q_p_sin, q_simp), azi),
    ]),
    list([ms, radius, list2(list2(q_p_cos, q_simp), zen)]),
    azi,
    minazi,
    maxazi,
    zen,
    minzen,
    maxzen,
  )
}

///|
/// cylindrical(r,z,minz,maxz,azi,minazi,maxazi)
fn vtk3d_cylindrical(
  r : Value,
  z : Value,
  minz : Value,
  maxz : Value,
  azi : Value,
  minazi : Value,
  maxazi : Value,
) -> Value raise {
  let ms = list2(q_mtimes, q_simp)
  vtk3d_parametric_surface(
    list([ms, r, list2(list2(q_p_cos, q_simp), azi)]),
    list([ms, r, list2(list2(q_p_sin, q_simp), azi)]),
    z,
    z,
    minz,
    maxz,
    azi,
    minazi,
    maxazi,
  )
}

///|
/// 3D: explicit(fcn,par1,minval1,maxval1,par2,minval2,maxval2)
fn vtk3d_explicit(
  fcn : Value,
  par1 : Value,
  minval1 : Value,
  maxval1 : Value,
  par2 : Value,
  minval2 : Value,
  maxval2 : Value,
) -> Value raise {
  let xu_grid = get_option(q_d_xu_grid)
  let yv_grid = get_option(q_d_yv_grid)
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let fminval1 = d_float(minval1)
  let fminval2 = d_float(minval2)
  let fmaxval1 = d_float(maxval1)
  let fmaxval2 = d_float(maxval2)
  let epsx = num_div(num_sub(fmaxval1, fminval1), xu_grid)
  let epsy = num_div(num_sub(fmaxval2, fminval2), yv_grid)
  let source_name = get_source_name()
  let points_name = get_points_name()
  let cellarray_name = get_cellarray_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let str = StringBuilder::new()
  let b = bind(q_d_numer, t)
  defer unbind(b)
  let mut count = -1
  let mut scalars : Value = Nil
  let mut scalars2 : Value = Nil
  let mut scalars_count = -1
  let mut scalars2_count = -1
  let nx = to_int(xu_grid) + 1
  let ny = to_int(yv_grid) + 1
  let mut lookup_table_name : Value = Nil
  check_enhanced3d_model(Str("explicit"), share_draw_vtk__ints([0, 2, 3, 99]))
  |> ignore
  check_isolines_model(Str("explicit"), share_draw_vtk__ints([0, 2, 3, 99]))
  |> ignore
  if share_draw_vtk__e3d() == 99 {
    update_enhanced3d_expression(list([list1(q_mlist), par1, par2])) |> ignore
  }
  if share_draw_vtk__iso() == 99 {
    update_isolines_expression(list([list1(q_mlist), par1, par2])) |> ignore
  }
  let fcn = share_draw__coerce_float_fun(fcn, list([list1(q_mlist), par1, par2]))
  let x = make_array([nx * ny], elt="flonum")
  let y = make_array([nx * ny], elt="flonum")
  let z = make_array([nx * ny], elt="flonum")
  if share_draw_vtk__e3d() > 0 {
    scalars = make_array([nx * ny], elt="flonum")
  }
  if share_draw_vtk__iso() > 0 {
    scalars2 = make_array([nx * ny], elt="flonum")
  }
  let mut vv = fminval2
  for _j in 0..<ny {
    let mut uu = fminval1
    for _i in 0..<nx {
      let xx = uu
      let yy = vv
      let zz = funcall(fcn, [xx, yy])
      // geometric transformation
      let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
      count = count + 1
      aset1(x, count, xx) |> ignore
      aset1(y, count, yy) |> ignore
      aset1(z, count, zz) |> ignore
      // check texture model
      match share_draw_vtk__e3d() {
        2 | 99 => {
          scalars_count = scalars_count + 1
          aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([xx, yy])) |> ignore
        }
        3 => {
          scalars_count = scalars_count + 1
          aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([xx, yy, zz]))
          |> ignore
        }
        _ => ()
      }
      // check isolines model
      match share_draw_vtk__iso() {
        2 | 99 => {
          scalars2_count = scalars2_count + 1
          aset1(scalars2, scalars2_count, share_draw_vtk__iso_fun([xx, yy]))
          |> ignore
        }
        3 => {
          scalars2_count = scalars2_count + 1
          aset1(scalars2, scalars2_count, share_draw_vtk__iso_fun([xx, yy, zz]))
          |> ignore
        }
        _ => ()
      }
      uu = num_add(uu, epsx)
    }
    vv = num_add(vv, epsy)
  }
  if share_draw_vtk__e3d() > 0 {
    lookup_table_name = share_draw_vtk__lut(str)
  }
  // python code
  share_draw_vtk__surface_body(
    str,
    source_name,
    points_name,
    cellarray_name,
    trans_name,
    filter_name,
    mapper_name,
    actor_name,
    x,
    y,
    z,
    build_surface_grid(int(nx), int(ny)),
    color,
    opacity,
    linewidth,
    wiredsurface,
  )
  share_draw_vtk__surface_tail(
    str, mapper_name, source_name, points_name, filter_name, lookup_table_name,
    scalars, scalars2, linewidth,
  )
  Str(str.to_string())
}

///|
/// 2D: explicit(fcn,var,minval,maxval)
fn vtk2d_explicit(
  fcn : Value,
  var_ : Value,
  minval : Value,
  maxval : Value,
) -> Value raise {
  let nticks = get_option(q_d_nticks)
  let adaptdepth = get_option(q_d_adapt_depth)
  let linewidth = get_option(q_d_line_width)
  let linetype = get_option(q_d_line_type)
  let color = share_draw__hex_to_numeric_list(get_option(q_d_color))
  let fillcolor = share_draw__hex_to_numeric_list(get_option(q_d_fill_color))
  let key = get_option(q_d_key)
  let mut xmin = d_float(minval)
  let mut xmax = d_float(maxval)
  let mut x_step = num_div(
    num_div(num_sub(xmax, xmin), d_float(nticks)),
    Fix(2L),
  )
  let arrayx_name = get_arrayx_name()
  let arrayy_name = get_arrayy_name()
  let table_name = get_table_name()
  let str = StringBuilder::new()
  let b1 = bind(share_draw__q_plot_realpart, symval(share_draw__q_plot_realpart))
  defer unbind(b1)
  let b2 = bind(q_d_numer, t)
  defer unbind(b2)
  let mut result : Value = Nil
  if num_lt(xmax, xmin) {
    merr("draw2d (explicit): illegal range", []) |> ignore
  }
  if share_draw_vtk__trim_key(key) != "" {
    set(q_ear_vtk_2dkey_counter, num_add(symval(q_ear_vtk_2dkey_counter), Fix(1L)))
    |> ignore
  }
  if get_option(q_d_logx).truthy() {
    xmin = llog(xmin)
    xmax = llog(xmax)
    x_step = num_div(num_div(num_sub(xmax, xmin), d_float(nticks)), Fix(2L))
  }
  set(share_draw__q_plot_realpart, get_option(q_d_draw_realpart)) |> ignore
  let fcn = share_draw__coerce_float_fun(fcn, list2(list1(q_mlist), var_))
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
  while x_end is Cons(_) {
    // The region is x-start to x-end, with mid-point x-mid.
    let mut sublst = share_draw__adaptive_plot(
      fun,
      car(x_start),
      car(x_mid),
      car(x_end),
      car(y_start),
      car(y_mid),
      car(y_end),
      to_int(adaptdepth),
      Flo(1.0e-5),
    )
    if !every(x => numberp(x) || eq(x, t), sublst) {
      let mut item : Value = Nil
      for it in sublst.iter() {
        if !(numberp(it) || eq(it, t)) {
          item = it
        }
      }
      merr("draw2d (explicit): non defined variable in term ~M", [item]) |> ignore
    }
    if result is Cons(_) {
      sublst = cddr(sublst)
    }
    let mut lst = sublst
    while lst is Cons(_) {
      result = append(
        result,
        list2(
          if get_option(q_d_logx).truthy() && numberp(first(lst)) {
            lexp(first(lst))
          } else {
            first(lst)
          },
          if get_option(q_d_logy).truthy() && numberp(second(lst)) {
            lexp(second(lst))
          } else {
            second(lst)
          },
        ),
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
  let result_array = if share_draw__transforming() {
    // With geometric transformation. When option filled_func in not nil,
    // geometric transformation is ignored
    let arr = make_array([length(result)])
    let mut count = -1
    let mut lis = result
    while lis is Cons(_) {
      let xold = first(lis)
      let yold = second(lis)
      let x = funcall(symval(q_ear_draw_transform_f1), [xold, yold])
      let y = funcall(symval(q_ear_draw_transform_f2), [xold, yold])
      count = count + 1
      aset1(arr, count, x) |> ignore
      count = count + 1
      aset1(arr, count, y) |> ignore
      lis = cddr(lis)
    }
    arr
  } else {
    // No geometric transformation invoked.
    vector(list_to_array(result))
  }
  // python code
  str.write_string(share_draw_vtk__f("~a=vtk.vtkFloatArray()~%", [arrayx_name]))
  str.write_string(
    share_draw_vtk__f("~a.SetName(\"~a\")~%", [arrayx_name, arrayx_name]),
  )
  str.write_string(share_draw_vtk__f("~a=vtk.vtkFloatArray()~%", [arrayy_name]))
  str.write_string(share_draw_vtk__f("~a.SetName(\"~a\")~%", [arrayy_name, key]))
  let mut i = 0
  while i < length(result) {
    if !equal(aref1(result_array, i + 1), t) {
      // in case of division by zero, do not insert next value. A vertical
      // line will be plotted, which should be fixed.
      str.write_string(
        share_draw_vtk__f("~a.InsertNextValue(~a)~%", [
          arrayx_name,
          aref1(result_array, i),
        ]),
      )
      str.write_string(
        share_draw_vtk__f("~a.InsertNextValue(~a)~%", [
          arrayy_name,
          aref1(result_array, i + 1),
        ]),
      )
    }
    i = i + 2
  }
  str.write_string(share_draw_vtk__f("~a=vtk.vtkTable()~%", [table_name]))
  str.write_string(share_draw_vtk__f("~a.AddColumn(~a)~%", [table_name, arrayx_name]))
  str.write_string(share_draw_vtk__f("~a.AddColumn(~a)~%", [table_name, arrayy_name]))
  str.write_string(
    share_draw_vtk__f("line=chart~a.AddPlot(~a)~%", [
      symval(q_ear_vtk_chart_counter),
      if get_option(q_d_filled_func).truthy() {
        Fix(3L)
      } else {
        Fix(0L)
      },
    ]),
  )
  str.write_string(share_draw_vtk__f("line.SetInputData(~a,0,1)~%", [table_name]))
  let col = if get_option(q_d_filled_func).truthy() { fillcolor } else { color }
  str.write_string(
    share_draw_vtk__f("line.SetColor(~a,~a,~a,255)~%", [
      share_draw_vtk__c255(first(col)),
      share_draw_vtk__c255(second(col)),
      share_draw_vtk__c255(third(col)),
    ]),
  )
  str.write_string(share_draw_vtk__f("line.SetWidth(~a)~%", [linewidth]))
  str.write_string(
    share_draw_vtk__f("line.GetPen().SetLineType(~a)~%~%", [
      share_draw_vtk__vtk_linetype(linetype),
    ]),
  )
  Str(str.to_string())
}

///|
/// 3d: elevation_grid(mat x0 y0 width height)
fn vtk3d_elevation_grid(
  mat : Value,
  x0 : Value,
  y0 : Value,
  width : Value,
  height : Value,
) -> Value raise {
  let fx0 = d_float(x0)
  let fy0 = d_float(y0)
  let fwidth = d_float(width)
  let fheight = d_float(height)
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let source_name = get_source_name()
  let points_name = get_points_name()
  let cellarray_name = get_cellarray_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let str = StringBuilder::new()
  let mut yi = num_add(fy0, fheight)
  let mut count = -1
  let mut scalars : Value = Nil
  let mut scalars2 : Value = Nil
  let mut scalars_count = -1
  let mut scalars2_count = -1
  let mut lookup_table_name : Value = Nil
  check_enhanced3d_model(Str("elevation_grid"), share_draw_vtk__ints([0, 2, 3]))
  |> ignore
  check_isolines_model(Str("elevation_grid"), share_draw_vtk__ints([0, 2, 3]))
  |> ignore
  if !d_matrixp(mat).truthy() {
    merr("draw3d (elevation_grid): Argument not recognized", []) |> ignore
  }
  let nx = length(cdadr(mat))
  let ny = length(cdr(mat))
  let dx = num_div(fwidth, int(nx - 1))
  let dy = num_div(fheight, int(ny - 1))
  let x = make_array([nx * ny], elt="flonum")
  let y = make_array([nx * ny], elt="flonum")
  let z = make_array([nx * ny], elt="flonum")
  if share_draw_vtk__e3d() > 0 {
    scalars = make_array([nx * ny], elt="flonum")
  }
  if share_draw_vtk__iso() > 0 {
    scalars2 = make_array([nx * ny], elt="flonum")
  }
  for row in cdr(mat).iter() {
    let mut xi = fx0
    for col in cdr(row).iter() {
      let xx = xi
      let yy = yi
      let zz = d_float(col)
      // geometric transformation
      let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
      count = count + 1
      aset1(x, count, xx) |> ignore
      aset1(y, count, yy) |> ignore
      aset1(z, count, zz) |> ignore
      // check texture model
      match share_draw_vtk__e3d() {
        2 => {
          scalars_count = scalars_count + 1
          aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([xx, yy])) |> ignore
        }
        3 => {
          scalars_count = scalars_count + 1
          aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([xx, yy, zz]))
          |> ignore
        }
        _ => ()
      }
      // check isolines model
      match share_draw_vtk__iso() {
        2 => {
          scalars2_count = scalars2_count + 1
          aset1(scalars2, scalars2_count, share_draw_vtk__iso_fun([xx, yy]))
          |> ignore
        }
        3 => {
          scalars2_count = scalars2_count + 1
          aset1(scalars2, scalars2_count, share_draw_vtk__iso_fun([xx, yy, zz]))
          |> ignore
        }
        _ => ()
      }
      xi = num_add(xi, dx)
    }
    yi = num_sub(yi, dy)
  }
  if share_draw_vtk__e3d() > 0 {
    lookup_table_name = share_draw_vtk__lut(str)
  }
  // python code
  share_draw_vtk__surface_body(
    str,
    source_name,
    points_name,
    cellarray_name,
    trans_name,
    filter_name,
    mapper_name,
    actor_name,
    x,
    y,
    z,
    build_surface_grid(int(nx), int(ny)),
    color,
    opacity,
    linewidth,
    wiredsurface,
  )
  share_draw_vtk__surface_tail(
    str, mapper_name, source_name, points_name, filter_name, lookup_table_name,
    scalars, scalars2, linewidth,
  )
  Str(str.to_string())
}

///|
fn build_surface_triangular_grid(ntri : Value) -> Value raise {
  let mut poly : Value = Nil
  let mut cont = -1
  let p = num_div(ntri, Fix(3L))
  // (dotimes (tri p) ...) with p a fixnum (or a ratio: dotimes then runs
  // ceiling(p) times)
  let np = to_int(num_ceiling(p).0)
  for _tri in 0..<np {
    poly = cons(share_draw_vtk__ints([cont + 1, cont + 2, cont + 3]), poly)
    cont = cont + 3
  }
  reverse(poly)
}

///|
/// 3d: implicit(expr,x,xmin,xmax,y,ymin,ymax,z,zmin,zmax)
fn vtk3d_implicit(
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
  let fxmin = d_float(xmin)
  let fxmax = d_float(xmax)
  let fymin = d_float(ymin)
  let fymax = d_float(ymax)
  let fzmin = d_float(zmin)
  let fzmax = d_float(zmax)
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let transform = get_option(q_d_transform)
  let source_name = get_source_name()
  let points_name = get_points_name()
  let cellarray_name = get_cellarray_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let str = StringBuilder::new()
  let mut scalars : Value = Nil
  let mut scalars2 : Value = Nil
  check_enhanced3d_model(Str("implicit"), share_draw_vtk__ints([0, 3, 99]))
  |> ignore
  check_isolines_model(Str("implicit"), share_draw_vtk__ints([0, 3, 99])) |> ignore
  if share_draw_vtk__e3d() == 99 {
    update_enhanced3d_expression(list([list1(q_mlist), par1, par2, par3]))
    |> ignore
  }
  if share_draw_vtk__iso() == 99 {
    update_isolines_expression(list([list1(q_mlist), par1, par2, par3])) |> ignore
  }
  let vertices = find_triangles(
    expr, par1, fxmin, fxmax, par2, fymin, fymax, par3, fzmin, fzmax,
  )
  if vertices is Nil {
    merr("draw3d (implicit): no surface within these ranges", []) |> ignore
  }
  let numvert = length(vertices)
  let x = vector(list_to_array(mapcar(v => first(v), vertices)))
  let y = vector(list_to_array(mapcar(v => second(v), vertices)))
  let z = vector(list_to_array(mapcar(v => third(v), vertices)))
  if share_draw_vtk__e3d() > 0 {
    scalars = make_array([numvert], elt="flonum")
  }
  if share_draw_vtk__iso() > 0 {
    scalars2 = make_array([numvert], elt="flonum")
  }
  for nf in 0..<numvert {
    let mut xx = aref1(x, nf)
    let mut yy = aref1(y, nf)
    let mut zz = aref1(z, nf)
    // geometric transformation
    if !eq(transform, q_d_none) {
      let (x1, y1, z1) = share_draw__transform_point3(xx, yy, zz)
      xx = x1
      yy = y1
      zz = z1
      aset1(x, nf, xx) |> ignore
      aset1(y, nf, yy) |> ignore
      aset1(z, nf, zz) |> ignore
    }
    // check texture model
    if share_draw_vtk__e3d() > 0 {
      aset1(scalars, nf, share_draw_vtk__e3d_fun([xx, yy, zz])) |> ignore
    }
    // check isolines model
    if share_draw_vtk__iso() > 0 {
      aset1(scalars2, nf, share_draw_vtk__iso_fun([xx, yy, zz])) |> ignore
    }
  }
  let lookup_table_name = share_draw_vtk__lut(str)
  // python code
  share_draw_vtk__surface_body(
    str,
    source_name,
    points_name,
    cellarray_name,
    trans_name,
    filter_name,
    mapper_name,
    actor_name,
    x,
    y,
    z,
    build_surface_triangular_grid(int(numvert)),
    color,
    opacity,
    linewidth,
    wiredsurface,
  )
  share_draw_vtk__surface_tail(
    str, mapper_name, source_name, points_name, filter_name, lookup_table_name,
    scalars, scalars2, linewidth,
  )
  Str(str.to_string())
}

///|
/// 3d: label([string1,x1,y1,z1],[string2,x2,y2,z2],...)
fn vtk3d_label(lab : Value) -> Value raise {
  let font_size = get_option(q_d_font_size)
  let colist = share_draw__hex_to_numeric_list(get_option(q_d_color))
  let mut out = ""
  if lab is Nil {
    merr("vtk (label): no arguments in object labels", [])
  } else if !every(z => d_listp(z).truthy(), lab) ||
    !every(z => share_draw__mlength(z) == 4, lab) {
    merr("vtk3d (label): arguments must be lists of length 4", [])
  } else {
    for k in lab.iter() {
      let text = format(Nil, "\"~a\"", [d_first(k)])
      let fx = d_float(funcall(q_d_second, [k]))
      let fy = d_float(funcall(q_d_third, [k]))
      let fz = d_float(funcall(q_d_fourth, [k]))
      if !floatp(fx) || !floatp(fy) || !floatp(fz) {
        merr("vtk3d (label): non real 3d coordinates", []) |> ignore
      }
      let labelactor_name = get_labelactor_name()
      let label_name = get_label_name()
      let polydatamapper_name = get_polydatamapper_name()
      out = out +
        share_draw_vtk__f("~a=vtk.vtkVectorText()~%", [label_name]) +
        share_draw_vtk__f("~a.SetText(~a)~%", [label_name, text]) +
        share_draw_vtk__f("~a=vtk.vtkPolyDataMapper()~%", [polydatamapper_name]) +
        share_draw_vtk__f("~a.SetInputConnection(~a.GetOutputPort())~%", [
          polydatamapper_name, label_name,
        ]) +
        share_draw_vtk__f("~a.ScalarVisibilityOff()~%", [polydatamapper_name]) +
        share_draw_vtk__f("~a=vtk.vtkFollower()~%", [labelactor_name]) +
        share_draw_vtk__f("~a.SetMapper(~a)~%", [labelactor_name, polydatamapper_name]) +
        share_draw_vtk__f("~a.SetScale(~a,~a,~a)~%", [
          labelactor_name, font_size, font_size, font_size,
        ]) +
        share_draw_vtk__f("~a.AddPosition(~a,~a,~a)~%", [labelactor_name, fx, fy, fz]) +
        share_draw_vtk__f("~a.GetProperty().SetColor(~a,~a,~a)~%~%", [
          labelactor_name,
          first(colist),
          second(colist),
          third(colist),
        ])
    }
    Str(out)
  }
}

///|
/// macro VTK-CHECK-TUBE-EXTREME: it refers to local variables of
/// VTK3D-TUBE, so it is expanded inline there.
fn vtk_check_tube_extreme(
  ex : Value,
  cx : Value,
  cy : Value,
  cz : Value,
) -> Value raise {
  ignore((ex, cx, cy, cz))
  raise LispError::SimpleError(
    "VTK-CHECK-TUBE-EXTREME is a macro expanded inline in VTK3D-TUBE",
  )
}

///|
/// 3d: tube(xfun,yfun,zfun,rad,par,parmin,parmax)
fn vtk3d_tube(
  xfun : Value,
  yfun : Value,
  zfun : Value,
  rad : Value,
  par : Value,
  parmin : Value,
  parmax : Value,
) -> Value raise {
  let ugrid = get_option(q_d_xu_grid)
  let vgrid = get_option(q_d_yv_grid)
  let color = get_option(q_d_color)
  let opacity = get_option(q_d_opacity)
  let linewidth = get_option(q_d_line_width)
  let wiredsurface = get_option(q_d_wired_surface)
  let capping = rest(get_option(q_d_capping))
  let tmin = d_float(parmin)
  let tmax = d_float(parmax)
  let vmax : Value = Flo(6.283185307179586) // = float(2*%pi)
  let teps = num_div(num_sub(tmax, tmin), num_sub(ugrid, Fix(1L)))
  let veps = num_div(vmax, num_sub(vgrid, Fix(1L)))
  let nu = to_int(ugrid) + share_draw_vtk__count_t(capping)
  let nv = to_int(vgrid)
  let source_name = get_source_name()
  let points_name = get_points_name()
  let cellarray_name = get_cellarray_name()
  let trans_name = get_trans_name()
  let filter_name = get_filter_name()
  let mapper_name = get_mapper_name()
  let actor_name = get_actor_name()
  let str = StringBuilder::new()
  let mut count = -1
  let mut scalars : Value = Nil
  let mut scalars2 : Value = Nil
  let mut scalars_count = -1
  let mut scalars2_count = -1
  let mut cx : Value = Nil
  let mut cy : Value = Nil
  let mut cz : Value = Nil
  let mut uxold : Value = Nil
  let mut uyold : Value = Nil
  let mut uzold : Value = Nil
  let mut tt : Value = Nil
  if num_lt(tmax, tmin) {
    merr("draw3d (tube): illegal parametric range", []) |> ignore
  }
  if !share_draw_vtk__subsetp_like(
      rest(
        d_append(
          list([
            d_listofvars(xfun),
            d_listofvars(yfun),
            d_listofvars(zfun),
            d_listofvars(rad),
          ]),
        ),
      ),
      list1(par),
    ) {
    merr("draw3d (tube): non defined variable", []) |> ignore
  }
  check_enhanced3d_model(Str("tube"), share_draw_vtk__ints([0, 1, 3, 99])) |> ignore
  check_isolines_model(Str("tube"), share_draw_vtk__ints([0, 1, 3, 99])) |> ignore
  if share_draw_vtk__e3d() == 99 {
    update_enhanced3d_expression(list2(list1(q_mlist), par)) |> ignore
  }
  if share_draw_vtk__iso() == 99 {
    update_isolines_expression(list2(list1(q_mlist), par)) |> ignore
  }
  let lv = list2(list1(q_mlist), par)
  let f1 = share_draw__coerce_float_fun(xfun, lv)
  let f2 = share_draw__coerce_float_fun(yfun, lv)
  let f3 = share_draw__coerce_float_fun(zfun, lv)
  let radius = share_draw__coerce_float_fun(rad, lv)
  let x = make_array([nu * nv], elt="flonum")
  let y = make_array([nu * nv], elt="flonum")
  let z = make_array([nu * nv], elt="flonum")
  if share_draw_vtk__e3d() > 0 {
    scalars = make_array([nu * nv], elt="flonum")
  }
  if share_draw_vtk__iso() > 0 {
    scalars2 = make_array([nu * nv], elt="flonum")
  }
  // macro VTK-CHECK-TUBE-EXTREME
  let check_tube_extreme = (ex : Int, cx : Value, cy : Value, cz : Value) => {
    if equal(nth(ex, get_option(q_d_capping)), t) {
      let mut cxx = cx
      let mut cyy = cy
      let mut czz = cz
      if share_draw__transforming() {
        cxx = funcall(symval(q_ear_draw_transform_f1), [cx, cy, cz])
        cyy = funcall(symval(q_ear_draw_transform_f2), [cx, cy, cz])
        czz = funcall(symval(q_ear_draw_transform_f3), [cx, cy, cz])
      }
      // check texture model
      if share_draw_vtk__e3d() > 0 {
        match share_draw_vtk__e3d() {
          1 | 99 => {
            scalars_count = scalars_count + 1
            aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([tt])) |> ignore
          }
          3 => {
            scalars_count = scalars_count + 1
            aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([cxx, cyy, czz]))
            |> ignore
          }
          _ => ()
        }
      }
      for _k in 0..<to_int(vgrid) {
        count = count + 1
        aset1(x, count, cxx) |> ignore
        aset1(y, count, cyy) |> ignore
        aset1(z, count, czz) |> ignore
      }
    }
  }
  for j in 0..<to_int(ugrid) {
    tt = num_add(tmin, num_mul(int(j), teps))
    // calculate center and radius of circle
    let mut nx : Value = Nil
    let mut ny : Value = Nil
    let mut nz : Value = Nil
    if j == 0 {
      // 1st circle
      cx = funcall(f1, [tt])
      cy = funcall(f2, [tt])
      cz = funcall(f3, [tt])
      let ttnext = num_add(tt, teps)
      check_tube_extreme(1, cx, cy, cz)
      nx = num_sub(funcall(f1, [ttnext]), cx)
      ny = num_sub(funcall(f2, [ttnext]), cy)
      nz = num_sub(funcall(f3, [ttnext]), cz)
    } else {
      // all next circles
      let cxold = cx
      let cyold = cy
      let czold = cz
      cx = funcall(f1, [tt])
      cy = funcall(f2, [tt])
      cz = funcall(f3, [tt])
      nx = num_sub(cx, cxold)
      ny = num_sub(cy, cyold)
      nz = num_sub(cz, czold)
    }
    let r = funcall(radius, [tt])
    // calculate the unitary normal vector
    let mut module_ = lsqrt(num_sum([num_mul(nx, nx), num_mul(ny, ny), num_mul(nz, nz)]))
    nx = num_div(nx, module_)
    ny = num_div(ny, module_)
    nz = num_div(nz, module_)
    // calculate unitary vector perpendicular to n=(nx,ny,nz)
    // ux.nx+uy.ny+uz.nz=0 => ux=-t(ny+nz)/nx, uy=uz=t
    // let's take t=1
    let (ux0, uy0, uz0) : (Value, Value, Value) = if num_eq(nx, Flo(0.0)) {
      (Flo(1.0), Flo(0.0), Flo(0.0))
    } else if num_eq(ny, Flo(0.0)) {
      (Flo(0.0), Flo(1.0), Flo(0.0))
    } else if num_eq(nz, Flo(0.0)) {
      (Flo(0.0), Flo(0.0), Flo(1.0))
    } else {
      (num_neg(num_div(num_add(ny, nz), nx)), Flo(1.0), Flo(1.0))
    }
    module_ = lsqrt(
      num_sum([num_mul(ux0, ux0), num_mul(uy0, uy0), num_mul(uz0, uz0)]),
    )
    let mut ux = num_div(ux0, module_)
    let mut uy = num_div(uy0, module_)
    let mut uz = num_div(uz0, module_)
    if num_gt(tt, tmin) &&
      num_lt(
        num_sum([num_mul(uxold, ux), num_mul(uyold, uy), num_mul(uzold, uz)]),
        Fix(0L),
      ) {
      ux = num_neg(ux)
      uy = num_neg(uy)
      uz = num_neg(uz)
    }
    uxold = ux
    uyold = uy
    uzold = uz
    // vector v = n times u
    let vx = num_sub(num_mul(ny, uz), num_mul(nz, uy))
    let vy = num_sub(num_mul(nz, ux), num_mul(nx, uz))
    let vz = num_sub(num_mul(nx, uy), num_mul(ny, ux))
    // parametric equation of the circumference of radius r and centered
    // at c=(cx,cy,cz):
    // x(t) = c + r(cos(t)u + sin(t)v), for t in (0, 2*%pi)
    let mut vv : Value = Flo(0.0)
    // calculate points of one circumference
    for _i in 0..<to_int(vgrid) {
      let rcos = num_mul(r, lcos(vv))
      let rsin = num_mul(r, lsin(vv))
      let xx = num_sum([cx, num_mul(rcos, ux), num_mul(rsin, vx)])
      let yy = num_sum([cy, num_mul(rcos, uy), num_mul(rsin, vy)])
      let zz = num_sum([cz, num_mul(rcos, uz), num_mul(rsin, vz)])
      // geometric translation
      let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
      count = count + 1
      aset1(x, count, xx) |> ignore
      aset1(y, count, yy) |> ignore
      aset1(z, count, zz) |> ignore
      // check texture model
      if share_draw_vtk__e3d() > 0 {
        match share_draw_vtk__e3d() {
          1 | 99 => {
            scalars_count = scalars_count + 1
            aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([tt])) |> ignore
          }
          3 => {
            scalars_count = scalars_count + 1
            aset1(scalars, scalars_count, share_draw_vtk__e3d_fun([xx, yy, zz]))
            |> ignore
          }
          _ => ()
        }
      }
      // check isolines model
      if share_draw_vtk__iso() > 0 {
        match share_draw_vtk__iso() {
          1 | 99 => {
            scalars2_count = scalars2_count + 1
            aset1(scalars2, scalars2_count, share_draw_vtk__iso_fun([tt])) |> ignore
          }
          3 => {
            scalars2_count = scalars2_count + 1
            aset1(scalars2, scalars2_count, share_draw_vtk__iso_fun([xx, yy, zz]))
            |> ignore
          }
          _ => ()
        }
      }
      vv = num_add(vv, veps)
      if num_gt(vv, vmax) {
        vv = vmax
      }
    }
  }
  check_tube_extreme(2, cx, cy, cz)
  let lookup_table_name = share_draw_vtk__lut(str)
  // python code
  share_draw_vtk__surface_body(
    str,
    source_name,
    points_name,
    cellarray_name,
    trans_name,
    filter_name,
    mapper_name,
    actor_name,
    x,
    y,
    z,
    build_surface_grid(int(nv), int(nu)),
    color,
    opacity,
    linewidth,
    wiredsurface,
  )
  share_draw_vtk__surface_tail(
    str, mapper_name, source_name, points_name, filter_name, lookup_table_name,
    scalars, scalars2, linewidth,
  )
  Str(str.to_string())
}

// ---------------------------------------------------------------------------
// 2D SCENE BUILDER

///|
fn make_vtk_scene_2d(args : Value) -> Value raise {
  let mut objects = ""
  let chart_name = get_chart_name()
  let renderer_name = get_renderer_name()
  ini_gr_options() |> ignore
  ini_local_option_variables() |> ignore
  user_defaults() |> ignore
  let largs = share_draw__listify_arguments(args)
  for x in largs.iter() {
    if equal(d_op(x), Str("=")) {
      let lhs = d_lhs(x)
      let rhs = d_rhs(x)
      let o = (s : Value) => eq(lhs, s)
      if o(q_d_allocation) {
        update_allocation(rhs) |> ignore
      } else if o(q_d_color) {
        update_color(q_d_color, rhs) |> ignore
      } else if o(q_d_fill_color) {
        update_color(q_d_fill_color, rhs) |> ignore
      } else if o(q_d_file_name) {
        update_string(q_d_file_name, rhs) |> ignore
      } else if o(q_d_font_size) {
        update_positive_float(q_d_font_size, rhs) |> ignore
      } else if o(q_d_head_angle) {
        update_positive_float(q_d_head_angle, rhs) |> ignore
      } else if o(q_d_head_length) {
        update_positive_float(q_d_head_length, rhs) |> ignore
      } else if o(q_d_background_color) {
        update_color(q_d_background_color, rhs) |> ignore
      } else if o(q_d_dimensions) {
        update_dimensions(rhs) |> ignore
      } else if o(q_d_nticks) {
        update_positive_integer(q_d_nticks, rhs) |> ignore
      } else if o(q_d_line_width) {
        update_positive_float(q_d_line_width, rhs) |> ignore
      } else if o(q_d_line_type) {
        update_linestyle(q_d_line_type, rhs) |> ignore
      } else if o(q_d_key) {
        update_string(q_d_key, rhs) |> ignore
      } else if o(q_d_key_pos) {
        update_key_pos(rhs) |> ignore
      } else if o(q_d_logx) {
        update_boolean_option(q_d_logx, rhs) |> ignore
      } else if o(q_d_logy) {
        update_boolean_option(q_d_logy, rhs) |> ignore
      } else if o(q_d_filled_func) {
        update_gr_option(q_d_filled_func, rhs) |> ignore
      } else if o(q_d_grid) {
        update_gr_option(q_d_grid, rhs) |> ignore
      } else if o(q_d_transform) {
        update_transform(rhs) |> ignore
      } else if o(q_d_points_joined) {
        update_pointsjoined(rhs) |> ignore
      } else if o(q_d_point_type) {
        update_pointtype(rhs) |> ignore
      } else if o(q_d_point_size) {
        update_nonnegative_float(q_d_point_size, rhs) |> ignore
      } else if o(q_d_terminal) {
        update_terminal(rhs) |> ignore
      } else if o(q_d_unit_vectors) {
        update_boolean_option(q_d_unit_vectors, rhs) |> ignore
      } else if o(q_d_xlabel) {
        update_string(q_d_xlabel, rhs) |> ignore
      } else if o(q_d_ylabel) {
        update_string(q_d_ylabel, rhs) |> ignore
        // options not yet implemented for 2D-vtk; they are included here
        // to avoid error messages
      } else if o(q_d_xrange) {
        update_gr_option(q_d_xrange, rhs) |> ignore
      } else if o(q_d_yrange) {
        update_gr_option(q_d_yrange, rhs) |> ignore
      } else {
        merr("vtk2d: unknown option ~M ", [lhs]) |> ignore
      }
    } else {
      let obj = gethash(caar(x), symval(q_ear_vtk2d_graphic_objects))
      if obj.truthy() {
        objects = objects + lstring(apply(obj, rest(x)))
      } else {
        merr("vtk2d: item ~M is not recognized", [x]) |> ignore
      }
    }
  }
  // scene allocation
  set(q_ear_allocations, cons(get_option(q_d_allocation), symval(q_ear_allocations)))
  |> ignore
  let s1 = lstring(vtkchartxy_code(chart_name))
  Str(s1 + objects + lstring(vtkrenderer2d_code(chart_name, renderer_name)))
}

// ---------------------------------------------------------------------------
// 3D SCENE BUILDER

///|
fn make_vtk_scene_3d(args : Value) -> Value raise {
  let mut objects = ""
  let appenddata_name = get_appenddata_name()
  let outline_name = get_outline_name()
  let polydatamapper_name = get_polydatamapper_name()
  let outlineactor_name = get_outlineactor_name()
  let textproperty_name = get_textproperty_name()
  let cubeaxesactor2d_name = get_cubeaxesactor2d_name()
  let renderer_name = get_renderer_name()
  let camera_name = get_camera_name()
  let first_actor = num_add(symval(q_ear_vtk_actor_counter), Fix(1L))
  let first_labelactor = num_add(symval(q_ear_vtk_labelactor_counter), Fix(1L))
  let first_extract = num_add(symval(q_ear_vtk_extract_counter), Fix(1L))
  let first_label = num_add(symval(q_ear_vtk_label_counter), Fix(1L))
  ini_gr_options() |> ignore
  ini_local_option_variables() |> ignore
  user_defaults() |> ignore
  let largs = share_draw__listify_arguments(args)
  for x in largs.iter() {
    if equal(d_op(x), Str("=")) {
      let lhs = d_lhs(x)
      let rhs = d_rhs(x)
      let o = (s : Value) => eq(lhs, s)
      if o(q_d_allocation) {
        update_allocation(rhs) |> ignore
      } else if o(q_d_axis_3d) {
        update_boolean_option(q_d_axis_3d, rhs) |> ignore
      } else if o(q_d_background_color) {
        update_color(q_d_background_color, rhs) |> ignore
      } else if o(q_d_capping) {
        update_capping(rhs) |> ignore
      } else if o(q_d_color) {
        update_color(q_d_color, rhs) |> ignore
      } else if o(q_d_isolines_color) {
        update_color(q_d_isolines_color, rhs) |> ignore
      } else if o(q_d_isolines_levels) {
        update_contour_isolines(q_d_isolines_levels, rhs) |> ignore
      } else if o(q_d_dimensions) {
        update_dimensions(rhs) |> ignore
      } else if o(q_d_enhanced3d) {
        update_enhanced3d(rhs) |> ignore
      } else if o(q_d_file_name) {
        update_string(q_d_file_name, rhs) |> ignore
      } else if o(q_d_font_size) {
        update_positive_float(q_d_font_size, rhs) |> ignore
      } else if o(q_d_head_angle) {
        update_positive_float(q_d_head_angle, rhs) |> ignore
      } else if o(q_d_head_length) {
        update_positive_float(q_d_head_length, rhs) |> ignore
      } else if o(q_d_isolines) {
        update_isolines(rhs) |> ignore
      } else if o(q_d_line_type) {
        update_linestyle(q_d_line_type, rhs) |> ignore
      } else if o(q_d_line_width) {
        update_positive_float(q_d_line_width, rhs) |> ignore
      } else if o(q_d_nticks) {
        update_positive_integer(q_d_nticks, rhs) |> ignore
      } else if o(q_d_opacity) {
        update_opacity(rhs) |> ignore
      } else if o(q_d_palette) {
        update_palette(rhs) |> ignore
      } else if o(q_d_points_joined) {
        update_pointsjoined(rhs) |> ignore
      } else if o(q_d_point_size) {
        update_nonnegative_float(q_d_point_size, rhs) |> ignore
      } else if o(q_d_point_type) {
        update_pointtype(rhs) |> ignore
      } else if o(q_d_terminal) {
        update_terminal(rhs) |> ignore
      } else if o(q_d_transform) {
        update_transform(rhs) |> ignore
      } else if o(q_d_unit_vectors) {
        update_boolean_option(q_d_unit_vectors, rhs) |> ignore
      } else if o(q_d_view) {
        update_view(rhs) |> ignore
      } else if o(q_d_wired_surface) {
        update_boolean_option(q_d_wired_surface, rhs) |> ignore
      } else if o(q_d_xu_grid) {
        update_positive_integer(q_d_xu_grid, rhs) |> ignore
      } else if o(q_d_yv_grid) {
        update_positive_integer(q_d_yv_grid, rhs) |> ignore
      } else if o(q_d_x_voxel) {
        update_positive_integer(q_d_x_voxel, rhs) |> ignore
      } else if o(q_d_y_voxel) {
        update_positive_integer(q_d_y_voxel, rhs) |> ignore
      } else if o(q_d_z_voxel) {
        update_positive_integer(q_d_z_voxel, rhs) |> ignore
      } else if o(q_d_xlabel) {
        update_string(q_d_xlabel, rhs) |> ignore
      } else if o(q_d_ylabel) {
        update_string(q_d_ylabel, rhs) |> ignore
      } else if o(q_d_zlabel) {
        update_string(q_d_zlabel, rhs) |> ignore
      } else if o(q_d_gnuplot_file_name) {
        // must be changed to script_file_name
        update_string(q_d_gnuplot_file_name, rhs) |> ignore
        // options not yet implemented for 3D-vtk; they are included here
        // to avoid error messages
      } else if o(q_d_surface_hide) {
        update_boolean_option(q_d_surface_hide, rhs) |> ignore
      } else if o(q_d_label_alignment) {
        update_string(q_d_label_alignment, rhs) |> ignore
      } else if o(q_d_label_orientation) {
        update_string(q_d_label_orientation, rhs) |> ignore
      } else if o(q_d_xrange) {
        update_gr_option(q_d_xrange, rhs) |> ignore
      } else if o(q_d_yrange) {
        update_gr_option(q_d_yrange, rhs) |> ignore
      } else if o(q_d_zrange) {
        update_gr_option(q_d_zrange, rhs) |> ignore
      } else {
        merr("vtk3d: unknown option ~M ", [lhs]) |> ignore
      }
    } else {
      let obj = gethash(caar(x), symval(q_ear_vtk3d_graphic_objects))
      if obj.truthy() {
        objects = objects + lstring(apply(obj, rest(x)))
      } else {
        merr("vtk3d: item ~M is not recognized", [x]) |> ignore
      }
    }
  }
  // scene allocation
  set(q_ear_allocations, cons(get_option(q_d_allocation), symval(q_ear_allocations)))
  |> ignore
  let s = StringBuilder::new()
  s.write_string(objects)
  if num_gt(symval(q_ear_vtk_extract_counter), Fix(0L)) {
    s.write_string(lstring(scenebounds()))
  }
  s.write_string(
    lstring(vtkappendpolydata_code(appenddata_name, first_extract, first_label)),
  )
  s.write_string(lstring(vtkoutlinefilter_code(outline_name, appenddata_name)))
  s.write_string(
    lstring(vtkpolydatamapper_code(polydatamapper_name, outline_name, t)),
  )
  s.write_string(
    lstring(
      vtkactor_code(
        outlineactor_name,
        polydatamapper_name,
        Str("#ff0000"),
        Fix(1L),
        Fix(1L),
        Nil,
      ),
    ),
  )
  s.write_string(lstring(vtktextproperty_code(textproperty_name)))
  s.write_string(
    lstring(
      vtkcubeaxesactor2d_code(cubeaxesactor2d_name, appenddata_name, textproperty_name),
    ),
  )
  s.write_string(
    lstring(
      vtkrenderer3d_code(
        renderer_name,
        cubeaxesactor2d_name,
        outlineactor_name,
        get_option(q_d_background_color),
        camera_name,
        car(get_option(q_d_view)),
        cadr(get_option(q_d_view)),
        first_actor,
        first_labelactor,
      ),
    ),
  )
  Str(s.to_string())
}

///|
fn draw_vtk(args : Value) -> Value raise {
  let mut scenes : Array[Value] = []
  ini_gr_options() |> ignore
  ini_global_options() |> ignore
  ini_local_option_variables() |> ignore
  user_defaults() |> ignore
  set(q_ear_allocations, Nil) |> ignore
  for c in [
    q_ear_vtk_appenddata_counter, q_ear_vtk_extract_counter, q_ear_vtk_outline_counter,
    q_ear_vtk_polydatamapper_counter, q_ear_vtk_outlineactor_counter, q_ear_vtk_textproperty_counter,
    q_ear_vtk_cubeaxesactor2d_counter, q_ear_vtk_camera_counter, q_ear_vtk_renderer_counter,
    q_ear_vtk_source_counter, q_ear_vtk_mapper_counter, q_ear_vtk_actor_counter,
    q_ear_vtk_labelactor_counter, q_ear_vtk_trans_counter, q_ear_vtk_filter_counter,
    q_ear_vtk_data_file_counter, q_ear_vtk_floatarray_counter, q_ear_vtk_points_counter,
    q_ear_vtk_glyphpoints_counter, q_ear_vtk_polydata_counter, q_ear_vtk_cellarray_counter,
    q_ear_vtk_solidsource_counter, q_ear_vtk_triangle_counter, q_ear_vtk_label_counter,
    q_ear_vtk_chart_counter, q_ear_vtk_table_counter, q_ear_vtk_arrayx_counter,
    q_ear_vtk_arrayy_counter, q_ear_vtk_2dkey_counter, q_ear_vtk_isolines_counter,
  ] {
    set(c, Fix(0L)) |> ignore
  }
  set(q_ear_lookup_tables, Nil) |> ignore
  set(q_ear_unitscale_already_defined, Nil) |> ignore
  let largs = share_draw__listify_arguments(args)
  for x in largs.iter() {
    if equal(d_op(x), Str("=")) {
      let lhs = d_lhs(x)
      let rhs = d_rhs(x)
      if eq(lhs, q_d_terminal) {
        update_terminal(rhs) |> ignore
      } else if eq(lhs, q_d_columns) {
        update_positive_integer(q_d_columns, rhs) |> ignore
      } else if eq(lhs, q_d_dimensions) {
        update_dimensions(rhs) |> ignore
      } else if eq(lhs, q_d_file_name) {
        update_string(q_d_file_name, rhs) |> ignore
      } else if eq(lhs, q_d_background_color) {
        update_color(q_d_background_color, rhs) |> ignore
      } else {
        merr("draw: unknown global option ~M ", [lhs]) |> ignore
      }
    } else if equal(caar(x), q_d_gr3d) {
      scenes.push(make_vtk_scene_3d(rest(x)))
    } else if equal(caar(x), q_d_gr2d) {
      scenes.push(make_vtk_scene_2d(rest(x)))
    } else {
      merr("draw: item ~M is not recognized", [x]) |> ignore
    }
  }
  // prepare script file
  let gfn = share_draw__plot_temp_file(
    format(Nil, "maxout~d.py", [share_draw__getpid()]),
  )
  let cmdstorage = StringBuilder::new()
  // pull in required packages
  cmdstorage.write_string(
    share_draw_vtk__f("~a~%~a~%~%~a~%~a~%~%~a~%~%", [
      Str("#!/usr/bin/env python"),
      Str("# -*- coding: UTF-8 -*-"),
      Str("import vtk"),
      Str("import sys"),
      Str("bounds=[]"),
    ]),
  )
  // write scenes
  for scn in scenes {
    cmdstorage.write_string(share_draw_vtk__f("~a", [scn]))
  }
  // the renderer window
  cmdstorage.write_string(
    share_draw_vtk__f("~a", [vtkrendererwindow_code(int(scenes.length()))]),
  )
  cmdstorage.write_string(share_draw_vtk__f("~a", [vtk_terminal()]))
  // close script file
  write_file(lstring(gfn), cmdstorage.to_string()) catch {
    _ =>
      merr(
        "draw: Cannot create file '~a'. Probably maxima_tempdir doesn't point to a writable directory.",
        [gfn],
      )
      |> ignore
  }
  // The Lisp code now runs the script with ($system "python ..."); the
  // port cannot run programs, so the script is only written.
  q_d_done
}

///|
/// Top-level forms of vtk.lisp.
fn init_share_vtk() -> Unit raise {
  // (defparameter *enhanced3d-or-isolines-code* (make-hash-table))
  set(q_ear_enhanced3d_or_isolines_code, make_hash_table()) |> ignore
  if !boundp(q_ear_vtk2d_graphic_objects) {
    set(q_ear_vtk2d_graphic_objects, make_hash_table()) |> ignore
  }
  let t2 = symval(q_ear_vtk2d_graphic_objects)
  sethash(q_d_explicit, t2, q_vtk2d_explicit) |> ignore
  sethash(q_d_parametric, t2, q_vtk2d_parametric) |> ignore
  sethash(q_d_points, t2, q_vtk2d_points) |> ignore
  sethash(q_d_polar, t2, q_vtk2d_polar) |> ignore
  if !boundp(q_ear_vtk3d_graphic_objects) {
    set(q_ear_vtk3d_graphic_objects, make_hash_table()) |> ignore
  }
  let t3 = symval(q_ear_vtk3d_graphic_objects)
  let entries = [
    (q_d_cone, q_vtk3d_cone),
    (q_d_cylinder, q_vtk3d_cylinder),
    (q_d_cube, q_vtk3d_cube),
    (q_d_prism, q_vtk3d_prism),
    (q_d_elevation_grid, q_vtk3d_elevation_grid),
    (q_d_implicit, q_vtk3d_implicit),
    (q_d_sphere, q_vtk3d_sphere),
    (q_d_parallelogram, q_vtk3d_parallelogram),
    (q_d_triangle, q_vtk3d_triangle),
    (q_d_vector, q_vtk3d_vector),
    (q_d_points, q_vtk3d_points),
    (q_d_parametric, q_vtk3d_parametric),
    (q_d_parametric_surface, q_vtk3d_parametric_surface),
    (q_d_spherical, q_vtk3d_spherical),
    (q_d_cylindrical, q_vtk3d_cylindrical),
    (q_d_explicit, q_vtk3d_explicit),
    (q_d_label, q_vtk3d_label),
    (q_d_tube, q_vtk3d_tube),
  ]
  for kv in entries {
    sethash(kv.0, t3, kv.1) |> ignore
  }
}
