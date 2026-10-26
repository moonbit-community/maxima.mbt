// Port of share/draw/gnuplot.lisp (part 2): the 3d graphic objects, image,
// the scene builders and draw_gnuplot, which writes the Gnuplot command
// and data files.  The port cannot run Gnuplot: where the Lisp code sends
// commands to a Gnuplot process or calls ($system $gnuplot_command ...),
// that step is skipped; the files are written exactly as by the Lisp code.

// ---------------------------------------------------------------------------
// Object: 'implicit3d'
// Usage:
//     implicit(expr,x,xmin,xmax,y,ymin,ymax,z,zmin,zmax)

///|
fn share_draw__implicit3d(
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
  let xmin = d_float(xmin)
  let xmax = d_float(xmax)
  let ymin = d_float(ymin)
  let ymax = d_float(ymax)
  let zmin = d_float(zmin)
  let zmax = d_float(zmax)
  let mut pts : Value = Nil
  let mut grouping : Value = Nil
  if !share_draw__subsetp_like(
      rest(d_listofvars(expr)),
      list([par1, par2, par3]),
    ) {
    merr("draw3d (implicit): non defined variable", []) |> ignore
  }
  check_enhanced3d_model(Str("implicit"), list([Fix(0L), Fix(3L), Fix(99L)]))
  |> ignore
  if num_eq(symval(q_ear_draw_enhanced3d_type), Fix(99L)) {
    update_enhanced3d_expression(list([list1(q_mlist), par1, par2, par3]))
    |> ignore
  }
  let ncols = if num_eq(symval(q_ear_draw_enhanced3d_type), Fix(0L)) {
    3
  } else {
    4
  }
  let vertices = find_triangles(
    expr, par1, xmin, xmax, par2, ymin, ymax, par3, zmin, zmax,
  )
  if vertices is Nil {
    merr("draw3d (implicit): no surface within these ranges", []) |> ignore
  }
  update_ranges_3d(xmin, xmax, ymin, ymax, zmin, zmax) |> ignore
  let style : Value = Str(
    if equal(get_option(q_d_enhanced3d), q_d_none) {
      "l"
    } else {
      "pm3d"
    },
  )
  let other = format(Nil, " t '' w ~a lw ~a lt ~a lc ~a", [
    style,
    get_option(q_d_line_width),
    get_option(q_d_line_type),
    share_draw__rgb(q_d_color),
  ])
  let others = Collector::new()
  for _ in 0..<(length(vertices) / 3 - 1) {
    others.add(other)
  }
  let pltcmd = cons(
    format(Nil, " ~a w ~a lw ~a lt ~a lc ~a", [
      make_obj_title(get_option(q_d_key)),
      style,
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
    ]),
    others.result(),
  )
  let mut v = vertices
  while !(v is Nil) {
    if ncols == 3 {
      pts = cons(
        share_draw__vec(
          flatten(list([first(v), second(v), first(v), third(v)])),
        ),
        pts,
      )
    } else {
      let v1 = first(v)
      let v2 = second(v)
      let v3 = third(v)
      let f = symval(q_ear_draw_enhanced3d_fun)
      let color1 = funcall(f, [car(v1), cadr(v1), caddr(v1)])
      let color2 = funcall(f, [car(v2), cadr(v2), caddr(v2)])
      let color3 = funcall(f, [car(v3), cadr(v3), caddr(v3)])
      pts = cons(
        share_draw__vec(
          flatten(list([v1, color1, v2, color2, v1, color1, v3, color3])),
        ),
        pts,
      )
    }
    grouping = cons(list2(int(ncols), Fix(2L)), grouping)
    v = cdddr(v)
  }
  share_draw__make_gr_object(q_implicit, pltcmd, grouping, pts)
}

// ---------------------------------------------------------------------------
// Object: 'explicit3d'
// Usage:
//     explicit(fcn,par1,minval1,maxval1,par2,minval2,maxval2)

///|
fn share_draw__explicit3d(
  fcn : Value,
  par1 : Value,
  minval1 : Value,
  maxval1 : Value,
  par2 : Value,
  minval2 : Value,
  maxval2 : Value,
) -> Value raise {
  with_specials(
    [(share_draw__q_plot_realpart, symval(share_draw__q_plot_realpart)), (q_d_numer, t)],
    () => {
      let xu_grid = get_option(q_d_xu_grid)
      let yv_grid = get_option(q_d_yv_grid)
      let mut fminval1 = d_float(minval1)
      let mut fminval2 = d_float(minval2)
      let mut fmaxval1 = d_float(maxval1)
      let mut fmaxval2 = d_float(maxval2)
      let epsx = num_div(num_sub(fmaxval1, fminval1), xu_grid)
      let epsy = num_div(num_sub(fmaxval2, fminval2), yv_grid)
      let ext = ShareDrawExt::new()
      let nx = to_int(xu_grid) + 1
      let ny = to_int(yv_grid) + 1
      let mut count = -1
      if !share_draw__subsetp_like(rest(d_listofvars(fcn)), list2(par1, par2)) {
        // Search for the item in sublist that is the undefined variable
        let mut item : Value = Nil
        for it in rest(d_listofvars(fcn)).iter() {
          if !share_draw__subsetp_like(list1(it), list2(par1, par2)) {
            item = it
          }
        }
        merr("draw3d (explicit): non defined variable in term ~M", [item])
        |> ignore
      }
      set(share_draw__q_plot_realpart, get_option(q_d_draw_realpart)) |> ignore
      check_enhanced3d_model(
        Str("explicit"),
        list([Fix(0L), Fix(2L), Fix(3L), Fix(99L)]),
      )
      |> ignore
      if num_eq(symval(q_ear_draw_enhanced3d_type), Fix(99L)) {
        update_enhanced3d_expression(list([list1(q_mlist), par1, par2]))
        |> ignore
      }
      let fcn = share_draw__coerce_float_fun(fcn, mk(q_mlist, [par1, par2]))
      let e3type = to_int(symval(q_ear_draw_enhanced3d_type))
      let ncols = if e3type == 0 { 3 } else { 4 }
      let result : Array[Value] = Array::make(ncols * nx * ny, Fix(0L))
      let mut vv = fminval2
      for _j in 0..<ny {
        let mut uu = fminval1
        for _i in 0..<nx {
          let xx = uu
          let yy = vv
          let zz = funcall(fcn, [xx, yy])
          let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
          if share_draw__transforming() {
            ext.x(xx)
            ext.y(yy)
          }
          ext.z(zz)
          count = count + 1
          result[count] = xx
          count = count + 1
          result[count] = yy
          count = count + 1
          result[count] = zz
          // check texture model
          if e3type == 2 || e3type == 99 {
            count = count + 1
            result[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [xx, yy])
          } else if e3type == 3 {
            count = count + 1
            result[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [
              xx, yy, zz,
            ])
          }
          uu = num_add(uu, epsx)
        }
        vv = num_add(vv, epsy)
      }
      if share_draw__transforming() {
        fminval1 = ext.xmin
        fmaxval1 = ext.xmax
        fminval2 = ext.ymin
        fmaxval2 = ext.ymax
      }
      update_ranges_3d(
        fminval1, fmaxval1, fminval2, fmaxval2, ext.zmin, ext.zmax,
      )
      |> ignore
      share_draw__make_gr_object(
        q_explicit,
        format(Nil, " ~a w ~a lw ~a lt ~a lc ~a", [
          make_obj_title(get_option(q_d_key)),
          Str(if e3type > 0 { "pm3d" } else { "l" }),
          get_option(q_d_line_width),
          get_option(q_d_line_type),
          share_draw__rgb(q_d_color),
        ]),
        list1(list2(int(ncols), int(nx))),
        list1(vector(result)),
      )
    },
  )
}

// ---------------------------------------------------------------------------
// Object: 'elevation_grid'
// Usage:
//     elevation_grid(mat,x0,y0,width,height)

///|
fn share_draw__elevation_grid(
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
  let ext = ShareDrawExt::new()
  let mut ncols_file = 0
  let mut ncols = 0
  let mut result : Value = Nil
  check_enhanced3d_model(
    Str("elevation_grid"),
    list([Fix(0L), Fix(2L), Fix(3L)]),
  )
  |> ignore
  if d_matrixp(mat).truthy() {
    let mut yi = num_add(fy0, fheight)
    let mut count = -1
    ncols = length(cdadr(mat))
    let nrows = length(cdr(mat))
    let dx = num_div(fwidth, int(ncols - 1))
    let dy = num_div(fheight, int(nrows - 1))
    let e3type = to_int(symval(q_ear_draw_enhanced3d_type))
    ncols_file = if e3type == 0 { 3 } else { 4 }
    let arr : Array[Value] = Array::make(ncols * nrows * ncols_file, Flo(0.0))
    for row in cdr(mat).iter() {
      let mut xi = fx0
      for col in cdr(row).iter() {
        let xx = xi
        let yy = yi
        let zz = d_float(col)
        let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
        if share_draw__transforming() {
          ext.x(xx)
          ext.y(yy)
        }
        ext.z(zz)
        count = count + 1
        arr[count] = xx
        count = count + 1
        arr[count] = yy
        count = count + 1
        arr[count] = zz
        // check texture model
        if e3type == 2 {
          count = count + 1
          arr[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [xx, yy])
        } else if e3type == 3 {
          count = count + 1
          arr[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [xx, yy, zz])
        }
        xi = num_add(xi, dx)
      }
      yi = num_sub(yi, dy)
    }
    result = vector(arr)
  } else {
    merr("draw3d (elevation_grid): Argument not recognized", []) |> ignore
  }
  if num_eq(symval(q_ear_draw_transform_dimensions), Fix(0L)) {
    ext.xmin = fx0
    ext.xmax = num_add(fx0, fwidth)
    ext.ymin = fy0
    ext.ymax = num_add(fy0, fheight)
  }
  update_ranges_3d(ext.xmin, ext.xmax, ext.ymin, ext.ymax, ext.zmin, ext.zmax)
  |> ignore
  share_draw__make_gr_object(
    q_elevation_grid,
    format(Nil, " ~a w ~a lw ~a lt ~a lc ~a", [
      make_obj_title(get_option(q_d_key)),
      Str(
        if num_gt(symval(q_ear_draw_enhanced3d_type), Fix(0L)) {
          "pm3d"
        } else {
          "l"
        },
      ),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
    ]),
    list1(list2(int(ncols_file), int(ncols))),
    list1(result),
  )
}

// ---------------------------------------------------------------------------
// Object: 'mesh'
// Usage:
//     mesh([[x_11,y_11,z_11], ...,[x_1n,y_1n,z_1n]],
//          [[x_21,y_21,z_21], ...,[x_2n,y_2n,z_2n]],
//          ...,
//          [[x_m1,y_m1,z_m1], ...,[x_mn,y_mn,z_mn]])

///|
fn share_draw__mesh(row : Value) -> Value raise {
  let ext = ShareDrawExt::new()
  let mut count = -1
  // let's see if the user wants to use mesh in the old way, what we now
  // call elevation_grid
  if length(row) == 5 && d_matrixp(first(row)).truthy() {
    print(Str("Warning: Seems like you want to draw an elevation_grid object..."))
    |> ignore
    print(Str("         Please, see documentation for object elevation_grid."))
    |> ignore
    return apply(q_elevation_grid, row)
  }
  check_enhanced3d_model(Str("mesh"), list([Fix(0L), Fix(2L), Fix(3L)]))
  |> ignore
  if length(row) < 2 || !every(z => d_listp(z).truthy(), row) {
    merr("draw3d (mesh): Arguments must be two or more lists", []) |> ignore
  }
  let e3type = to_int(symval(q_ear_draw_enhanced3d_type))
  let ncols_file = if e3type == 0 { 3 } else { 4 }
  let m = length(row)
  let n = share_draw__mlength(first(row))
  let result : Array[Value] = Array::make(m * n * ncols_file, Flo(0.0))
  let mut row_num = 0
  for r in row.iter() {
    row_num = row_num + 1
    let mut col_num = 0
    for c in rest(r).iter() {
      col_num = col_num + 1
      let xx = d_float(d_first(c))
      let yy = d_float(funcall(q_d_second, [c]))
      let zz = d_float(funcall(q_d_third, [c]))
      let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
      ext.x(xx)
      ext.y(yy)
      ext.z(zz)
      count = count + 1
      result[count] = xx
      count = count + 1
      result[count] = yy
      count = count + 1
      result[count] = zz
      // check texture model
      if e3type == 2 {
        count = count + 1
        result[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [
          int(row_num),
          int(col_num),
        ])
      } else if e3type == 3 {
        count = count + 1
        result[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [xx, yy, zz])
      }
    }
  }
  update_ranges_3d(ext.xmin, ext.xmax, ext.ymin, ext.ymax, ext.zmin, ext.zmax)
  |> ignore
  share_draw__make_gr_object(
    q_mesh,
    format(Nil, " ~a w ~a lw ~a lt ~a lc ~a", [
      make_obj_title(get_option(q_d_key)),
      Str(if e3type > 0 { "pm3d" } else { "l" }),
      get_option(q_d_line_width),
      get_option(q_d_line_type),
      share_draw__rgb(q_d_color),
    ]),
    list1(list2(int(ncols_file), int(n))),
    list1(vector(result)),
  )
}

///|
/// ((mlist simp) ((mlist simp) a1 a2 a3) ((mlist simp) b1 b2 b3))
fn share_draw__vertex_list3(
  a : (Value, Value, Value),
  b : (Value, Value, Value),
) -> Value {
  mk_simp(q_mlist, [
    mk_simp(q_mlist, [a.0, a.1, a.2]),
    mk_simp(q_mlist, [b.0, b.1, b.2]),
  ])
}

// ---------------------------------------------------------------------------
// Object: 'triangle3d'
// Usage:
//     triangle([x1,y1,z1], [x2,y2,z2], [x3,y3,z3])

///|
fn share_draw__triangle3d(arg1 : Value, arg2 : Value, arg3 : Value) -> Value raise {
  if !share_draw__vertices_ok([arg1, arg2, arg3], 3) {
    merr("draw3d (triangle): vertices are not correct", []) |> ignore
  }
  let x1 = d_float(cadr(arg1))
  let y1 = d_float(caddr(arg1))
  let z1 = d_float(cadddr(arg1))
  let x2 = d_float(cadr(arg2))
  let y2 = d_float(caddr(arg2))
  let z2 = d_float(cadddr(arg2))
  let x3 = d_float(cadr(arg3))
  let y3 = d_float(caddr(arg3))
  let z3 = d_float(cadddr(arg3))
  let grobj = share_draw__mesh(
    list2(
      share_draw__vertex_list3((x1, y1, z1), (x1, y1, z1)),
      share_draw__vertex_list3((x2, y2, z2), (x3, y3, z3)),
    ),
  )
  share_draw__set_gr_object_name(grobj, q_triangle)
  grobj
}

// ---------------------------------------------------------------------------
// Object: 'quadrilateral3d'
// Usage:
//     quadrilateral([x1,y1,z1], [x2,y2,z2], [x3,y3,z3], [x4,y4,z4])

///|
fn share_draw__quadrilateral3d(
  arg1 : Value,
  arg2 : Value,
  arg3 : Value,
  arg4 : Value,
) -> Value raise {
  if !share_draw__vertices_ok([arg1, arg2, arg3, arg4], 3) {
    merr("draw3d (quadrilateral): vertices are not correct", []) |> ignore
  }
  let x1 = d_float(cadr(arg1))
  let y1 = d_float(caddr(arg1))
  let z1 = d_float(cadddr(arg1))
  let x2 = d_float(cadr(arg2))
  let y2 = d_float(caddr(arg2))
  let z2 = d_float(cadddr(arg2))
  let x3 = d_float(cadr(arg3))
  let y3 = d_float(caddr(arg3))
  let z3 = d_float(cadddr(arg3))
  let x4 = d_float(cadr(arg4))
  let y4 = d_float(caddr(arg4))
  let z4 = d_float(cadddr(arg4))
  let grobj = share_draw__mesh(
    list2(
      share_draw__vertex_list3((x1, y1, z1), (x2, y2, z2)),
      share_draw__vertex_list3((x3, y3, z3), (x4, y4, z4)),
    ),
  )
  share_draw__set_gr_object_name(grobj, q_quadrilateral)
  grobj
}

// ---------------------------------------------------------------------------
// Object: 'parametric'
// Usage:
//     parametric(xfun,yfun,par,parmin,parmax)
// Note: similar to draw2d-parametric in plot.lisp

///|
fn share_draw__parametric(
  xfun : Value,
  yfun : Value,
  par : Value,
  parmin : Value,
  parmax : Value,
) -> Value raise {
  with_specials(
    [(q_d_numer, t), (share_draw__q_plot_realpart, symval(share_draw__q_plot_realpart))],
    () => {
      let nticks = get_option(q_d_nticks)
      let tmin = d_float(parmin)
      let tmax = d_float(parmax)
      let ext = ShareDrawExt::new()
      let mut tt = d_float(parmin)
      let eps = num_div(num_sub(tmax, tmin), num_sub(nticks, Fix(1L)))
      if num_lt(tmax, tmin) {
        merr("draw2d (parametric): illegal range", []) |> ignore
      }
      if !share_draw__subsetp_like(
          append(rest(d_listofvars(xfun)), rest(d_listofvars(yfun))),
          list1(par),
        ) {
        merr("draw2d (parametric): non defined variable", []) |> ignore
      }
      set(share_draw__q_plot_realpart, get_option(q_d_draw_realpart)) |> ignore
      let f1 = share_draw__coerce_float_fun(xfun, mk(q_mlist, [par]))
      let f2 = share_draw__coerce_float_fun(yfun, mk(q_mlist, [par]))
      let col = Collector::new()
      while true {
        let xx = d_float(funcall(f1, [tt]))
        let yy = d_float(funcall(f2, [tt]))
        let (xx, yy) = share_draw__transform_point2(xx, yy)
        ext.x(xx)
        ext.y(yy)
        col.add(xx)
        col.add(yy)
        if num_ge(tt, tmax) {
          break
        }
        tt = num_add(tt, eps)
        if num_ge(tt, tmax) {
          tt = tmax
        }
      }
      let result = col.result()
      // update x-y ranges if necessary
      update_ranges_2d(ext.xmin, ext.xmax, ext.ymin, ext.ymax) |> ignore
      share_draw__make_gr_object(
        q_parametric,
        format(Nil, " ~a w l lw ~a lt ~a lc ~a axis ~a", [
          make_obj_title(get_option(q_d_key)),
          get_option(q_d_line_width),
          get_option(q_d_line_type),
          share_draw__rgb(q_d_color),
          axes_to_plot(),
        ]),
        share_draw__lit_groups_2_0,
        list1(share_draw__vec(result)),
      )
    },
  )
}

// ---------------------------------------------------------------------------
// Object: 'polar'
// Usage:
//     polar(radius,ang,minang,maxang)
// This object is constructed as a parametric function

///|
fn share_draw__polar(
  radius : Value,
  ang : Value,
  minang : Value,
  maxang : Value,
) -> Value raise {
  let grobj = share_draw__parametric(
    list([list2(q_mtimes, q_simp), radius, list2(list2(q_p_cos, q_simp), ang)]),
    list([list2(q_mtimes, q_simp), radius, list2(list2(q_p_sin, q_simp), ang)]),
    ang,
    minang,
    maxang,
  )
  share_draw__set_gr_object_name(grobj, q_polar)
  grobj
}

// ---------------------------------------------------------------------------
// Object: 'spherical'
// Usage:
//     spherical(radius,az,minazi,maxazi,zen,minzen,maxzen)
// This object is constructed as a parametric surface in 3d. Functions are
// defined in format r=r(azimuth,zenith), where, normally, azimuth is an
// angle in [0,2*%pi] and zenith in [0,%pi]

///|
fn share_draw__spherical(
  radius : Value,
  azi : Value,
  minazi : Value,
  maxazi : Value,
  zen : Value,
  minzen : Value,
  maxzen : Value,
) -> Value raise {
  let mts = list2(q_mtimes, q_simp)
  let grobj = share_draw__parametric_surface(
    list([
      mts,
      radius,
      list2(list2(q_p_sin, q_simp), zen),
      list2(list2(q_p_cos, q_simp), azi),
    ]),
    list([
      mts,
      radius,
      list2(list2(q_p_sin, q_simp), zen),
      list2(list2(q_p_sin, q_simp), azi),
    ]),
    list([mts, radius, list2(list2(q_p_cos, q_simp), zen)]),
    azi,
    minazi,
    maxazi,
    zen,
    minzen,
    maxzen,
  )
  share_draw__set_gr_object_name(grobj, q_spherical)
  grobj
}

// ---------------------------------------------------------------------------
// Object: 'cylindrical'
// Usage:
//     cylindrical(r,z,minz,maxz,azi,minazi,maxazi)
// This object is constructed as a parametric surface in 3d. Functions are
// defined in format z=z(radius,azimuth), where, normally, azimuth is an
// angle in [0,2*%pi] and r any real

///|
fn share_draw__cylindrical(
  r : Value,
  z : Value,
  minz : Value,
  maxz : Value,
  azi : Value,
  minazi : Value,
  maxazi : Value,
) -> Value raise {
  let grobj = share_draw__parametric_surface(
    list([list2(q_mtimes, q_simp), r, list2(list2(q_p_cos, q_simp), azi)]),
    list([list2(q_mtimes, q_simp), r, list2(list2(q_p_sin, q_simp), azi)]),
    z,
    z,
    minz,
    maxz,
    azi,
    minazi,
    maxazi,
  )
  share_draw__set_gr_object_name(grobj, q_cylindrical)
  grobj
}

// ---------------------------------------------------------------------------
// Object: 'parametric3d'
// Usage:
//     parametric(xfun,yfun,zfun,par1,parmin,parmax)

///|
fn share_draw__parametric3d(
  xfun : Value,
  yfun : Value,
  zfun : Value,
  par1 : Value,
  parmin : Value,
  parmax : Value,
) -> Value raise {
  with_specials(
    [(q_d_numer, t), (share_draw__q_plot_realpart, symval(share_draw__q_plot_realpart))],
    () => {
      let nticks = get_option(q_d_nticks)
      let tmin = d_float(parmin)
      let tmax = d_float(parmax)
      let ext = ShareDrawExt::new()
      let mut tt = tmin
      let eps = num_div(num_sub(tmax, tmin), num_sub(nticks, Fix(1L)))
      let mut count = -1
      if !share_draw__subsetp_like(
          rest(
            d_append(
              list([d_listofvars(xfun), d_listofvars(yfun), d_listofvars(zfun)]),
            ),
          ),
          list1(par1),
        ) {
        merr("draw3d (parametric): non defined variable", []) |> ignore
      }
      set(share_draw__q_plot_realpart, get_option(q_d_draw_realpart)) |> ignore
      check_enhanced3d_model(
        Str("parametric"),
        list([Fix(0L), Fix(1L), Fix(3L), Fix(99L)]),
      )
      |> ignore
      if num_eq(symval(q_ear_draw_enhanced3d_type), Fix(99L)) {
        update_enhanced3d_expression(list([list1(q_mlist), par1])) |> ignore
      }
      if num_lt(tmax, tmin) {
        merr("draw3d (parametric): illegal range", []) |> ignore
      }
      let f1 = share_draw__coerce_float_fun(xfun, mk(q_mlist, [par1]))
      let f2 = share_draw__coerce_float_fun(yfun, mk(q_mlist, [par1]))
      let f3 = share_draw__coerce_float_fun(zfun, mk(q_mlist, [par1]))
      let e3type = to_int(symval(q_ear_draw_enhanced3d_type))
      let ncols = if e3type == 0 { 3 } else { 4 }
      let n = to_int(nticks)
      let result : Array[Value] = Array::make(ncols * n, Fix(0L))
      for _k in 0..<n {
        let xx = funcall(f1, [tt])
        let yy = funcall(f2, [tt])
        let zz = funcall(f3, [tt])
        let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
        ext.x(xx)
        ext.y(yy)
        ext.z(zz)
        count = count + 1
        result[count] = xx
        count = count + 1
        result[count] = yy
        count = count + 1
        result[count] = zz
        // check texture model
        if e3type == 1 || e3type == 99 {
          count = count + 1
          result[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [tt])
        } else if e3type == 3 {
          count = count + 1
          result[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [xx, yy, zz])
        }
        tt = num_add(tt, eps)
      }
      // update x-y ranges if necessary
      update_ranges_3d(
        ext.xmin,
        ext.xmax,
        ext.ymin,
        ext.ymax,
        ext.zmin,
        ext.zmax,
      )
      |> ignore
      share_draw__make_gr_object(
        q_parametric,
        format(Nil, " ~a w l lw ~a lt ~a lc ~a", [
          make_obj_title(get_option(q_d_key)),
          get_option(q_d_line_width),
          get_option(q_d_line_type),
          if e3type > 0 {
            Str("palette")
          } else {
            share_draw__rgb(q_d_color)
          },
        ]),
        list1(list2(int(ncols), Fix(0L))),
        list1(vector(result)),
      )
    },
  )
}

// ---------------------------------------------------------------------------
// Object: 'parametric_surface'
// Usage:
//     parametric_surface(xfun,yfun,zfun,par1,par1min,par1max,par2,par2min,par2max)

///|
fn share_draw__parametric_surface(
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
  with_specials(
    [(q_d_numer, t), (share_draw__q_plot_realpart, symval(share_draw__q_plot_realpart))],
    () => {
      let ugrid = get_option(q_d_xu_grid)
      let vgrid = get_option(q_d_yv_grid)
      let umin = d_float(par1min)
      let umax = d_float(par1max)
      let vmin = d_float(par2min)
      let vmax = d_float(par2max)
      let ext = ShareDrawExt::new()
      let ueps = num_div(num_sub(umax, umin), num_sub(ugrid, Fix(1L)))
      let veps = num_div(num_sub(vmax, vmin), num_sub(vgrid, Fix(1L)))
      let nu = to_int(ugrid) + 1
      let nv = to_int(vgrid) + 1
      let mut count = -1
      if !share_draw__subsetp_like(
          rest(
            d_append(
              list([d_listofvars(xfun), d_listofvars(yfun), d_listofvars(zfun)]),
            ),
          ),
          list2(par1, par2),
        ) {
        merr("draw3d (parametric_surface): non defined variable", []) |> ignore
      }
      set(share_draw__q_plot_realpart, get_option(q_d_draw_realpart)) |> ignore
      check_enhanced3d_model(
        Str("parametric_surface"),
        list([Fix(0L), Fix(2L), Fix(3L), Fix(99L)]),
      )
      |> ignore
      if num_eq(symval(q_ear_draw_enhanced3d_type), Fix(99L)) {
        update_enhanced3d_expression(list([list1(q_mlist), par1, par2]))
        |> ignore
      }
      if num_lt(umax, umin) || num_lt(vmax, vmin) {
        merr("draw3d (parametric_surface): illegal range", []) |> ignore
      }
      let f1 = share_draw__coerce_float_fun(xfun, mk(q_mlist, [par1, par2]))
      let f2 = share_draw__coerce_float_fun(yfun, mk(q_mlist, [par1, par2]))
      let f3 = share_draw__coerce_float_fun(zfun, mk(q_mlist, [par1, par2]))
      let e3type = to_int(symval(q_ear_draw_enhanced3d_type))
      let ncols = if e3type == 0 { 3 } else { 4 }
      let result : Array[Value] = Array::make(ncols * nu * nv, Fix(0L))
      let mut vv = vmin
      for _j in 0..<nv {
        let mut uu = umin
        for _i in 0..<nu {
          let xx = funcall(f1, [uu, vv])
          let yy = funcall(f2, [uu, vv])
          let zz = funcall(f3, [uu, vv])
          let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
          ext.x(xx)
          ext.y(yy)
          ext.z(zz)
          count = count + 1
          result[count] = xx
          count = count + 1
          result[count] = yy
          count = count + 1
          result[count] = zz
          // check texture model
          if e3type == 2 || e3type == 99 {
            count = count + 1
            result[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [uu, vv])
          } else if e3type == 3 {
            count = count + 1
            result[count] = funcall(symval(q_ear_draw_enhanced3d_fun), [
              xx, yy, zz,
            ])
          }
          uu = num_add(uu, ueps)
          if num_gt(uu, umax) {
            uu = umax
          }
        }
        vv = num_add(vv, veps)
        if num_gt(vv, vmax) {
          vv = vmax
        }
      }
      // update x-y-z ranges if necessary
      update_ranges_3d(
        ext.xmin,
        ext.xmax,
        ext.ymin,
        ext.ymax,
        ext.zmin,
        ext.zmax,
      )
      |> ignore
      share_draw__make_gr_object(
        q_parametric_surface,
        format(Nil, " ~a w ~a lw ~a lt ~a lc ~a", [
          make_obj_title(get_option(q_d_key)),
          Str(if e3type > 0 { "pm3d" } else { "l" }),
          get_option(q_d_line_width),
          get_option(q_d_line_type),
          share_draw__rgb(q_d_color),
        ]),
        // ncols is 4 or 3, depending on colored 4th dimension or not
        list1(list2(int(ncols), int(nu))),
        list1(vector(result)),
      )
    },
  )
}

// ---------------------------------------------------------------------------
// Object: 'tube'
// Usage:
//     tube(xfun,yfun,zfun,rad,par1,parmin,parmax)

///|
fn share_draw__tube(
  xfun : Value,
  yfun : Value,
  zfun : Value,
  rad : Value,
  par1 : Value,
  parmin : Value,
  parmax : Value,
) -> Value raise {
  with_special(q_d_numer, t, () => {
    let ugrid = get_option(q_d_xu_grid)
    let vgrid = get_option(q_d_yv_grid)
    let tmin = d_float(parmin)
    let tmax = d_float(parmax)
    let vmax : Value = Flo(6.283185307179586) // = float(2*%pi)
    let ext = ShareDrawExt::new()
    let teps = num_div(num_sub(tmax, tmin), num_sub(ugrid, Fix(1L)))
    let veps = num_div(vmax, num_sub(vgrid, Fix(1L)))
    let mut tt = tmin
    let mut circ : Value = Nil
    let mut result : Value = Nil
    let mut cx : Value = Nil
    let mut cy : Value = Nil
    let mut cz : Value = Nil
    let mut nx : Value = Nil
    let mut ny : Value = Nil
    let mut nz : Value = Nil
    let mut uxold : Value = Nil
    let mut uyold : Value = Nil
    let mut uzold : Value = Nil
    if num_lt(tmax, tmin) {
      merr("draw3d (tube): illegal range", []) |> ignore
    }
    if !share_draw__subsetp_like(
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
        list1(par1),
      ) {
      merr("draw3d (tube): non defined variable", []) |> ignore
    }
    check_enhanced3d_model(
      Str("tube"),
      list([Fix(0L), Fix(1L), Fix(3L), Fix(99L)]),
    )
    |> ignore
    if num_eq(symval(q_ear_draw_enhanced3d_type), Fix(99L)) {
      update_enhanced3d_expression(list([list1(q_mlist), par1])) |> ignore
    }
    let f1 = share_draw__coerce_float_fun(xfun, mk(q_mlist, [par1]))
    let f2 = share_draw__coerce_float_fun(yfun, mk(q_mlist, [par1]))
    let f3 = share_draw__coerce_float_fun(zfun, mk(q_mlist, [par1]))
    let e3type = to_int(symval(q_ear_draw_enhanced3d_type))
    let ncols = if e3type == 0 { 3 } else { 4 }
    let radius = share_draw__coerce_float_fun(rad, mk(q_mlist, [par1]))
    let nvgrid = to_int(vgrid)
    // Macro CHECK-TUBE-EXTREME.
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
        if e3type == 0 {
          circ = list([cxx, cyy, czz])
        } else if e3type == 1 || e3type == 99 {
          circ = list([
            cxx,
            cyy,
            czz,
            funcall(symval(q_ear_draw_enhanced3d_fun), [tt]),
          ])
        } else if e3type == 3 {
          circ = list([
            cxx,
            cyy,
            czz,
            funcall(symval(q_ear_draw_enhanced3d_fun), [cxx, cyy, czz]),
          ])
        }
        for _k in 0..<nvgrid {
          result = append(result, circ)
        }
      }
    }
    while true {
      // calculate center and radius of circle
      if num_eq(tt, tmin) {
        // 1st iteration
        cx = funcall(f1, [tt])
        cy = funcall(f2, [tt])
        cz = funcall(f3, [tt])
        let ttnext = num_add(tt, teps)
        check_tube_extreme(1, cx, cy, cz)
        nx = num_sub(funcall(f1, [ttnext]), cx)
        ny = num_sub(funcall(f2, [ttnext]), cy)
        nz = num_sub(funcall(f3, [ttnext]), cz)
      } else {
        // all next iterations along the parametric curve
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
      let mut module = lsqrt(
        num_sum([num_mul(nx, nx), num_mul(ny, ny), num_mul(nz, nz)]),
      )
      nx = num_div(nx, module)
      ny = num_div(ny, module)
      nz = num_div(nz, module)
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
      module = lsqrt(
        num_sum([num_mul(ux0, ux0), num_mul(uy0, uy0), num_mul(uz0, uz0)]),
      )
      let mut ux = num_div(ux0, module)
      let mut uy = num_div(uy0, module)
      let mut uz = num_div(uz0, module)
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
      circ = Nil
      for _i in 0..<nvgrid {
        let rcos = num_mul(r, lcos(vv))
        let rsin = num_mul(r, lsin(vv))
        let xx = num_sum([cx, num_mul(rcos, ux), num_mul(rsin, vx)])
        let yy = num_sum([cy, num_mul(rcos, uy), num_mul(rsin, vy)])
        let zz = num_sum([cz, num_mul(rcos, uz), num_mul(rsin, vz)])
        let (xx, yy, zz) = share_draw__transform_point3(xx, yy, zz)
        ext.x(xx)
        ext.y(yy)
        ext.z(zz)
        // check texture model
        if e3type == 0 {
          circ = cons(list([xx, yy, zz]), circ)
        } else if e3type == 1 || e3type == 99 {
          circ = cons(
            list([xx, yy, zz, funcall(symval(q_ear_draw_enhanced3d_fun), [tt])]),
            circ,
          )
        } else if e3type == 3 {
          circ = cons(
            list([
              xx,
              yy,
              zz,
              funcall(symval(q_ear_draw_enhanced3d_fun), [xx, yy, zz]),
            ]),
            circ,
          )
        }
        vv = num_add(vv, veps)
        if num_gt(vv, vmax) {
          vv = vmax
        }
      }
      result = append(result, share_draw__apply_append(circ))
      if num_ge(tt, tmax) {
        break
      }
      tt = num_add(tt, teps)
      if num_gt(tt, tmax) {
        tt = tmax
      }
    }
    check_tube_extreme(2, cx, cy, cz)
    // update x-y-z ranges
    update_ranges_3d(ext.xmin, ext.xmax, ext.ymin, ext.ymax, ext.zmin, ext.zmax)
    |> ignore
    share_draw__make_gr_object(
      q_tube,
      format(Nil, " ~a w ~a lw ~a lt ~a lc ~a", [
        make_obj_title(get_option(q_d_key)),
        Str(if e3type > 0 { "pm3d" } else { "l" }),
        get_option(q_d_line_width),
        get_option(q_d_line_type),
        share_draw__rgb(q_d_color),
      ]),
      list1(list2(int(ncols), vgrid)),
      list1(share_draw__vec(result)),
    )
  })
}

///|
/// (apply #'append lists)
fn share_draw__apply_append(lists : Value) -> Value {
  let col = Collector::new()
  for l in lists.iter() {
    for x in l.iter() {
      col.add(x)
    }
  }
  col.result()
}

// ---------------------------------------------------------------------------
// Object: 'image'
// Usages:
//     image(matrix_of_numbers,x0,y0,width,height)
//     image(matrix_of_[r,g,b],x0,y0,width,height)
//     image(picture_object,x0,y0,width,height)

///|
fn share_draw__image(
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
  let mut result : Value = Nil
  let mut n = 0
  if d_matrixp(mat).truthy() {
    let nrows = length(cdr(mat))
    let ncols = length(cdadr(mat))
    let dx = num_div(fwidth, int(ncols))
    let dy = num_div(fheight, int(nrows))
    n = if !d_listp(car(cdadr(mat))).truthy() {
      // it's a matrix of reals: 3 numbers to be sent to gnuplot: x,y,value
      3
    } else {
      // 5 numbers to be sent: x,y,r,g,b
      5
    }
    let arr : Array[Value] = Array::make(n * nrows * ncols, Flo(0.0))
    let mut yi = num_add(num_add(fy0, height), num_mul(dy, Flo(-0.5)))
    let mut counter = -1
    for row in cdr(mat).iter() {
      let mut xi = num_add(fx0, num_mul(dx, Flo(0.5)))
      for col in cdr(row).iter() {
        counter = counter + 1
        arr[counter] = xi
        counter = counter + 1
        arr[counter] = yi
        if n == 3 {
          counter = counter + 1
          arr[counter] = d_float(col)
        } else {
          let colors = cdr(col)
          counter = counter + 1
          arr[counter] = d_float(car(colors))
          counter = counter + 1
          arr[counter] = d_float(cadr(colors))
          counter = counter + 1
          arr[counter] = d_float(caddr(colors))
        }
        xi = num_add(xi, dx)
      }
      yi = num_sub(yi, dy)
    }
    result = vector(arr)
  } else if d_picturep(mat).truthy() {
    let nrows = to_int(nth(3, mat)) // picture height
    let ncols = to_int(nth(2, mat)) // picture width
    let dx = num_div(fwidth, int(ncols))
    let dy = num_div(fheight, int(nrows))
    let kind = nth(1, mat)
    if equal(kind, q_d_level) {
      // gray level picture: 3 numbers to be sent to gnuplot: x,y,value
      n = 3
    } else if equal(kind, q_d_rgb) {
      // 5 numbers to be sent: x,y,r,g,b
      n = 5
    } else if equal(kind, q_d_rgb_alpha) {
      // 6 numbers to be sent: x,y,r,g,b,t
      n = 6
    } else {
      merr("image: picture type ~M not recognized.", [kind]) |> ignore
    }
    let arr : Array[Value] = Array::make(n * nrows * ncols, Flo(0.0))
    let mut yi = num_add(num_add(fy0, height), num_mul(dy, Flo(-0.5)))
    let mut count1 = -1
    let mut count2 = -1
    let data = nth(4, mat)
    for _r in 0..<nrows {
      let mut xi = num_add(fx0, num_mul(dx, Flo(0.5)))
      for _c in 0..<ncols {
        count1 = count1 + 1
        arr[count1] = xi
        count1 = count1 + 1
        arr[count1] = yi
        for _q in 3..=n {
          count1 = count1 + 1
          count2 = count2 + 1
          arr[count1] = d_float(aref1(data, count2))
        }
        xi = num_add(xi, dx)
      }
      yi = num_sub(yi, dy)
    }
    result = vector(arr)
  } else {
    merr("draw2d (image): Argument not recognized", []) |> ignore
  }
  // update x-y ranges if necessary
  update_ranges_2d(fx0, num_add(fx0, fwidth), fy0, num_add(fy0, fheight))
  |> ignore
  share_draw__make_gr_object(
    q_image,
    match n {
      3 => format(Nil, " t '' w image", [])
      5 => format(Nil, " t '' w rgbimage", [])
      6 => format(Nil, " t '' w rgbalpha", [])
      _ => Nil
    },
    match n {
      // numbers are sent to gnuplot in groups of 3, 5 or 6, no blank lines
      3 => list1(list2(Fix(3L), Fix(0L)))
      5 => list1(list2(Fix(5L), Fix(0L)))
      6 => list1(list2(Fix(6L), Fix(0L)))
      _ => Nil
    },
    list1(result),
  )
}

///|
/// Macro WRITE-PALETTE-CODE.
fn share_draw__write_palette_code() -> Value raise {
  let pal = get_option(q_d_palette)
  if equal(pal, q_d_gray) {
    format(Nil, "set palette gray~%", [])
  } else if equal(pal, q_d_color) {
    format(Nil, "set palette rgbformulae 7,5,15~%", [])
  } else if listp(pal) &&
    length(pal) == 3 &&
    every(x => integerp(x) && num_le(num_abs(x), Fix(36L)), pal) {
    format(Nil, "set palette rgbformulae ~a,~a,~a~%", [
      car(pal),
      cadr(pal),
      caddr(pal),
    ])
  } else if listp(pal) && every(x => listp(x) && length(x) == 3, pal) {
    let n = length(pal)
    Str(
      with_output_to_string(stream => {
        format(stream, "set palette defined ( \\~%", []) |> ignore
        for k in 0..<n {
          let triplete = nth(k, pal)
          format(stream, "  ~a ~a ~a ~a ", [
            int(k),
            car(triplete),
            cadr(triplete),
            caddr(triplete),
          ])
          |> ignore
          if k + 1 == n {
            format(stream, ")~%", []) |> ignore
          } else {
            format(stream, ", \\~%", []) |> ignore
          }
        }
      }),
    )
  } else {
    merr("draw: illegal palette description", [])
  }
}

///|
/// Resolve suggest(opt = val) markers in a flattened scene list. A
/// suggested option is applied only when that option is not also set
/// explicitly elsewhere in the same scene (in any position), so scene
/// builders can propose a default xrange/yrange/... without clobbering a
/// user setting.
fn resolve_suggestions(largs : Value) -> Value raise {
  let mut explicit : Value = Nil
  let mut result : Value = Nil
  // Collect options explicitly set.
  for x in largs.iter() {
    if consp(x) && eq(caar(x), q_mequal) {
      explicit = cons(cadr(x), explicit)
    }
  }
  // Unpack instances of suggest(opt = val) to opt = val if opt isn't
  // explicity set.
  for x in largs.iter() {
    if consp(x) &&
      eq(caar(x), q_p_suggest) &&
      consp(cadr(x)) &&
      eq(car(car(cadr(x))), q_mequal) {
      let inner = cadr(x)
      if !memq(cadr(inner), explicit).truthy() {
        result = cons(inner, result)
      }
    } else {
      result = cons(x, result)
    }
  }
  nreverse(result)
}

///|
/// Concatenation of the strings (nil counts as an empty sequence).
fn share_draw__concat(parts : Array[Value]) -> Value {
  let sb = StringBuilder::new()
  for p in parts {
    match p {
      Str(s) => sb.write_string(s)
      _ => ()
    }
  }
  Str(sb.to_string())
}

///|
/// The "set ~a" / "unset ~a" pair of a boolean option.
fn share_draw__set_unset(opt : Value, yes : String, no : String) -> Value raise {
  Str(if get_option(opt).truthy() { yes } else { no })
}

///|
/// Detect objects to be plotted and update option values: the objects of
/// a scene, built with the constructors in TABLE.
fn share_draw__scene_objects(
  args : Value,
  table : Value,
  what : String,
) -> Value raise {
  let mut objects : Value = Nil
  ini_gr_options() |> ignore
  ini_local_option_variables() |> ignore
  user_defaults() |> ignore
  let largs = resolve_suggestions(share_draw__listify_arguments(args))
  // update option values and detect objects to be plotted
  for x in largs.iter() {
    if equal(d_op(x), Str("=")) {
      update_gr_option(d_lhs(x), d_rhs(x)) |> ignore
    } else {
      let aux = caar(x)
      if !(gethash(aux, symval(table)) is Nil) {
        objects = append(
          objects,
          list1(apply(gethash(aux, symval(table)), rest(x))),
        )
      } else {
        merr("draw: " + what + " graphic object not recognized, ~M", [aux])
        |> ignore
      }
    }
  }
  objects
}

///|
/// The ticks / grid lines of a scene: ~d as in Lisp's format.
fn share_draw__tics(
  opt : Value,
  rot : Value,
  axis : Value,
  name : String,
) -> Value raise {
  if get_option(opt) is Nil {
    format(Nil, "unset " + name + "~%", [])
  } else {
    format(Nil, "set " + name + " ~a ~a ~a~%", [
      Str(if get_option(rot).truthy() { "rotate" } else { "norotate" }),
      Str(if get_option(axis).truthy() { "axis" } else { "border" }),
      get_option(opt),
    ])
  }
}

///|
fn make_scene_2d(args : Value) -> Value raise {
  let objects = share_draw__scene_objects(
    args,
    q_ear_2d_graphic_objects,
    "2D",
  )
  // save in plotcmd the gnuplot preamble
  let parts : Array[Value] = []
  if !(
      symval(q_ear_multiplot_is_active).truthy() ||
      member(
        get_option(q_d_terminal),
        list([
          q_d_eps, q_d_epslatex, q_d_epslatex_standalone, q_d_cairolatex_pdf,
          q_d_cairolatex_pdf_standalone,
        ]),
      ).truthy()
    ) {
    parts.push(
      format(Nil, "set obj 1 fc rgb '~a' fs solid 1.0 noborder ~%", [
        get_option(q_d_background_color),
      ]),
    )
  }
  parts.push(
    if equal(get_option(q_d_proportional_axes), q_d_none) {
      format(Nil, "set size noratio~%", [])
    } else {
      format(Nil, "set size ratio -1~%", [])
    },
  )
  // this let statement is to prevent error messages from gnuplot when the
  // amplitude of the ranges equals zero
  {
    let mut xi = first(get_option(q_d_xrange))
    let mut xf = second(get_option(q_d_xrange))
    let mut yi = first(get_option(q_d_yrange))
    let mut yf = second(get_option(q_d_yrange))
    let mut x2i = first(get_option(q_d_xrange_secondary))
    let mut x2f = second(get_option(q_d_xrange_secondary))
    let mut y2i = first(get_option(q_d_yrange_secondary))
    let mut y2f = second(get_option(q_d_yrange_secondary))
    let d : Value = Flo(0.01)
    if get_option(q_d_xrange).truthy() && near_equal(xi, xf).truthy() {
      xi = num_sub(xi, d)
      xf = num_add(xf, d)
    }
    if get_option(q_d_xrange_secondary).truthy() &&
      near_equal(x2i, x2f).truthy() {
      x2i = num_sub(x2i, d)
      x2f = num_add(x2f, d)
    }
    if get_option(q_d_yrange).truthy() && near_equal(yi, yf).truthy() {
      yi = num_sub(yi, d)
      yf = num_add(yf, d)
    }
    if get_option(q_d_yrange_secondary).truthy() &&
      near_equal(y2i, y2f).truthy() {
      y2i = num_sub(y2i, d)
      y2f = num_add(y2f, d)
    }
    parts.push(
      format(Nil, "~a~a~a~a", [
        if get_option(q_d_xrange).truthy() {
          format(Nil, "set xrange [~a:~a]~%", [xi, xf])
        } else {
          Str("")
        },
        if get_option(q_d_xrange_secondary).truthy() {
          format(Nil, "set x2range [~a:~a]~%", [x2i, x2f])
        } else {
          Str("")
        },
        if get_option(q_d_yrange).truthy() {
          format(Nil, "set yrange [~a:~a]~%", [yi, yf])
        } else {
          Str("")
        },
        if get_option(q_d_yrange_secondary).truthy() {
          format(Nil, "set y2range [~a:~a]~%", [y2i, y2f])
        } else {
          Str("")
        },
      ]),
    )
  }
  parts.push(
    if get_option(q_d_cbrange).truthy() {
      format(Nil, "set cbrange [~a:~a]~%", [
        first(get_option(q_d_cbrange)),
        second(get_option(q_d_cbrange)),
      ])
    } else {
      format(Nil, "set cbrange [*:*]~%", [])
    },
  )
  parts.push(
    format(Nil, "~a~%", [
      share_draw__set_unset(q_d_logx, "set logscale x", "unset logscale x"),
    ]),
  )
  parts.push(
    format(Nil, "~a~%", [
      share_draw__set_unset(q_d_logx_secondary, "set logscale x2", "unset logscale x2"),
    ]),
  )
  parts.push(
    format(Nil, "~a~%", [
      share_draw__set_unset(q_d_logy, "set logscale y", "unset logscale y"),
    ]),
  )
  parts.push(
    format(Nil, "~a~%", [
      share_draw__set_unset(q_d_logy_secondary, "set logscale y2", "unset logscale y2"),
    ]),
  )
  parts.push(
    format(Nil, "~a~%", [
      share_draw__set_unset(q_d_logcb, "set logscale cb", "unset logscale cb"),
    ]),
  )
  parts.push(
    if equal(car(get_option(q_d_grid)), Fix(0L)) {
      format(Nil, "unset grid~%", [])
    } else {
      format(
        Nil,
        "set grid xtics ytics mxtics mytics~%set mxtics ~d~%set mytics ~d~%",
        [car(get_option(q_d_grid)), cadr(get_option(q_d_grid))],
      )
    },
  )
  parts.push(format(Nil, "set title '~a'~%", [get_option(q_d_title)]))
  parts.push(format(Nil, "set xlabel '~a'~%", [get_option(q_d_xlabel)]))
  parts.push(
    format(Nil, "set x2label '~a'~%", [get_option(q_d_xlabel_secondary)]),
  )
  parts.push(format(Nil, "set ylabel '~a'~%", [get_option(q_d_ylabel)]))
  parts.push(
    format(Nil, "set y2label '~a'~%", [get_option(q_d_ylabel_secondary)]),
  )
  {
    let mut suma = 0
    if get_option(q_d_axis_bottom).truthy() {
      suma = suma + 1
    }
    if get_option(q_d_axis_left).truthy() {
      suma = suma + 2
    }
    if get_option(q_d_axis_top).truthy() {
      suma = suma + 4
    }
    if get_option(q_d_axis_right).truthy() {
      suma = suma + 8
    }
    parts.push(format(Nil, "set border ~a~%", [int(suma)]))
  }
  parts.push(
    if get_option(q_d_key_pos).truthy() {
      format(Nil, "set key ~a~%", [get_option(q_d_key_pos)])
    } else {
      format(Nil, "set key top right~%", [])
    },
  )
  parts.push(share_draw__zeroaxis(q_d_xaxis, "x"))
  parts.push(share_draw__zeroaxis(q_d_yaxis, "y"))
  parts.push(
    if get_option(q_d_xtics_secondary) is Nil {
      format(Nil, "unset x2tics~%set xtics nomirror~%", [])
    } else {
      format(Nil, "set x2tics ~a ~a ~a~%", [
        Str(
          if get_option(q_d_xtics_secondary_rotate).truthy() {
            "rotate"
          } else {
            "norotate"
          },
        ),
        Str(
          if get_option(q_d_xtics_secondary_axis).truthy() {
            "axis"
          } else {
            "border"
          },
        ),
        get_option(q_d_xtics_secondary),
      ])
    },
  )
  parts.push(share_draw__tics(q_d_xtics, q_d_xtics_rotate, q_d_xtics_axis, "xtics"))
  parts.push(
    if get_option(q_d_ytics_secondary) is Nil {
      format(Nil, "unset y2tics~%set ytics nomirror~%", [])
    } else {
      format(Nil, "set ytics nomirror~%set y2tics ~a ~a ~a~%", [
        Str(
          if get_option(q_d_ytics_secondary_rotate).truthy() {
            "rotate"
          } else {
            "norotate"
          },
        ),
        Str(
          if get_option(q_d_ytics_secondary_axis).truthy() {
            "axis"
          } else {
            "border"
          },
        ),
        get_option(q_d_ytics_secondary),
      ])
    },
  )
  parts.push(share_draw__tics(q_d_ytics, q_d_ytics_rotate, q_d_ytics_axis, "ytics"))
  parts.push(
    if get_option(q_d_cbtics) is Nil {
      format(Nil, "unset cbtics~%", [])
    } else {
      format(Nil, "set cbtics ~a~%", [get_option(q_d_cbtics)])
    },
  )
  parts.push(
    if get_option(q_d_colorbox).truthy() {
      format(Nil, "set colorbox~%", [])
    } else {
      format(Nil, "unset colorbox~%", [])
    },
  )
  parts.push(
    format(Nil, "set cblabel '~a'~%", [
      if stringp(get_option(q_d_colorbox)) {
        get_option(q_d_colorbox)
      } else {
        Str("")
      },
    ]),
  )
  parts.push(share_draw__write_palette_code())
  if lstring(get_option(q_d_user_preamble)) != "" {
    parts.push(format(Nil, "~a~%", [get_option(q_d_user_preamble)]))
  }
  let plotcmd = share_draw__concat(parts)
  // scene allocation
  set(
    q_ear_allocations,
    cons(get_option(q_d_allocation), symval(q_ear_allocations)),
  )
  |> ignore
  // scene description: (dimensions, gnuplot preamble in string format, list
  // of objects)
  list([Fix(2L), plotcmd, objects])
}

///|
/// The x/y/z zero axis lines of a scene.
fn share_draw__zeroaxis(opt : Value, axis : String) -> Value raise {
  if get_option(opt).truthy() {
    let w = if axis == "x" {
      q_d_xaxis_width
    } else if axis == "y" {
      q_d_yaxis_width
    } else {
      q_d_zaxis_width
    }
    let ty = if axis == "x" {
      q_d_xaxis_type
    } else if axis == "y" {
      q_d_yaxis_type
    } else {
      q_d_zaxis_type
    }
    let c = if axis == "x" {
      q_d_xaxis_color
    } else if axis == "y" {
      q_d_yaxis_color
    } else {
      q_d_zaxis_color
    }
    format(Nil, "set " + axis + "zeroaxis lw ~a lt ~a lc ~a~%", [
      get_option(w),
      get_option(ty),
      share_draw__rgb(c),
    ])
  } else {
    format(Nil, "unset " + axis + "zeroaxis~%", [])
  }
}

///|
/// This function builds a 3d scene by calling the graphic objects
/// constructors.
fn make_scene_3d(args : Value) -> Value raise {
  let objects = share_draw__scene_objects(
    args,
    q_ear_3d_graphic_objects,
    "3D",
  )
  // save in plotcmd the gnuplot preamble
  let parts : Array[Value] = []
  // background rectangle
  parts.push(
    format(
      Nil,
      "set style rectangle fillcolor rgb '~a' fs solid 1.0 noborder~%",
      [get_option(q_d_background_color)],
    ),
  )
  // this let statement is to prevent error messages in gnuplot when the
  // amplitude of the ranges equals zero
  {
    let mut xi = first(get_option(q_d_xrange))
    let mut xf = second(get_option(q_d_xrange))
    let mut yi = first(get_option(q_d_yrange))
    let mut yf = second(get_option(q_d_yrange))
    let mut zi = first(get_option(q_d_zrange))
    let mut zf = second(get_option(q_d_zrange))
    let d : Value = Flo(0.01)
    if near_equal(xi, xf).truthy() {
      xi = num_sub(xi, d)
      xf = num_add(xf, d)
    }
    if near_equal(yi, yf).truthy() {
      yi = num_sub(yi, d)
      yf = num_add(yf, d)
    }
    if near_equal(zi, zf).truthy() {
      zi = num_sub(zi, d)
      zf = num_add(zf, d)
    }
    parts.push(
      format(
        Nil,
        "set xrange [~a:~a]~%set yrange [~a:~a]~%set zrange [~a:~a]~%",
        [xi, xf, yi, yf, zi, zf],
      ),
    )
  }
  parts.push(
    if get_option(q_d_cbrange).truthy() {
      format(Nil, "set cbrange [~a:~a]~%", [
        first(get_option(q_d_cbrange)),
        second(get_option(q_d_cbrange)),
      ])
    } else {
      format(Nil, "set cbrange [*:*]~%", [])
    },
  )
  let contour = get_option(q_d_contour)
  let levels = get_option(q_d_contour_levels)
  if eq(contour, q_d_surface) {
    parts.push(
      format(Nil, "set contour surface~%set cntrparam levels ~a~%", [levels]),
    )
  } else if eq(contour, q_d_base) {
    parts.push(
      format(Nil, "set contour base~%set cntrparam levels ~a~%", [levels]),
    )
  } else if eq(contour, q_d_both) {
    parts.push(
      format(Nil, "set contour both~%set cntrparam levels ~a~%", [levels]),
    )
  } else if eq(contour, q_d_map) {
    parts.push(
      format(
        Nil,
        "set contour base~%unset surface~%set cntrparam levels ~a~%",
        [levels],
      ),
    )
  }
  parts.push(format(Nil, "set title '~a'~%", [get_option(q_d_title)]))
  parts.push(format(Nil, "set xlabel '~a'~%", [get_option(q_d_xlabel)]))
  parts.push(format(Nil, "set ylabel '~a'~%", [get_option(q_d_ylabel)]))
  parts.push(
    if lstring(get_option(q_d_zlabel)).length() < 5 {
      format(Nil, "set zlabel '~a'~%", [get_option(q_d_zlabel)])
    } else {
      format(Nil, "set zlabel '~a' rotate~%", [get_option(q_d_zlabel)])
    },
  )
  parts.push(format(Nil, "set datafile missing 'NIL'~%", []))
  parts.push(
    format(Nil, "~a~%", [
      share_draw__set_unset(q_d_logx, "set logscale x", "unset logscale x"),
    ]),
  )
  parts.push(
    format(Nil, "~a~%", [
      share_draw__set_unset(q_d_logy, "set logscale y", "unset logscale y"),
    ]),
  )
  parts.push(
    format(Nil, "~a~%", [
      share_draw__set_unset(q_d_logz, "set logscale z", "unset logscale z"),
    ]),
  )
  parts.push(
    if get_option(q_d_key_pos).truthy() {
      format(Nil, "set key ~a~%", [get_option(q_d_key_pos)])
    } else {
      format(Nil, "set key top center~%", [])
    },
  )
  parts.push(
    format(Nil, "~a~%", [
      share_draw__set_unset(q_d_logcb, "set logscale cb", "unset logscale cb"),
    ]),
  )
  parts.push(
    if equal(car(get_option(q_d_grid)), Fix(0L)) {
      format(Nil, "unset grid~%", [])
    } else {
      format(
        Nil,
        "set grid xtics ytics ztics mxtics mytics mztics~%set mxtics ~d~%set mytics ~d~%",
        [car(get_option(q_d_grid)), cadr(get_option(q_d_grid))],
      )
    },
  )
  parts.push(share_draw__zeroaxis(q_d_xaxis, "x"))
  parts.push(share_draw__zeroaxis(q_d_yaxis, "y"))
  parts.push(share_draw__zeroaxis(q_d_zaxis, "z"))
  parts.push(share_draw__tics(q_d_xtics, q_d_xtics_rotate, q_d_xtics_axis, "xtics"))
  parts.push(share_draw__tics(q_d_ytics, q_d_ytics_rotate, q_d_ytics_axis, "ytics"))
  parts.push(share_draw__tics(q_d_ztics, q_d_ztics_rotate, q_d_ztics_axis, "ztics"))
  parts.push(
    if get_option(q_d_cbtics) is Nil {
      format(Nil, "unset cbtics~%", [])
    } else {
      format(Nil, "set cbtics ~a~%", [get_option(q_d_cbtics)])
    },
  )
  parts.push(
    if eql(get_option(q_d_contour), q_d_map) || eql(get_option(q_d_view), q_d_map) {
      format(Nil, "set view map~%~a~%", [
        Str(
          if equal(get_option(q_d_proportional_axes), q_d_none) {
            "set size noratio"
          } else {
            "set size ratio -1"
          },
        ),
      ])
    } else {
      let pa = get_option(q_d_proportional_axes)
      format(Nil, "set view ~a, ~a, 1, 1~%~a~%", [
        first(get_option(q_d_view)),
        second(get_option(q_d_view)),
        Str(
          if eq(pa, q_d_xy) {
            "set view equal xy"
          } else if eq(pa, q_d_xyz) {
            "set view equal xyz"
          } else {
            ""
          },
        ),
      ])
    },
  )
  if !get_option(q_d_axis_3d).truthy() {
    parts.push(
      format(Nil, "set border 0~%unset xtics~%unset ytics~%unset ztics~%", []),
    )
  }
  if !(get_option(q_d_enhanced3d) is Nil) {
    parts.push(
      if get_option(q_d_wired_surface) is Nil {
        format(Nil, "set pm3d at s ~a explicit~%", [
          get_option(q_d_interpolate_color),
        ])
      } else {
        format(
          Nil,
          "set style line 1 lt 1 lw 1 lc rgb '#000000'~%set pm3d at s depthorder explicit hidden3d 1~%",
          [],
        )
      },
    )
  }
  if get_option(q_d_surface_hide).truthy() {
    parts.push(format(Nil, "set hidden3d nooffset~%", []))
  }
  if get_option(q_d_xyplane).truthy() {
    parts.push(format(Nil, "set xyplane at ~a~%", [get_option(q_d_xyplane)]))
  }
  parts.push(
    if get_option(q_d_colorbox).truthy() {
      format(Nil, "set colorbox~%", [])
    } else {
      format(Nil, "unset colorbox~%", [])
    },
  )
  parts.push(
    format(Nil, "set cblabel '~a'~%", [
      if stringp(get_option(q_d_colorbox)) {
        get_option(q_d_colorbox)
      } else {
        Str("")
      },
    ]),
  )
  parts.push(share_draw__write_palette_code())
  if lstring(get_option(q_d_user_preamble)) != "" {
    parts.push(format(Nil, "~a~%", [get_option(q_d_user_preamble)]))
  }
  let plotcmd = share_draw__concat(parts)
  // scene allocation
  set(
    q_ear_allocations,
    cons(get_option(q_d_allocation), symval(q_ear_allocations)),
  )
  |> ignore
  // scene description: (dimensions, gnuplot preamble in string format, list
  // of objects)
  list([Fix(3L), plotcmd, objects])
}

///|
/// Macro WRITE-SUBARRAY: the elements of ARR (a vector), each followed by
/// a space, then a newline.
fn share_draw__write_subarray(arr : Array[Value], str : Value) -> Unit raise {
  let sb = StringBuilder::new()
  for z in arr {
    sb.write_string(format_to_string("~a ", [z]))
  }
  format(str, "~a~%", [Str(sb.to_string())]) |> ignore
}

///|
/// The elements of a vector.
fn share_draw__vec_data(v : Value) -> Array[Value] raise {
  match v {
    Vec(a) =>
      match a.fill {
        Some(f) => a.data[0:f].to_array()
        None => a.data
      }
    _ => raise LispError::SimpleError("not a vector: " + princ_to_string(v))
  }
}

///|
/// (subseq vect start end) of a vector's elements.
fn share_draw__subseq(
  v : Array[Value],
  start : Int,
  end : Int,
) -> Array[Value] raise {
  if end > v.length() {
    raise LispError::SimpleError(
      "The bounding indices " +
      start.to_string() +
      " and " +
      end.to_string() +
      " are bad for a sequence of length " +
      v.length().to_string() +
      ".",
    )
  }
  v[start:end].to_array()
}

///|
/// (round (first (get-option '$dimensions))) and friends.
fn share_draw__dim(i : Int) -> Value raise {
  nth(i, get_option(q_d_dimensions))
}

///|
fn draw_gnuplot(args : Value) -> Value raise {
  ini_global_options() |> ignore
  user_defaults() |> ignore
  set(q_ear_allocations, Nil) |> ignore
  let mut counter = 0
  let mut scenes_list = list1(list2(q_mlist, q_simp))
  let mut scenes : Value = Nil
  let mut ncols : Value = Fix(1L)
  let mut nrows : Value = Nil
  let mut width : Value = Nil
  let mut height : Value = Nil
  let largs = share_draw__listify_arguments(args)
  for x in largs.iter() {
    if equal(d_op(x), Str("=")) {
      let lhs = d_lhs(x)
      let global = [
        q_d_terminal, q_d_columns, q_d_dimensions, q_d_file_name, q_d_gnuplot_file_name,
        q_d_data_file_name, q_d_delay,
        // deprecated global options
        q_d_file_bgcolor, q_d_pic_width, q_d_pic_height, q_d_eps_width, q_d_eps_height,
        q_d_pdf_width, q_d_pdf_height,
      ]
      if global.iter().any(o => eql(lhs, o)) {
        update_gr_option(lhs, d_rhs(x)) |> ignore
      } else {
        merr("draw: unknown global option ~M ", [lhs]) |> ignore
      }
    } else if equal(caar(x), q_d_gr3d) {
      scenes = append(scenes, list1(make_scene_3d(rest(x))))
    } else if equal(caar(x), q_d_gr2d) {
      scenes = append(scenes, list1(make_scene_2d(rest(x))))
    } else {
      merr("draw: item ~M is not recognized", [x]) |> ignore
    }
  }
  let terminal = get_option(q_d_terminal)
  let isanimatedgif = equal(terminal, q_d_animated_gif)
  let ismultipage = member(
    terminal,
    list([
      q_d_multipage_pdf, q_d_multipage_pdfcairo, q_d_multipage_eps, q_d_multipage_eps_color,
    ]),
  ).truthy()
  let gfn = share_draw__plot_temp_file(get_option(q_d_gnuplot_file_name))
  let dfn = share_draw__plot_temp_file(get_option(q_d_data_file_name))
  // we now create two files: maxout.gnuplot and data.gnuplot
  let cmdstorage = make_string_output_stream()
  let datastorage = make_string_output_stream()
  // :if-exists :supersede -- the files are created when opened
  write_file(lstring(gfn), "")
  write_file(lstring(dfn), "")
  let datapath = format(Nil, "'~a'", [dfn])
  let f = (ctl : String, args : Array[Value]) => format(cmdstorage, ctl, args)
    |> ignore
  let rnd = (v : Value) => round1(v)
  let cm = (v : Value) => num_div(v, Flo(100.0))
  // when one multiplot window is active, change of terminal is not allowed
  if !symval(q_ear_multiplot_is_active).truthy() {
    let term = get_option(q_d_terminal)
    let term_is = (ts : Array[Value]) => ts.iter().any(t1 => eql(term, t1))
    let fn_ = get_option(q_d_file_name)
    if term_is([q_d_dumb]) {
      f("set terminal dumb size ~a, ~a", [
        rnd(num_div(share_draw__dim(0), Fix(10L))),
        rnd(num_div(share_draw__dim(1), Fix(10L))),
      ])
    } else if term_is([q_d_dumb_file]) {
      f("set terminal dumb size ~a, ~a~%set out '~a.dumb'", [
        rnd(num_div(share_draw__dim(0), Fix(10L))),
        rnd(num_div(share_draw__dim(1), Fix(10L))),
        fn_,
      ])
    } else if term_is([q_d_canvas]) {
      f("set terminal canvas enhanced ~a size ~a, ~a~%set out '~a.html'", [
        write_font_type(),
        rnd(share_draw__dim(0)),
        rnd(share_draw__dim(1)),
        fn_,
      ])
    } else if term_is([q_d_png]) {
      f(
        "set terminal png enhanced truecolor ~a size ~a, ~a~%set out '~a.png'",
        [write_font_type(), rnd(share_draw__dim(0)), rnd(share_draw__dim(1)), fn_],
      )
    } else if term_is([q_d_pngcairo]) {
      f(
        "set terminal pngcairo dashed enhanced truecolor ~a size ~a, ~a~%set out '~a.png'",
        [write_font_type(), rnd(share_draw__dim(0)), rnd(share_draw__dim(1)), fn_],
      )
    } else if term_is([q_d_eps, q_d_multipage_eps]) {
      f(
        "set terminal postscript dashed eps enhanced ~a size ~acm, ~acm~%set out '~a.eps'",
        [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
      )
    } else if term_is([q_d_eps_color, q_d_multipage_eps_color]) {
      f(
        "set terminal postscript dashed eps enhanced ~a color size ~acm, ~acm~%set out '~a.eps'",
        [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
      )
    } else if term_is([q_d_epslatex]) {
      f("set terminal epslatex ~a color size ~acm, ~acm~%set out '~a.tex'", [
        write_font_type(),
        cm(share_draw__dim(0)),
        cm(share_draw__dim(1)),
        fn_,
      ])
    } else if term_is([q_d_epslatex_standalone]) {
      f(
        "set terminal epslatex dashed standalone ~a color size ~acm, ~acm~%set out '~a.tex'",
        [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
      )
    } else if term_is([q_d_cairolatex_pdf]) {
      f(
        "set terminal cairolatex pdf ~a color size ~acm, ~acm~%set out '~a.tex'",
        [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
      )
    } else if term_is([q_d_cairolatex_pdf_standalone]) {
      f(
        "set terminal cairolatex pdf standalone ~a color size ~acm, ~acm~%set out '~a.tex'",
        [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
      )
    } else if term_is([q_d_pdf, q_d_multipage_pdf]) {
      f(
        "set terminal pdf dashed enhanced ~a color size ~acm, ~acm~%set out '~a.pdf'",
        [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
      )
    } else if term_is([q_d_pdfcairo, q_d_multipage_pdfcairo]) {
      f(
        "set terminal pdfcairo dashed enhanced ~a color size ~acm, ~acm~%set out '~a.pdf'",
        [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
      )
    } else if term_is([q_d_jpg]) {
      f("set terminal jpeg enhanced ~a size ~a, ~a~%set out '~a.jpg'", [
        write_font_type(),
        rnd(share_draw__dim(0)),
        rnd(share_draw__dim(1)),
        fn_,
      ])
    } else if term_is([q_d_gif]) {
      f("set terminal gif enhanced ~a size ~a, ~a~%set out '~a.gif'", [
        write_font_type(),
        rnd(share_draw__dim(0)),
        rnd(share_draw__dim(1)),
        fn_,
      ])
    } else if term_is([q_d_svg]) {
      f("set terminal svg dashed enhanced ~a size ~a, ~a~%set out '~a.svg'", [
        write_font_type(),
        rnd(share_draw__dim(0)),
        rnd(share_draw__dim(1)),
        fn_,
      ])
    } else if term_is([q_d_tikz]) {
      f("set terminal tikz ~a size ~a, ~a~%set out '~a.tikz'", [
        write_font_type(),
        cm(rnd(share_draw__dim(0))),
        cm(rnd(share_draw__dim(1))),
        fn_,
      ])
    } else if term_is([q_d_tikz_standalone]) {
      f("set terminal tikz standalone ~a size ~a, ~a~%set out '~a.tikz'", [
        write_font_type(),
        cm(rnd(share_draw__dim(0))),
        cm(rnd(share_draw__dim(1))),
        fn_,
      ])
    } else if term_is([q_d_animated_gif]) {
      f(
        "set terminal gif enhanced animate ~a size ~a, ~a delay ~a~%set out '~a.gif'",
        [
          write_font_type(),
          rnd(share_draw__dim(0)),
          rnd(share_draw__dim(1)),
          get_option(q_d_delay),
          fn_,
        ],
      )
    } else if term_is([q_d_aquaterm]) {
      f("set terminal aqua enhanced ~a ~a size ~a ~a~%", [
        symval(q_ear_draw_terminal_number),
        write_font_type(),
        rnd(share_draw__dim(0)),
        rnd(share_draw__dim(1)),
      ])
    } else if term_is([q_d_wxt]) {
      f("set terminal wxt dashed enhanced ~a ~a size ~a, ~a~%", [
        symval(q_ear_draw_terminal_number),
        write_font_type(),
        rnd(share_draw__dim(0)),
        rnd(share_draw__dim(1)),
      ])
    } else if term_is([q_d_qt]) {
      f("set terminal qt dashed enhanced ~a ~a size ~a, ~a~%", [
        symval(q_ear_draw_terminal_number),
        write_font_type(),
        rnd(share_draw__dim(0)),
        rnd(share_draw__dim(1)),
      ])
    } else if term_is([q_d_x11]) {
      f(
        "if(GPVAL_VERSION >= 5.0){set terminal x11 dashed enhanced ~a ~a size ~a, ~a replotonresize} else {set terminal x11 dashed enhanced ~a ~a size ~a, ~a}~%",
        [
          symval(q_ear_draw_terminal_number),
          write_font_type(),
          rnd(share_draw__dim(0)),
          rnd(share_draw__dim(1)),
          symval(q_ear_draw_terminal_number),
          write_font_type(),
          rnd(share_draw__dim(0)),
          rnd(share_draw__dim(1)),
        ],
      )
    } else if term_is([q_d_windows]) {
      f("set terminal windows enhanced ~a ~a size ~a, ~a~%", [
        symval(q_ear_draw_terminal_number),
        write_font_type(),
        rnd(share_draw__dim(0)),
        rnd(share_draw__dim(1)),
      ])
    } else {
      // If we arrive here, (get-option '$terminal) returned something
      // unrecognized: $obj $ply $pnm $screen $stl $tiff $vrml are accepted
      // by UPDATE-TERMINAL, but not handled here.
      if !eq(get_option(q_d_terminal), q_d_screen) {
        mtell(
          list([
            Str(
              "draw: warning: I don't know about terminal '~m'; I'll try to restore the default.~%",
            ),
            get_option(q_d_terminal),
          ]),
        )
        |> ignore
        mtell(
          list1(
            Str("draw: try this: set_draw_defaults(terminal = <something>);~%"),
          ),
        )
        |> ignore
      }
      f("set terminal GNUTERM ~a ~a size ~a, ~a~%", [
        symval(q_ear_draw_terminal_number),
        write_font_type(),
        rnd(share_draw__dim(0)),
        rnd(share_draw__dim(1)),
      ])
    }
  }
  // compute some parameters for multiplot
  if !isanimatedgif && !ismultipage {
    ncols = get_option(q_d_columns)
    nrows = num_ceiling(num_div(int(length(scenes)), ncols)).0
    if length(scenes) > 1 {
      f("~%set size 1.0, 1.0~%set origin 0.0, 0.0~%set multiplot~%", [])
    }
  }
  // Make gnuplot versions newer than 5.0 understand that linetype means we
  // try to set the dash type
  f("~%if(GPVAL_VERSION >= 5.0){set for [i=1:8] linetype i dashtype i}", [])
  // By default gnuplot assumes everything below 1e-8 to be a rounding error
  // and rounds it down to 0. As plot and draw handle the imaginary part
  // without gnuplot's help this isn't needed here and is turned off.
  f("~%set zero 0.0", [])
  // We use whitespace as a separator, so override any datafile separator
  // the user has set.
  f("~%set datafile separator whitespace", [])
  // write descriptions of 2d and 3d scenes
  {
    let mut i = -1
    let mut alloc = reverse(symval(q_ear_allocations))
    let mut nilcounter = 0
    // recalculate nrows for automatic scene allocations
    let mut nnil = 0
    for a in alloc.iter() {
      if a is Nil {
        nnil = nnil + 1
      }
    }
    nrows = num_ceiling(num_div(int(nnil), ncols)).0
    if num_gt(nrows, Fix(0L)) {
      width = num_div(Flo(1.0), ncols)
      height = num_div(Flo(1.0), nrows)
    }
    for scn in scenes.iter() {
      // write size and origin if necessary
      if isanimatedgif || ismultipage {
        f("~%set size 1.0, 1.0~%", [])
        f("set obj 1 rectangle behind from screen 0.0,0.0 to screen 1.0,1.0~%", [])
      } else {
        // it's not an animated gif
        let thisalloc = car(alloc)
        alloc = cdr(alloc)
        let mut origin1 : Value = Nil
        let mut origin2 : Value = Nil
        let mut size1 : Value = Nil
        let mut size2 : Value = Nil
        if thisalloc.truthy() {
          // user defined scene allocation
          origin1 = first(thisalloc)
          origin2 = second(thisalloc)
          size1 = third(thisalloc)
          size2 = fourth(thisalloc)
        } else {
          // automatic scene allocation
          origin1 = num_mul(width, num_mod(int(nilcounter), ncols))
          origin2 = num_mul(
            height,
            num_sub(
              num_sub(nrows, Flo(1.0)),
              num_floor(num_div(int(nilcounter), ncols)).0,
            ),
          )
          size1 = width
          size2 = height
          nilcounter = nilcounter + 1
        }
        f("~%set size ~a, ~a~%", [size1, size2])
        f("set origin ~a, ~a~%", [origin1, origin2])
        if !(
            symval(q_ear_multiplot_is_active).truthy() ||
            member(
              get_option(q_d_terminal),
              list([
                q_d_epslatex, q_d_epslatex_standalone, q_d_cairolatex_pdf, q_d_cairolatex_pdf_standalone,
              ]),
            ).truthy()
          ) {
          f("set obj 1 rectangle behind from screen ~a,~a to screen ~a,~a~%", [
            origin1,
            origin2,
            num_add(origin1, size1),
            num_add(origin2, size2),
          ])
        }
      }
      let mut is1stobj = true
      let mut biglist : Value = Nil
      let mut grouplist : Value = Nil
      let mut scene_short_description : Value = Nil
      f("~a", [second(scn)])
      if num_eq(first(scn), Fix(2L)) {
        // it's a 2d scene
        scene_short_description = list1(list2(q_d_gr2d, q_simp))
        f("plot ", [])
      } else if num_eq(first(scn), Fix(3L)) {
        // it's a 3d scene
        scene_short_description = list1(list2(q_d_gr3d, q_simp))
        f("splot ", [])
      }
      for obj in third(scn).iter() {
        scene_short_description = cons(
          share_draw__gr_object_name(obj),
          scene_short_description,
        )
        if is1stobj {
          is1stobj = false
        } else {
          f(", \\~%", [])
        }
        let mut pcom = share_draw__gr_object_command(obj)
        if listp(pcom) {
          while consp(pcom) {
            i = i + 1
            let index = format(Nil, " index ~a", [int(i)])
            let c = car(pcom)
            pcom = cdr(pcom)
            f("~a~a~a~a", [
              datapath,
              index,
              c,
              Str(if pcom is Nil { "" } else { "," }),
            ])
          }
        } else {
          i = i + 1
          f("~a~a~a", [datapath, format(Nil, " index ~a", [int(i)]), pcom])
        }
        grouplist = append(grouplist, share_draw__gr_object_groups(obj))
        biglist = append(biglist, share_draw__gr_object_points(obj))
      }
      // let's write data in data.gnuplot
      let mut blis = biglist
      let mut glis = grouplist
      while !(blis is Nil) {
        let vect = share_draw__vec_data(car(blis))
        let k = vect.length()
        let ncol = to_int(caar(glis))
        let mut l = 0
        let m = cadar(glis)
        let mut non_numeric_region = false
        if num_eq(m, Fix(0L)) {
          // no blank lines
          let mut cont = 0
          while cont != k {
            let coordinates = share_draw__subseq(vect, cont, cont + ncol)
            // control of non numeric y values, code related to draw_realpart
            if non_numeric_region {
              if finite_real_p(coordinates[0]).truthy() &&
                finite_real_p(coordinates[1]).truthy() {
                non_numeric_region = false
                share_draw__write_subarray(coordinates, datastorage)
              }
            } else if finite_real_p(coordinates[0]).truthy() &&
              finite_real_p(coordinates[1]).truthy() {
              share_draw__write_subarray(coordinates, datastorage)
            } else {
              non_numeric_region = true
              format(datastorage, "~%", []) |> ignore
            }
            cont = cont + ncol
          }
        } else {
          // blank lines every m lines
          let mm = to_int(m)
          let mut cont = 0
          while cont != k {
            if l == mm {
              format(datastorage, "~%", []) |> ignore
              l = 0
            }
            share_draw__write_subarray(share_draw__subseq(vect, cont, cont + ncol), datastorage)
            l = l + 1
            cont = cont + ncol
          }
        }
        format(datastorage, "~%~%", []) |> ignore
        blis = cdr(blis)
        glis = cdr(glis)
      }
      counter = counter + 1
      scenes_list = cons(reverse(scene_short_description), scenes_list)
    }
  }
  write_file(lstring(dfn), get_output_stream_string(datastorage))
  if isanimatedgif || ismultipage {
    // this is an animated gif or multipage plot file
    if isanimatedgif {
      f("~%unset output~%quit~%~%", [])
    } else {
      f("~%set term dumb~%~%", [])
    }
    write_file(lstring(gfn), get_output_stream_string(cmdstorage))
    // ($system $gnuplot_command (format nil $gnuplot_file_args gfn)):
    // Gnuplot is not run by the port.
  } else {
    // non animated gif: command file maxout.gnuplot is now ready
    f("~%", [])
    if length(scenes) > 1 {
      f("unset multiplot~%unset output ~%", [])
    } else if lstring(get_option(q_d_xy_file)) != "" {
      // if we want to save the coordinates in a file, print them when
      // hitting the x key after clicking the mouse button
      f("set print \"~a\" append~%bind x \"print MOUSE_X,MOUSE_Y\"~%", [
        get_option(q_d_xy_file),
      ])
    }
    // in svg and pdfcairo terminals it is necessary to unset output to
    // force Gnuplot to write the last few bytes at the end of the file. It
    // is always save to unset the output at the end of a scene.
    if !symval(q_ear_multiplot_is_active).truthy() {
      // not in a one window multiplot
      f("unset output~%", [])
    }
    write_file(lstring(gfn), get_output_stream_string(cmdstorage))
    // get the plot: the Lisp code either sends "load 'gfn'" to the Gnuplot
    // process (screen-like terminals with gnuplot_pipes) or runs
    // $gnuplot_command on gfn. The port cannot run Gnuplot; that step is
    // skipped.
    if member(
        get_option(q_d_terminal),
        list([q_d_screen, q_d_aquaterm, q_d_wxt, q_d_x11, q_d_qt, q_d_windows]),
      ).truthy() &&
      equal(symval(q_d_draw_renderer), q_d_gnuplot_pipes) {
      if !symval(q_ear_multiplot_is_active).truthy() {
        share_draw__send_gnuplot_command(Str("unset output"))
      }
      share_draw__send_gnuplot_command(Str("reset"))
      share_draw__send_gnuplot_command(format(Nil, "load '~a'", [gfn]))
    }
  }
  ignore(counter)
  // the output is a simplified description of the scene(s)
  reverse(scenes_list)
}

///|
/// This function transforms an integer number into a string, adding zeros
/// at the left side until the length of the string equals 10. This
/// function is useful to name a sequence of frames.
fn d_add_zeroes(num : Value) -> Value raise {
  format(Nil, "~10,'0d", [d_sconcat(list1(num))])
}

///|
/// Copies current plot in window into a file.
fn d_draw_file(opts : Value) -> Value raise {
  let mut str : Value = Nil
  for x in opts.iter() {
    if equal(d_op(x), Str("=")) {
      update_gr_option(d_lhs(x), d_rhs(x)) |> ignore
    } else {
      merr("draw: item ~M is not recognized as an option assignment", [x])
      |> ignore
    }
  }
  let term = get_option(q_d_terminal)
  let term_is = (t1 : Value) => eql(term, t1)
  let fn_ = get_option(q_d_file_name)
  let rnd = (v : Value) => round1(v)
  let cm = (v : Value) => num_div(v, Flo(100.0))
  if term_is(q_d_canvas) {
    str = format(
      Nil,
      "set terminal canvas enhanced ~a size ~a, ~a~%set out '~a.html'",
      [write_font_type(), rnd(share_draw__dim(0)), rnd(share_draw__dim(1)), fn_],
    )
  } else if term_is(q_d_png) {
    str = format(
      Nil,
      "set terminal png enhanced truecolor ~a size ~a, ~a~%set out '~a.png'",
      [write_font_type(), rnd(share_draw__dim(0)), rnd(share_draw__dim(1)), fn_],
    )
  } else if term_is(q_d_pngcairo) {
    str = format(
      Nil,
      "set terminal pngcairo dashed enhanced truecolor ~a size ~a, ~a~%set out '~a.png'",
      [write_font_type(), rnd(share_draw__dim(0)), rnd(share_draw__dim(1)), fn_],
    )
  } else if term_is(q_d_eps) {
    str = format(
      Nil,
      "set terminal postscript dashed eps enhanced ~a size ~acm, ~acm~%set out '~a.eps'",
      [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
    )
  } else if term_is(q_d_epslatex) {
    // (format str ...) with STR nil: the string is discarded
    format(
      str,
      "set terminal epslatex ~a color dashed size ~acm, ~acm~%set out '~a.tex'",
      [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
    )
    |> ignore
  } else if term_is(q_d_epslatex_standalone) {
    format(
      str,
      "set terminal epslatex dashed standalone ~a color size ~acm, ~acm~%set out '~a.tex'",
      [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
    )
    |> ignore
  } else if term_is(q_d_eps_color) {
    str = format(
      Nil,
      "set terminal postscript dashed eps enhanced ~a color size ~acm, ~acm~%set out '~a.eps'",
      [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
    )
  } else if term_is(q_d_cairolatex_pdf) {
    format(
      str,
      "set terminal cairolatex pdf ~a color size ~acm, ~acm~%set out '~a.tex'",
      [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
    )
    |> ignore
  } else if term_is(q_d_cairolatex_pdf_standalone) {
    format(
      str,
      "set terminal cairolatex pdf standalone ~a color size ~acm, ~acm~%set out '~a.tex'",
      [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
    )
    |> ignore
  } else if term_is(q_d_pdf) {
    str = format(
      Nil,
      "set terminal pdf dashed enhanced ~a color size ~acm, ~acm~%set out '~a.pdf'",
      [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
    )
  } else if term_is(q_d_pdfcairo) {
    str = format(
      Nil,
      "set terminal pdfcairo dashed enhanced ~a color size ~acm, ~acm~%set out '~a.pdf'",
      [write_font_type(), cm(share_draw__dim(0)), cm(share_draw__dim(1)), fn_],
    )
  } else if term_is(q_d_jpg) {
    str = format(Nil, "set terminal jpeg ~a size ~a, ~a~%set out '~a.jpg'", [
      write_font_type(),
      rnd(share_draw__dim(0)),
      rnd(share_draw__dim(1)),
      fn_,
    ])
  } else if term_is(q_d_gif) {
    str = format(Nil, "set terminal gif ~a size ~a, ~a~%set out '~a.gif'", [
      write_font_type(),
      rnd(share_draw__dim(0)),
      rnd(share_draw__dim(1)),
      fn_,
    ])
  } else if term_is(q_d_svg) {
    str = format(
      Nil,
      "set terminal svg dashed enhanced ~a size ~a, ~a~%set out '~a.svg'",
      [write_font_type(), rnd(share_draw__dim(0)), rnd(share_draw__dim(1)), fn_],
    )
  } else if term_is(q_d_tikz) {
    str = format(Nil, "set terminal tikz ~a size ~a, ~a~%set out '~a.tikz'", [
      write_font_type(),
      cm(rnd(share_draw__dim(0))),
      cm(rnd(share_draw__dim(1))),
      fn_,
    ])
  } else if term_is(q_d_tikz_standalone) {
    str = format(
      Nil,
      "set terminal tikz standalone ~a size ~a, ~a~%set out '~a.tikz'",
      [
        write_font_type(),
        cm(rnd(share_draw__dim(0))),
        cm(rnd(share_draw__dim(1))),
        fn_,
      ],
    )
  } else {
    merr("draw: not a file format", []) |> ignore
  }
  // The command goes to the Gnuplot process, which the port cannot run.
  share_draw__send_gnuplot_command(
    format(Nil, "~a~%replot~%unset output~%", [str]),
  )
  Nil
}

///|
/// When working with multiple windows, for example terminal = [wxt, 5],
/// only the newest window is active. This function activates any other
/// previous window at will.
fn d_activate_window(term : Value, num : Value) -> Value raise {
  if !member(term, list([q_d_screen, q_d_wxt, q_d_aquaterm])).truthy() ||
    !integerp(num) ||
    num_lt(num, Fix(0L)) {
    merr("draw: Incorrect terminal or window number", []) |> ignore
  }
  let str = if eq(term, q_d_wxt) {
    "wxt"
  } else if eq(term, q_d_aquaterm) {
    "aquaterm"
  } else if eq(term, q_d_qt) {
    "qt"
  } else {
    "GNUTERM"
  }
  // The command goes to the Gnuplot process, which the port cannot run.
  share_draw__send_gnuplot_command(
    format(Nil, "set terminal ~a ~a~%", [Str(str), num]),
  )
  Nil
}

///|
/// Installs the argument-checking function cells of the DEFUN-CHECKED
/// graphic object constructors.
fn share_draw__register_objects() -> Unit {
  let a = share_draw__argn
  defun(q_errors, args => {
    share_draw__check_args("errors", ["arg"], 0, None, args)
    share_draw__errors(a(args, 0))
  })
  defun(q_points, args => {
    share_draw__check_args("points", ["arg1"], 1, None, args)
    share_draw__points(a(args, 0), a(args, 1))
  })
  defun(q_points3d, args => {
    share_draw__check_args("points3d", ["arg1"], 2, None, args)
    share_draw__points3d(a(args, 0), a(args, 1), a(args, 2))
  })
  defun(q_polygon, args => {
    share_draw__check_args("polygon", ["arg1"], 1, None, args)
    share_draw__polygon(a(args, 0), a(args, 1))
  })
  defun(q_triangle, args => {
    share_draw__check_args("triangle", ["arg1", "arg2", "arg3"], 0, None, args)
    share_draw__triangle(a(args, 0), a(args, 1), a(args, 2))
  })
  defun(q_quadrilateral, args => {
    share_draw__check_args(
      "quadrilateral",
      ["arg1", "arg2", "arg3", "arg4"],
      0,
      None,
      args,
    )
    share_draw__quadrilateral(a(args, 0), a(args, 1), a(args, 2), a(args, 3))
  })
  defun(q_rectangle, args => {
    share_draw__check_args("rectangle", ["arg1", "arg2"], 0, None, args)
    share_draw__rectangle(a(args, 0), a(args, 1))
  })
  defun(q_ellipse, args => {
    share_draw__check_args(
      "ellipse",
      ["xc", "yc", "a", "b", "ang1", "ang2"],
      0,
      None,
      args,
    )
    share_draw__ellipse(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
    )
  })
  defun(q_label, args => {
    share_draw__check_args("label", [], 0, Some("lab"), args)
    share_draw__label(list(args))
  })
  defun(q_bars, args => {
    share_draw__check_args("bars", [], 0, Some("boxes"), args)
    share_draw__bars(list(args))
  })
  defun(q_vect, args => {
    share_draw__check_args("vect", ["arg1", "arg2"], 0, None, args)
    share_draw__vect(a(args, 0), a(args, 1))
  })
  defun(q_vect3d, args => {
    share_draw__check_args("vect3d", ["arg1", "arg2"], 0, None, args)
    share_draw__vect3d(a(args, 0), a(args, 1))
  })
  defun(q_explicit, args => {
    share_draw__check_args(
      "explicit",
      ["fcn", "var", "minval", "maxval"],
      0,
      None,
      args,
    )
    share_draw__explicit(a(args, 0), a(args, 1), a(args, 2), a(args, 3))
  })
  defun(q_region, args => {
    share_draw__check_args(
      "region",
      ["ineq", "x-var", "x-minval", "x-maxval", "y-var", "y-minval", "y-maxval"],
      0,
      None,
      args,
    )
    share_draw__region(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
      a(args, 6),
    )
  })
  defun(q_implicit, args => {
    share_draw__check_args(
      "implicit",
      ["expr", "x", "xmin", "xmax", "y", "ymin", "ymax"],
      0,
      None,
      args,
    )
    share_draw__implicit(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
      a(args, 6),
    )
  })
  defun(q_implicit3d, args => {
    share_draw__check_args(
      "implicit3d",
      [
        "expr", "par1", "xmin", "xmax", "par2", "ymin", "ymax", "par3", "zmin", "zmax",
      ],
      0,
      None,
      args,
    )
    share_draw__implicit3d(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
      a(args, 6),
      a(args, 7),
      a(args, 8),
      a(args, 9),
    )
  })
  defun(q_explicit3d, args => {
    share_draw__check_args(
      "explicit3d",
      ["fcn", "par1", "minval1", "maxval1", "par2", "minval2", "maxval2"],
      0,
      None,
      args,
    )
    share_draw__explicit3d(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
      a(args, 6),
    )
  })
  defun(q_elevation_grid, args => {
    share_draw__check_args(
      "elevation_grid",
      ["mat", "x0", "y0", "width", "height"],
      0,
      None,
      args,
    )
    share_draw__elevation_grid(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
    )
  })
  defun(q_mesh, args => {
    share_draw__check_args("mesh", [], 0, Some("row"), args)
    share_draw__mesh(list(args))
  })
  defun(q_triangle3d, args => {
    share_draw__check_args("triangle3d", ["arg1", "arg2", "arg3"], 0, None, args)
    share_draw__triangle3d(a(args, 0), a(args, 1), a(args, 2))
  })
  defun(q_quadrilateral3d, args => {
    share_draw__check_args(
      "quadrilateral3d",
      ["arg1", "arg2", "arg3", "arg4"],
      0,
      None,
      args,
    )
    share_draw__quadrilateral3d(a(args, 0), a(args, 1), a(args, 2), a(args, 3))
  })
  defun(q_parametric, args => {
    share_draw__check_args(
      "parametric",
      ["xfun", "yfun", "par", "parmin", "parmax"],
      0,
      None,
      args,
    )
    share_draw__parametric(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
    )
  })
  defun(q_polar, args => {
    share_draw__check_args(
      "polar",
      ["radius", "ang", "minang", "maxang"],
      0,
      None,
      args,
    )
    share_draw__polar(a(args, 0), a(args, 1), a(args, 2), a(args, 3))
  })
  defun(q_spherical, args => {
    share_draw__check_args(
      "spherical",
      ["radius", "azi", "minazi", "maxazi", "zen", "minzen", "maxzen"],
      0,
      None,
      args,
    )
    share_draw__spherical(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
      a(args, 6),
    )
  })
  defun(q_cylindrical, args => {
    share_draw__check_args(
      "cylindrical",
      ["r", "z", "minz", "maxz", "azi", "minazi", "maxazi"],
      0,
      None,
      args,
    )
    share_draw__cylindrical(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
      a(args, 6),
    )
  })
  defun(q_parametric3d, args => {
    share_draw__check_args(
      "parametric3d",
      ["xfun", "yfun", "zfun", "par1", "parmin", "parmax"],
      0,
      None,
      args,
    )
    share_draw__parametric3d(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
    )
  })
  defun(q_parametric_surface, args => {
    share_draw__check_args(
      "parametric_surface",
      [
        "xfun", "yfun", "zfun", "par1", "par1min", "par1max", "par2", "par2min", "par2max",
      ],
      0,
      None,
      args,
    )
    share_draw__parametric_surface(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
      a(args, 6),
      a(args, 7),
      a(args, 8),
    )
  })
  defun(q_tube, args => {
    share_draw__check_args(
      "tube",
      ["xfun", "yfun", "zfun", "rad", "par1", "parmin", "parmax"],
      0,
      None,
      args,
    )
    share_draw__tube(
      a(args, 0),
      a(args, 1),
      a(args, 2),
      a(args, 3),
      a(args, 4),
      a(args, 5),
      a(args, 6),
    )
  })
  defun(q_image, args => {
    share_draw__check_args(
      "image",
      ["mat", "x0", "y0", "width", "height"],
      0,
      None,
      args,
    )
    share_draw__image(a(args, 0), a(args, 1), a(args, 2), a(args, 3), a(args, 4))
  })
}

///|
/// Top-level forms of gnuplot.lisp.
fn init_share_gnuplot() -> Unit raise {
  // to be removed in the future
  d_put(q_d_gnuplot, Fix(1L), q_d_version) |> ignore
  if !boundp(q_pts) {
    set(q_pts, Nil) |> ignore
  }
  share_draw__register_objects()
  if !boundp(q_ear_2d_graphic_objects) {
    set(q_ear_2d_graphic_objects, make_hash_table()) |> ignore
  }
  let t2 = symval(q_ear_2d_graphic_objects)
  // table of basic 2d graphic objects
  for kv in [
    (q_d_points, q_points),
    (q_d_errors, q_errors),
    (q_d_polygon, q_polygon),
    (q_d_ellipse, q_ellipse),
    (q_d_triangle, q_triangle),
    (q_d_rectangle, q_rectangle),
    (q_d_quadrilateral, q_quadrilateral),
    (q_d_region, q_region),
    (q_d_explicit, q_explicit),
    (q_d_implicit, q_implicit),
    (q_d_parametric, q_parametric),
    (q_d_vector, q_vect),
    (q_d_label, q_label),
    (q_d_bars, q_bars),
    (q_d_polar, q_polar),
    (q_d_image, q_image),
    (q_p_points, q_points),
    (q_p_errors, q_errors),
    (q_p_polygon, q_polygon),
    (q_p_ellipse, q_ellipse),
    (q_p_triangle, q_triangle),
    (q_p_rectangle, q_rectangle),
    (q_p_quadrilateral, q_quadrilateral),
    (q_p_region, q_region),
    (q_p_explicit, q_explicit),
    (q_p_implicit, q_implicit),
    (q_p_parametric, q_parametric),
    (q_p_vector, q_vect),
    (q_p_label, q_label),
    (q_p_bars, q_bars),
    (q_p_polar, q_polar),
    (q_p_image, q_image),
  ] {
    sethash(kv.0, t2, kv.1) |> ignore
  }
  if !boundp(q_ear_3d_graphic_objects) {
    set(q_ear_3d_graphic_objects, make_hash_table()) |> ignore
  }
  let t3 = symval(q_ear_3d_graphic_objects)
  // table of basic 3d graphic objects
  for kv in [
    (q_d_points, q_points3d),
    (q_d_elevation_grid, q_elevation_grid),
    (q_d_mesh, q_mesh),
    (q_d_triangle, q_triangle3d),
    (q_d_quadrilateral, q_quadrilateral3d),
    (q_d_explicit, q_explicit3d),
    (q_d_implicit, q_implicit3d),
    (q_d_parametric, q_parametric3d),
    (q_d_vector, q_vect3d),
    (q_d_label, q_label),
    (q_d_parametric_surface, q_parametric_surface),
    (q_d_tube, q_tube),
    (q_d_spherical, q_spherical),
    (q_d_cylindrical, q_cylindrical),
    (q_p_points, q_points3d),
    (q_p_elevation_grid, q_elevation_grid),
    (q_p_mesh, q_mesh),
    (q_p_triangle, q_triangle3d),
    (q_p_quadrilateral, q_quadrilateral3d),
    (q_p_explicit, q_explicit3d),
    (q_p_implicit, q_implicit3d),
    (q_p_parametric, q_parametric3d),
    (q_p_vector, q_vect3d),
    (q_p_label, q_label),
    (q_p_parametric_surface, q_parametric_surface),
    (q_p_tube, q_tube),
    (q_p_spherical, q_spherical),
    (q_p_cylindrical, q_cylindrical),
  ] {
    sethash(kv.0, t3, kv.1) |> ignore
  }
}
