// Port of share/draw/wbd.lisp (Mario Rodriguez Riotorto, 2007-2010):
// the functions of graphic object geomap for two and three dimensions.
// The boundary data $boundaries_array (coast lines and country borders
// from the public domain 'World Boundary Databank') is a literal defvar
// set by the generated init_vars.

///|
extern "C" fn share_wbd__c_sin(x : Double) -> Double = "sin"

///|
extern "C" fn share_wbd__c_cos(x : Double) -> Double = "cos"

///|
extern "C" fn share_wbd__c_tan(x : Double) -> Double = "tan"

///|
extern "C" fn share_wbd__c_log(x : Double) -> Double = "log"

///|
/// (log x) for a double: complex for negative arguments, as in CL.
fn share_wbd__log(x : Double) -> Double raise {
  if x < 0.0 || x == 0.0 {
    to_double(llog(Flo(x)))
  } else {
    share_wbd__c_log(x)
  }
}

///|
/// Common loop of the 2d projections: PROJ maps (longitude, latitude) of a
/// boundary point to (x, y).
fn share_wbd__project_2d(
  lis : Value,
  proj : (Double, Double) -> (Double, Double) raise,
) -> Value raise {
  let mut xmin = 1.7976931348623157e308
  let mut xmax = -1.7976931348623157e308
  let mut ymin = 1.7976931348623157e308
  let mut ymax = -1.7976931348623157e308
  let res = Collector::new()
  let arr = symval(q_d_boundaries_array)
  for i in lis.iter() {
    let polyseg = aref1(arr, to_int(i))
    let len = length(polyseg)
    let ni = len / 2 - 1
    let resi = make_array([2 * (len / 2)], elt="flonum", initial=Flo(0.0))
    let mut count = -1
    for k in 0..=ni {
      let (x, y) = proj(
        to_double(aref1(polyseg, 2 * k)),
        to_double(aref1(polyseg, 2 * k + 1)),
      )
      if x < xmin {
        xmin = x
      } else if x > xmax {
        xmax = x
      }
      if y < ymin {
        ymin = y
      } else if y > ymax {
        ymax = y
      }
      count += 1
      aset1(resi, count, Flo(x)) |> ignore
      count += 1
      aset1(resi, count, Flo(y)) |> ignore
    }
    res.add(resi)
  }
  update_ranges_2d(Flo(xmin), Flo(xmax), Flo(ymin), Flo(ymax)) |> ignore
  res.result()
}

///|
/// Common loop of the 3d projections: PROJ maps (longitude, latitude) of a
/// boundary point to (x, y, z).
fn share_wbd__project_3d(
  lis : Value,
  proj : (Double, Double) -> (Double, Double, Double) raise,
) -> Value raise {
  let mut xmin = 1.7976931348623157e308
  let mut xmax = -1.7976931348623157e308
  let mut ymin = 1.7976931348623157e308
  let mut ymax = -1.7976931348623157e308
  let mut zmin = 1.7976931348623157e308
  let mut zmax = -1.7976931348623157e308
  let res = Collector::new()
  let arr = symval(q_d_boundaries_array)
  for i in lis.iter() {
    let polyseg = aref1(arr, to_int(i))
    let len = length(polyseg)
    let ni = len / 2 - 1
    let resi = make_array([3 * (len / 2)], elt="flonum", initial=Flo(0.0))
    let mut count = -1
    for k in 0..=ni {
      let (x, y, z) = proj(
        to_double(aref1(polyseg, 2 * k)),
        to_double(aref1(polyseg, 2 * k + 1)),
      )
      if x < xmin {
        xmin = x
      } else if x > xmax {
        xmax = x
      }
      if y < ymin {
        ymin = y
      } else if y > ymax {
        ymax = y
      }
      if z < zmin {
        zmin = z
      } else if z > zmax {
        zmax = z
      }
      count += 1
      aset1(resi, count, Flo(x)) |> ignore
      count += 1
      aset1(resi, count, Flo(y)) |> ignore
      count += 1
      aset1(resi, count, Flo(z)) |> ignore
    }
    res.add(resi)
  }
  update_ranges_3d(
    Flo(xmin),
    Flo(xmax),
    Flo(ymin),
    Flo(ymax),
    Flo(zmin),
    Flo(zmax),
  )
  |> ignore
  res.result()
}

///|
/// x and y are the longitude and latitude coordinates
fn longitude_latitude_projection_2d(lis : Value) -> Value raise {
  share_wbd__project_2d(lis, (lon, lat) => (lon, lat))
}

///|
/// Mercator cylindrical projection
/// This is experimental and not documented
fn mercator_projection_2d(lis : Value) -> Value raise {
  let c = 0.0174532925199433 // = %pi / 180
  share_wbd__project_2d(lis, (lon, lat0) => {
    let lat = c * lat0
    (lon, share_wbd__log(share_wbd__c_tan(lat) + 1.0 / share_wbd__c_cos(lat)))
  })
}

///|
/// Miller cylindrical projection
/// This is experimental and not documented
fn miller_projection_2d(lis : Value) -> Value raise {
  let c = 0.0174532925199433 // = %pi / 180
  let c1 = 0.7853981633974483 // = %pi / 4
  share_wbd__project_2d(lis, (lon, lat) => (
    lon,
    1.25 * share_wbd__log(share_wbd__c_tan(c1 + 0.4 * c * lat)),
  ))
}

///|
/// Kavrayskiy VII pseudocylindrical projection
/// This is experimental and not documented
fn kavrayskiy_projection_2d(lis : Value) -> Value raise {
  let c = 0.0174532925199433 // = %pi / 180
  let c1 = 0.4774648292756861 // = 3 / (2 * %pi)
  let c2 = 3.289868133696452 // = %pi^2 / 3
  share_wbd__project_2d(lis, (lon, lat) => {
    let d = c2 - c * c * lat * lat
    let s = if d < 0.0 { to_double(lsqrt(Flo(d))) } else { d.sqrt() }
    (c1 * lon * s, lat)
  })
}

///|
/// Checks of geomap / geomap3d; returns the list of segment numbers.
fn share_wbd__check_args(
  lis : Value,
  proj : Value,
  what : String,
) -> Value raise {
  if symval(q_d_boundaries_array) is Nil {
    merr(what + " (geomap): variable boundaries_array not yet defined", [])
    |> ignore
  }
  if !d_listp(lis).truthy() {
    merr(what + " (geomap): first argument must be a list of integers", [])
    |> ignore
  }
  if !(proj is Nil) && !d_listp(proj).truthy() {
    merr(what + " (geomap): second optional argument must be a list", [])
    |> ignore
  }
  let lis = cdr(d_setify(d_flatten(lis)))
  let nsegments = int(array_dimension(symval(q_d_boundaries_array), 0) - 1)
  let mut bad = false
  for z in lis.iter() {
    if !integerp(z) || num_lt(z, Fix(0L)) || num_gt(z, nsegments) {
      bad = true
      break
    }
  }
  if bad {
    merr(
      what + " (geomap): non integer argument or out of range (0-~M)",
      [nsegments],
    )
    |> ignore
  }
  lis
}

///|
/// (make-list (length lis) :initial-element x)
fn share_wbd__make_list(n : Int, x : Value) -> Value {
  let mut l : Value = Nil
  for _ in 0..<n {
    l = cons(x, l)
  }
  l
}

///|
/// The plot command shared by geomap and geomap3d.
fn share_wbd__command() -> Value raise {
  format(Nil, " t '' w l lw ~a lt ~a lc ~a", [
    get_option(q_d_line_width),
    get_option(q_d_line_type),
    hex_to_rgb(get_option(q_d_color)),
  ])
}

///|
/// Object: 'geomap'
/// Usage:
///     geomap([integer1, integer2,....]), where integers correspond to the
///           polygonal segments stored in array 'boundaries_array'.
/// Options:
///     line_width
///     color
///     line_type
fn geomap(lis : Value, proj? : Value = Nil) -> Value raise {
  let lis = share_wbd__check_args(lis, proj, "draw2d")
  let n = length(lis)
  let command = share_wbd__make_list(n, share_wbd__command())
  // numbers are sent to gnuplot in groups of 2
  let groups = share_wbd__make_list(n, share_wbd__lit_2_0)
  let len1 = fn() raise { num_eq(d_length(proj), Fix(1L)) }
  let points = if proj is Nil ||
    (equal(cadr(proj), q_d_longitude_latitude_projection) && len1()) {
    longitude_latitude_projection_2d(lis)
  } else if equal(cadr(proj), q_d_mercator_projection) && len1() {
    mercator_projection_2d(lis)
  } else if equal(cadr(proj), q_d_miller_projection) && len1() {
    miller_projection_2d(lis)
  } else if equal(cadr(proj), q_d_kavrayskiy_projection) && len1() {
    kavrayskiy_projection_2d(lis)
  } else {
    merr("draw2d (geomap): unknown projection or not well defined", [])
  }
  share_draw__make_gr_object(q_geomap, command, groups, points)
}

///|
let share_wbd__lit_2_0 : Value = list2(Fix(2L), Fix(0L))

///|
let share_wbd__lit_3_0 : Value = list2(Fix(3L), Fix(0L))

///|
/// sphere of radius r and center (cx,cy,cz)
fn spherical_projection_3d(
  lis : Value,
  cx : Value,
  cy : Value,
  cz : Value,
  r : Value,
) -> Value raise {
  let c = 0.0174532925199433 // = %pi / 180
  let cx = to_double(cx)
  let cy = to_double(cy)
  let cz = to_double(cz)
  let r = to_double(r)
  share_wbd__project_3d(lis, (lon0, lat0) => {
    let lon = c * lon0
    let lat = c * lat0
    (
      cx + r * share_wbd__c_cos(lat) * share_wbd__c_cos(lon),
      cy + r * share_wbd__c_cos(lat) * share_wbd__c_sin(lon),
      cz + r * share_wbd__c_sin(lat),
    )
  })
}

///|
/// cylinder of radius rc with its axis passing through the poles of the
/// sphere of radius r and center (cx,cy,cz). In future versions, the axis
/// should be selected by the user, giving the coordinates (long,lati) of
/// one of the points of intersection with the sphere.
fn cylindrical_projection_3d(
  lis : Value,
  cx : Value,
  cy : Value,
  cz : Value,
  r : Value,
  rc : Value,
) -> Value raise {
  let c = 0.0174532925199433 // = %pi / 180
  let cx = to_double(cx)
  let cy = to_double(cy)
  let cz = to_double(cz)
  let r = to_double(r)
  let rc = to_double(rc)
  share_wbd__project_3d(lis, (lon0, lat0) => {
    let lon = c * lon0
    let lat = c * lat0
    (
      cx + rc * share_wbd__c_cos(lon),
      cy + rc * share_wbd__c_sin(lon),
      cz + r * share_wbd__c_sin(lat),
    )
  })
}

///|
/// cone with angle a and axis passing through the poles of the sphere
/// of radius r and center (cx,cy,cz). The cone is tangent to the globe.
fn conic_projection_3d(
  lis : Value,
  cx : Value,
  cy : Value,
  cz : Value,
  r : Value,
  a : Value,
) -> Value raise {
  let c = 0.0174532925199433 // = %pi / 180
  let cx = to_double(cx)
  let cy = to_double(cy)
  let cz = to_double(cz)
  let r = to_double(r)
  let cte = 1.570796326794897 - c * to_double(a) * 0.5 // = %pi / 2 - c*a /2
  share_wbd__project_3d(lis, (lon0, lat0) => {
    let lon = c * lon0
    let mut lat = c * lat0
    let north = lat >= 0.0
    lat = lat.abs()
    let p = r / share_wbd__c_sin(cte + lat)
    let x = cx + p * share_wbd__c_cos(lat) * share_wbd__c_cos(lon)
    let y = cy + p * share_wbd__c_cos(lat) * share_wbd__c_sin(lon)
    let z = if north {
      cz + p * share_wbd__c_sin(lat)
    } else {
      cz + -1.0 * p * share_wbd__c_sin(lat)
    }
    (x, y, z)
  })
}

///|
/// Object: 'geomap3d'
/// Usage:
///     geomap([integer1, integer2,....])
///     geomap([integer1, integer2,....], [3d_proyection_type,par1am1,param2,...]),
///           where integers correspond to the polygonal segments stored in
///           array 'boundaries_array'. Spherical 3d projection is default.
/// Options:
///     line_width
///     color
///     line_type
fn geomap3d(lis : Value, proj? : Value = Nil) -> Value raise {
  let lis = share_wbd__check_args(lis, proj, "draw3d")
  let n = length(lis)
  let command = share_wbd__make_list(n, share_wbd__command())
  // numbers are sent to gnuplot in groups of 3 without blank lines
  let groups = share_wbd__make_list(n, share_wbd__lit_3_0)
  let lenp = fn(k : Int64) raise { num_eq(d_length(proj), Fix(k)) }
  let points = if proj is Nil {
    // default: spherical projection with r=1 and center (0,0,0)
    spherical_projection_3d(lis, Fix(0L), Fix(0L), Fix(0L), Fix(1L))
  } else if equal(cadr(proj), q_d_spherical_projection) && lenp(5L) {
    spherical_projection_3d(
      lis,
      nth(2, proj),
      nth(3, proj),
      nth(4, proj),
      nth(5, proj),
    )
  } else if equal(cadr(proj), q_d_cylindrical_projection) && lenp(6L) {
    cylindrical_projection_3d(
      lis,
      nth(2, proj),
      nth(3, proj),
      nth(4, proj),
      nth(5, proj),
      nth(6, proj),
    )
  } else if equal(cadr(proj), q_d_conic_projection) &&
    lenp(6L) &&
    num_gt(nth(6, proj), Fix(0L)) &&
    num_lt(nth(6, proj), Fix(180L)) {
    conic_projection_3d(
      lis,
      nth(2, proj),
      nth(3, proj),
      nth(4, proj),
      nth(5, proj),
      nth(6, proj),
    )
  } else {
    merr("draw3d (geomap): unknown projection or not well defined", [])
  }
  share_draw__make_gr_object(q_geomap, command, groups, points)
}

///|
fn init_share_wbd() -> Unit raise {
  // update lists of graphic objects
  sethash(q_d_geomap, symval(q_ear_2d_graphic_objects), q_geomap) |> ignore
  sethash(q_d_geomap, symval(q_ear_3d_graphic_objects), q_geomap3d) |> ignore
}
