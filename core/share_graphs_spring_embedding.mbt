// Port of share/graphs/spring_embedding.lisp: force-based graph embedding
// algorithm.
//
// Based on:
// T.M.J. Fruchterman, E.M. Reingold, Graph drawing by force-directed
// placement, Software practice and experience 21 (1991), 11, 1129--1164.
//
// GRAPHS - graph theory package for Maxima
// Copyright (C) 2007 Andrej Vodopivec <andrej.vodopivec@gmail.com>
// (GPL v2 or later)
//
// The specials *vertex-position* and *optimal-distance* (defvar without a
// value) are bound by $spring_embedding.

///|
fn attractive_force(d : Value) -> Value raise {
  num_div(num_mul(d, d), symval(q_ear_optimal_distance))
}

///|
fn repulsive_force(d : Value) -> Value raise {
  let d = num_max(d, symval(q_ear_epsilon_distance))
  let od = symval(q_ear_optimal_distance)
  num_div(num_div(num_mul(od, od), d), Fix(100L))
}

///|
fn distance(p1 : Value, p2 : Value) -> Value raise {
  let d = mapcar2((a, b) => num_sub(a, b), p1, p2)
  let s = num_sum(list_to_array(mapcar2((a, b) => num_mul(a, b), d, d)))
  share_graphs__cl_sqrt(s)
}

///|
/// The port has no single-floats: a CL single-float value is kept as a
/// double rounded to single precision. `single` tells whether `x` is the
/// result of a single-float operation.
fn share_graphs__sfix(x : Value, single : Bool) -> Value {
  match x {
    Flo(d) if single => Flo(Float::from_double(d).to_double())
    _ => x
  }
}

///|
/// Whether `(distance p1 p2)` is a single-float: the coordinate differences
/// are all rational.
fn share_graphs__single_distance_p(delta : Value) -> Bool {
  delta.iter().all(x => x is (Fix(_) | Big(_) | Ratio(_, _)))
}

///|
/// `(/ u (max delta-abs *epsilon-distance*))` where delta-abs may be a
/// single-float.
fn share_graphs__div_dist(
  u : Value,
  delta_abs : Value,
  eps : Value,
  single : Bool,
) -> Value raise {
  let m = num_max(delta_abs, eps)
  let single = single && !num_lt(delta_abs, eps) && !floatp(u)
  share_graphs__sfix(num_div(u, m), single)
}

///|
/// CL `sqrt`: the square root of a rational is a single-float.
fn share_graphs__cl_sqrt(x : Value) -> Value raise {
  match x {
    Fix(_) | Big(_) | Ratio(_, _) if !minusp(x) =>
      match lsqrt(x) {
        Flo(d) => Flo(Float::from_double(d).to_double())
        r => r
      }
    _ => lsqrt(x)
  }
}

///|
fn random_positions(v_list : Value, dimension : Value) -> Value raise {
  let fixed = symval(q_ear_fixed_vertices)
  let fw = symval(q_ear_frame_width)
  if fixed.truthy() {
    let n = int(length(fixed))
    for i in 0..<length(fixed) {
      let v = nth(i, fixed)
      let ang = num_div(num_mul(num_mul(Fix(2L), int(i)), share_graphs__pi), n)
      let x = num_mul(fw, ftake(q_p_sin, [ang]))
      let y = num_mul(fw, ftake(q_p_cos, [ang]))
      sethash(v, symval(q_ear_vertex_position), list([x, y])) |> ignore
    }
  }
  for v in v_list.iter() {
    if !member(v, fixed).truthy() {
      let x = num_sub(fw, mt_random(num_mul(Fix(2L), fw)))
      let y = num_sub(fw, mt_random(num_mul(Fix(2L), fw)))
      let z = num_sub(fw, mt_random(num_mul(Fix(2L), fw)))
      sethash(
        v,
        symval(q_ear_vertex_position),
        if num_eq(dimension, Fix(3L)) {
          list([x, y, z])
        } else {
          list([x, y])
        },
      )
      |> ignore
    }
  }
  Nil
}

///|
fn d_spring_embedding(
  g : Value,
  depth : Value,
  fixed_vertices : Value,
  dimension : Value,
  continue_ : Value,
) -> Value raise {
  let fw = symval(q_ear_frame_width)
  let vertex_displacement = make_hash_table()
  with_specials(
    [
      (q_ear_vertex_position, make_hash_table()),
      (q_ear_fixed_vertices, cdr(fixed_vertices)),
      (
        q_ear_optimal_distance,
        num_div(num_mul(Fix(2L), fw), share_graphs__cl_sqrt(d_graph_order(g))),
      ),
    ],
    () => {
      let vpos = symval(q_ear_vertex_position)
      let fixed = symval(q_ear_fixed_vertices)
      let eps = symval(q_ear_epsilon_distance)
      // Start with current positions if we already have some.
      if continue_.truthy() &&
        length(d_get_positions(g)) > 1 &&
        num_eq(d_length(d_first(d_get_positions(g))), dimension) {
        for v in cdr(d_get_positions(g)).iter() {
          sethash(cadr(v), vpos, cdaddr(v)) |> ignore
        }
      } else {
        random_positions(vertices(g), dimension) |> ignore
      }
      let mut step = num_div(fw, Fix(5L))
      let d_step = num_div(step, num_add(Fix(1L), depth))
      for _ in 0..<to_int(depth) {
        step = num_sub(step, d_step)
        for v in vertices(g).iter() {
          sethash(
            v,
            vertex_displacement,
            if num_eq(dimension, Fix(2L)) {
              list([Fix(0L), Fix(0L)])
            } else {
              list([Fix(0L), Fix(0L), Fix(0L)])
            },
          )
          |> ignore
        }

        // calculate repulsive forces
        if fixed is Nil {
          let mut v_vrt = vertices(g)
          while v_vrt.truthy() {
            let v = car(v_vrt)
            let mut u_vrt = cdr(v_vrt)
            let v_pos = gethash(v, vpos)
            while u_vrt.truthy() {
              let u = car(u_vrt)
              let u_pos = gethash(u, vpos)
              let delta = mapcar2((a, b) => num_sub(a, b), v_pos, u_pos)
              let delta_abs = distance(v_pos, u_pos)
              let single = share_graphs__single_distance_p(delta)
              let force = repulsive_force(delta_abs)
              let vu_disp = mapcar(
                u => num_mul(
                  share_graphs__div_dist(u, delta_abs, eps, single),
                  force,
                ),
                delta,
              )
              let v_disp = gethash(v, vertex_displacement)
              let u_disp = gethash(u, vertex_displacement)
              sethash(
                v,
                vertex_displacement,
                mapcar2((a, b) => num_add(a, b), v_disp, vu_disp),
              )
              |> ignore
              sethash(
                u,
                vertex_displacement,
                mapcar2((a, b) => num_sub(a, b), u_disp, vu_disp),
              )
              |> ignore
              u_vrt = cdr(u_vrt)
            }
            v_vrt = cdr(v_vrt)
          }
        }

        // calculate attractive forces
        for e in edges(g).iter() {
          let v = car(e)
          let u = cadr(e)
          let v_pos = gethash(v, vpos)
          let u_pos = gethash(u, vpos)
          let delta = mapcar2((a, b) => num_sub(a, b), v_pos, u_pos)
          let delta_abs = distance(v_pos, u_pos)
          let v_disp = gethash(v, vertex_displacement)
          let u_disp = gethash(u, vertex_displacement)
          let single = share_graphs__single_distance_p(delta)
          // (attractive-force delta-abs), with (* d d) a single-float
          // product when delta-abs is a single-float
          let force = if single {
            num_div(
              share_graphs__sfix(num_mul(delta_abs, delta_abs), true),
              symval(q_ear_optimal_distance),
            )
          } else {
            attractive_force(delta_abs)
          }
          let vu_disp = mapcar(
            u => num_mul(share_graphs__div_dist(u, delta_abs, eps, single), force),
            delta,
          )
          sethash(
            v,
            vertex_displacement,
            mapcar2((a, b) => num_sub(a, b), v_disp, vu_disp),
          )
          |> ignore
          sethash(
            u,
            vertex_displacement,
            mapcar2((a, b) => num_add(a, b), u_disp, vu_disp),
          )
          |> ignore
        }

        // Limit the displacement
        for v in vertices(g).iter() {
          if !member(v, fixed).truthy() {
            let v_disp = gethash(v, vertex_displacement)
            let v_disp = mapcar(u => num_div(u, Fix(2L)), v_disp)
            let v_disp_abs = share_graphs__cl_sqrt(
              num_sum(list_to_array(mapcar2((a, b) => num_mul(a, b), v_disp, v_disp))),
            )
            let mut v_pos = gethash(v, vpos)
            if num_gt(v_disp_abs, step) {
              v_pos = mapcar2(
                (u, v) => num_add(u, num_mul(num_div(v, v_disp_abs), step)),
                v_pos,
                v_disp,
              )
            } else {
              v_pos = mapcar2((a, b) => num_add(a, b), v_pos, v_disp)
            }
            v_pos = mapcar(u => num_min(fw, num_max(u, num_neg(fw))), v_pos)
            sethash(v, vpos, v_pos) |> ignore
          }
        }
      }
      let mut result : Value = Nil
      maphash(
        (vrt, pos) => {
          result = cons(
            share_graphs__ml(list([vrt, share_graphs__ml(pos)])),
            result,
          )
        },
        vpos,
      )
      cons(list([q_mlist, q_simp]), result)
    },
  )
}
