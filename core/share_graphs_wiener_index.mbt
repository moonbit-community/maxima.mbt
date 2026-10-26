// Port of share/graphs/wiener_index.lisp: all-pairs shortest paths
// (Floyd-Warshall, Johnson) and the ordinary and weighted Wiener index
// (Juvan-Mohar algorithm).
//
// GRAPHS - graph theory package for Maxima
// Copyright (C) 2008 Andrej Vodopivec <andrej.vodopivec@gmail.com>
// (GPL v2 or later)

///|
fn find_option(opt : Value, options : Value, default? : Value = Nil) -> Value raise {
  for o in options.iter() {
    if eq(o, opt) {
      return t
    } else if listp(o) && eq(cadr(o), opt) {
      return caddr(o)
    }
  }
  default
}

// ---------------------------------------------------------------------------
// FLOYD-WARSHALL algorithm for all-pairs shortest paths

///|
fn d_floyd_warshall(g : Value, options : Value) -> Value raise {
  require_graph_or_digraph(Fix(1L), q_floyd_warshall, g) |> ignore
  let n = to_int(share_graphs__graph_order(g))
  let m : Array[Value] = Array::make(n * n, Fix(0L))
  let mut my_inf : Value = Fix(1L)
  let options = cons(list1(list([q_mlist, q_simp])), options)
  let weighted = find_option(q_d_weighted, options, default=t)
  let mut vrts = cdr(find_option(q_d_vertices, options))
  let mat = d_zeromatrix(int(n), int(n))
  if vrts is Nil {
    vrts = vertices(g)
  }
  if weighted.truthy() {
    for e in cdr(d_edges(g)).iter() {
      my_inf = add_star(
        list([my_inf, d_abs(d_get_edge_weight(e, g, default=Fix(1L)))]),
      )
    }
  } else {
    my_inf = num_add(Fix(1L), share_graphs__graph_order(g))
  }

  // setup the array
  for i in 0..<n {
    for j in 0..<n {
      if i != j {
        m[i * n + j] = if weighted.truthy() {
          d_get_edge_weight(
            share_graphs__ml(list([nth(i, vrts), nth(j, vrts)])),
            g,
            default=Fix(1L),
            not_present=my_inf,
          )
        } else if member(nth(i, vrts), neighbors(nth(j, vrts), g)).truthy() {
          Fix(1L)
        } else {
          my_inf
        }
      } else {
        m[i * n + j] = Fix(0L)
      }
    }
  }

  // compute the distances
  for k in 0..<n {
    for i in 0..<n {
      for j in 0..<n {
        if eq(
            mlsp(add_star(list([m[i * n + k], m[k * n + j]])), m[i * n + j]),
            t,
          ) {
          m[i * n + j] = add_star(list([m[i * n + k], m[k * n + j]]))
        }
      }
    }
  }

  // check for negative cycles
  for k in 0..<n {
    if eq(mlsp(m[k * n + k], Fix(0L)), t) {
      share_graphs__error([Str("Graph contains a negative cycle.")]) |> ignore
    }
  }

  // fill the matrix
  for i in 0..<n {
    for j in 0..<n {
      share_graphs__setf_nth(
        j + 1,
        nth(i + 1, mat),
        if equal(m[i * n + j], my_inf) {
          q_d_inf
        } else {
          m[i * n + j]
        },
      )
      |> ignore
    }
  }
  mat
}

// ---------------------------------------------------------------------------
// JOHNSON's algorithm for all pairs shortest path

///|
fn bellman_ford(s : Value, g : Value) -> (Value, Value) raise {
  let d = make_hash_table()
  let edges = if share_graphs__graph_p(g) {
    append(edges(g), mapcar(e => reverse(e), edges(g)))
  } else {
    edges(g)
  }
  let mut my_inf : Value = Fix(1L)
  let prev = make_hash_table()
  for e in cdr(d_edges(g)).iter() {
    my_inf = add_star(
      list([my_inf, d_abs(d_get_edge_weight(e, g, default=Fix(1L)))]),
    )
  }

  // initialize distances
  for v in vertices(g).iter() {
    if num_eq(s, v) {
      sethash(v, d, Fix(0L)) |> ignore
    } else {
      sethash(v, d, my_inf) |> ignore
    }
  }

  // relax edges
  for _ in 0..<(length(vertices(g)) - 1) {
    for e in edges.iter() {
      let u = car(e)
      let v = cadr(e)
      let nd = add_star(
        list([gethash(u, d), d_get_edge_weight(share_graphs__ml(e), g)]),
      )
      if !equal(gethash(u, d), my_inf) && eq(mgrp(gethash(v, d), nd), t) {
        sethash(v, d, nd) |> ignore
        sethash(v, prev, u) |> ignore
      }
    }
  }

  // check for negative cycles
  for e in edges.iter() {
    let u = car(e)
    let v = cadr(e)
    if eq(
        mgrp(
          gethash(v, d),
          add_star(
            list([gethash(u, d), d_get_edge_weight(share_graphs__ml(e), g)]),
          ),
        ),
        t,
      ) {
      share_graphs__error([Str("Graph contains a negative cycle.")]) |> ignore
    }
  }
  (d, prev)
}

///|
fn d_johnson(g : Value, options : Value) -> Value raise {
  let h = d_copy_graph(g)
  let n = to_int(share_graphs__graph_order(g))
  let options = cons(list1(list([q_mlist, q_simp])), options)
  let weighted = find_option(q_d_weighted, options, default=t)
  let mut vrts = cdr(find_option(q_d_vertices, options))
  let m = d_zeromatrix(int(n), int(n))
  if vrts is Nil {
    vrts = vertices(g)
  }
  let nv = num_add(Fix(1L), share_graphs__max_list(vrts))
  if weighted.truthy() {
    for e in cdr(d_edges(g)).iter() {
      d_set_edge_weight(e, d_get_edge_weight(e, g), h) |> ignore
    }
  }

  // add a new vertex
  d_add_vertex(nv, gr=h) |> ignore
  for v in vrts.iter() {
    d_add_edge(share_graphs__ml(list([nv, v])), h) |> ignore
    d_set_edge_weight(share_graphs__ml(list([nv, v])), Fix(0L), h) |> ignore
  }

  // run the bellman-ford algorithm
  let (d, _) = bellman_ford(nv, h)

  // re-weight the edges
  for e in cdr(d_edges(g)).iter() {
    let nw = add_star(
      list([
        if weighted.truthy() {
          d_get_edge_weight(e, g)
        } else {
          Fix(1L)
        },
        gethash(d_first(e), d),
        mul_star(list([Fix(-1L), gethash(funcall(q_d_second, [e]), d)])),
      ]),
    )
    d_set_edge_weight(e, nw, h) |> ignore
  }
  d_remove_vertex(nv, h) |> ignore

  // run the dijkstra's algorithm for each vertex
  for i in 0..<n {
    let (dd, _) = dijkstra(nth(i, vrts), nv, h)
    for j in 0..<n {
      if i != j {
        share_graphs__setf_nth(
          j + 1,
          nth(i + 1, m),
          if eq(q_d_inf, gethash(nth(j, vrts), dd)) {
            q_d_inf
          } else {
            add_star(
              list([
                gethash(nth(j, vrts), dd),
                mul_star(list([Fix(-1L), gethash(nth(i, vrts), d)])),
                gethash(nth(j, vrts), d),
              ]),
            )
          },
        )
        |> ignore
      }
    }
  }

  // return the matrix m
  m
}

// ---------------------------------------------------------------------------
// JUVAN-MOHAR algorithm

///|
fn wiener_h_index(g : Value) -> Value raise {
  let n = length(vertices(g))
  let q = make_hash_table()
  let mut j = 0
  let mut k = 1
  let mut w : Value = Fix(0L)
  let visited = make_hash_table()
  let d = make_hash_table(kind=Equal)
  let s = make_hash_table()
  let c = make_hash_table(kind=Equal)
  let we = make_hash_table(kind=Equal)
  let mut wi : Value = Fix(0L)

  // initialize array we
  for e in edges(g).iter() {
    sethash(e, we, Fix(0L)) |> ignore
  }

  // initialize arrays c and d
  for v in vertices(g).iter() {
    for u in vertices(g).iter() {
      sethash(list([v, u]), c, Fix(0L)) |> ignore
      sethash(list([v, u]), d, Fix(0L)) |> ignore
    }
  }

  // For each vertex i
  for v in vertices(g).iter() {
    // initialize c
    sethash(list([v, v]), c, Fix(1L)) |> ignore

    // we do a bfs search
    for i in vertices(g).iter() {
      sethash(i, visited, Nil) |> ignore
    }
    sethash(Fix(1L), q, v) |> ignore
    sethash(v, visited, t) |> ignore
    j = 0
    k = 1
    while j < k {
      j = j + 1
      w = gethash(int(j), q)
      for u in neighbors(w, g).iter() {
        if !gethash(u, visited).truthy() {
          sethash(list([v, u]), d, num_add(Fix(1L), gethash(list([v, w]), d)))
          |> ignore
          sethash(u, visited, t) |> ignore
          k = k + 1
          sethash(int(k), q, u) |> ignore
        }
        if num_gt(gethash(list([v, u]), d), gethash(list([v, w]), d)) {
          share_graphs__incf_hash(list([v, u]), c, gethash(list([v, w]), c))
          |> ignore
        }
      }
    }

    // and visit vertices in reverse order
    let mut j = n
    while j >= 1 {
      let w = gethash(int(j), q)
      sethash(w, s, Fix(0L)) |> ignore
      for u in neighbors(w, g).iter() {
        if num_lt(gethash(list([v, w]), d), gethash(list([v, u]), d)) {
          let x = num_mul(
            num_div(gethash(list([v, w]), c), gethash(list([v, u]), c)),
            num_add(Fix(1L), gethash(u, s)),
          )
          share_graphs__incf_hash(
            list([num_min(u, w), num_max(u, w)]),
            we,
            num_div(x, Fix(2L)),
          )
          |> ignore
          share_graphs__incf_hash(w, s, x) |> ignore
        }
      }
      j = j - 1
    }
  }

  // Compute the Wiener index
  for e in edges(g).iter() {
    wi = num_add(wi, gethash(e, we))
  }
  wi
}

///|
fn d_wiener_index(g : Value, options : Value) -> Value raise {
  require_graph(Fix(1L), q_wiener_index, g) |> ignore
  if !d_is_connected(g).truthy() {
    share_graphs__error([Str("`wiener_index': input graph is not connected")])
    |> ignore
  }
  let weighted = find_option(q_d_weighted, options)
  let algorithm = find_option(
    q_d_algorithm,
    options,
    default=if weighted.truthy() { q_d_floyd_warshall } else { q_d_juvan_mohar },
  )
  if eq(algorithm, q_d_juvan_mohar) {
    wiener_h_index(g)
  } else if eq(algorithm, q_d_johnson) {
    div_star(
      d_xreduce(
        Str("+"),
        d_flatten(
          d_args(d_johnson(g, list1(share_graphs__ml(list([q_d_weighted, weighted]))))),
        ),
      ),
      Fix(2L),
    )
  } else if eq(algorithm, q_d_floyd_warshall) {
    div_star(
      d_xreduce(
        Str("+"),
        d_flatten(
          d_args(
            d_floyd_warshall(g, list1(share_graphs__ml(list([q_d_weighted, weighted])))),
          ),
        ),
      ),
      Fix(2L),
    )
  } else {
    share_graphs__error([Str("Unknown algorithm for WIENER_INDEX")])
  }
}

///|
fn init_share_wiener_index() -> Unit raise {
  ()
}
