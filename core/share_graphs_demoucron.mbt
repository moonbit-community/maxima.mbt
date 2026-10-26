// Port of share/graphs/demoucron.lisp: Demoucron planarity test algorithm
// (a simple quadratic-time planarity test algorithm).
//
// GRAPHS - graph theory package for Maxima
// Copyright (C) 2008 Andrej Vodopivec <andrej.vodopivec@gmail.com>
// (GPL v2 or later)
//
// The state of the algorithm lives in specials (defvar without a value):
// *back-edges* *dfsnum* *dfsnum-curr* *dfs-prev* *h-vertices* *h-edges*
// *g-vertices* *embedding* *facial-walks* *bridges* *current-bridge*
// *current-attachements* *visited-vertices* *available-faces* *dfs-visited*.

///|
fn share_graphs__push_special(s : Value, x : Value) -> Unit {
  set(s, cons(x, symval(s))) |> ignore
}

// ---------------------------------------------------------------------------
// finds a cycle in g - g should be connected

///|
fn find_h_cycle(gr : Value) -> Value raise {
  let v = car(vertices(gr))
  with_specials(
    [
      (q_ear_back_edges, Nil),
      (q_ear_dfsnum, make_hash_table()),
      (q_ear_dfs_prev, make_hash_table()),
      (q_ear_dfsnum_curr, Fix(0L)),
    ],
    () => {
      let mut cycle : Value = Nil
      sethash(v, symval(q_ear_dfs_prev), v) |> ignore
      dfs_find_cycle(v, gr) |> ignore
      let back_edges = symval(q_ear_back_edges)
      if back_edges is Nil {
        Nil
      } else {
        let mut u = caar(back_edges)
        let v = cadar(back_edges)
        while !num_eq(u, v) {
          cycle = cons(u, cycle)
          u = gethash(u, symval(q_ear_dfs_prev))
        }
        cycle = cons(v, cycle)
        cycle
      }
    },
  )
}

///|
fn dfs_find_cycle(v : Value, gr : Value) -> Value raise {
  let dfsnum = symval(q_ear_dfsnum)
  let prev = symval(q_ear_dfs_prev)
  sethash(v, dfsnum, symval(q_ear_dfsnum_curr)) |> ignore
  set(q_ear_dfsnum_curr, num_add(symval(q_ear_dfsnum_curr), Fix(1L))) |> ignore
  for u in neighbors(v, gr).iter() {
    if gethash(u, dfsnum) is Nil {
      sethash(u, prev, v) |> ignore
      dfs_find_cycle(u, gr) |> ignore
    } else if !num_eq(u, gethash(v, prev)) {
      share_graphs__push_special(q_ear_back_edges, list([u, v]))
    }
  }
  Nil
}

///|
fn d_find_cycle(gr : Value) -> Value raise {
  require_graph(q_find_cycle, Fix(1L), gr) |> ignore
  let cycle = find_h_cycle(gr)
  share_graphs__ml(cycle)
}

// ---------------------------------------------------------------------------
// finds facial walks of h (running time o(E(h)))

///|
fn find_facial_walks(edges : Value) -> Value raise {
  let visited_edges = make_hash_table(kind=Equal)
  let embedding = symval(q_ear_embedding)
  for e in edges.iter() {
    if gethash(e, visited_edges) is Nil {
      let mut u = car(e)
      let mut v = cadr(e)
      let mut walk = list1(u)
      let mut z = gethash(list([v, u]), embedding)
      sethash(list([u, v]), visited_edges, t) |> ignore
      u = v
      v = z
      while !(num_eq(u, car(e)) && num_eq(v, cadr(e))) {
        sethash(list([u, v]), visited_edges, t) |> ignore
        walk = cons(u, walk)
        z = gethash(list([v, u]), embedding)
        u = v
        v = z
      }
      share_graphs__push_special(q_ear_facial_walks, walk)
    }
  }
  Nil
}

// ---------------------------------------------------------------------------
// finds the bridges in g-h
//  - a bridge is a list (vertices-of-the-bridge attachements-of-the-bridge)

///|
fn find_bridges(gr : Value) -> Value raise {
  set(q_ear_bridges, Nil) |> ignore
  set(q_ear_visited_vertices, make_hash_table()) |> ignore
  for v in symval(q_ear_g_vertices).iter() {
    if !gethash(v, symval(q_ear_visited_vertices)).truthy() {
      set(q_ear_current_bridge, list1(v)) |> ignore
      set(q_ear_current_attachements, Nil) |> ignore
      dfs_find_bridge(v, gr) |> ignore
      for v in symval(q_ear_current_attachements).iter() {
        remhash(v, symval(q_ear_visited_vertices)) |> ignore
      }
      share_graphs__push_special(
        q_ear_bridges,
        list([symval(q_ear_current_bridge), symval(q_ear_current_attachements)]),
      )
    }
  }
  for e in edges(gr).iter() {
    if subsetp(e, symval(q_ear_h_vertices)) &&
      gethash(e, symval(q_ear_h_edges)) is Nil {
      share_graphs__push_special(q_ear_bridges, list([e, e]))
    }
  }
  Nil
}

///|
fn dfs_find_bridge(v : Value, gr : Value) -> Value raise {
  let visited = symval(q_ear_visited_vertices)
  sethash(v, visited, t) |> ignore
  for u in neighbors(v, gr).iter() {
    if gethash(u, visited) is Nil {
      share_graphs__push_special(q_ear_current_bridge, u)
      if member(u, symval(q_ear_h_vertices)).truthy() {
        sethash(u, visited, t) |> ignore
        share_graphs__push_special(q_ear_current_attachements, u)
      } else {
        dfs_find_bridge(u, gr) |> ignore
      }
    }
  }
  Nil
}

// ---------------------------------------------------------------------------
// for each bridge find facial walks in which the bridge can be embedded
//  - a bridge is a list (vertices-of-the-bridge attachements-of-the-bridge)

///|
fn match_bridges_to_walks() -> Value raise {
  set(q_ear_available_faces, make_hash_table(kind=Equal)) |> ignore
  for b in symval(q_ear_bridges).iter() {
    let mut walks : Value = Nil
    for w in symval(q_ear_facial_walks).iter() {
      if subsetp(cadr(b), w) {
        walks = cons(w, walks)
      }
    }
    sethash(b, symval(q_ear_available_faces), walks) |> ignore
  }
  Nil
}

// ---------------------------------------------------------------------------
// finds a path between attachment vertices in a bridge

///|
fn find_path(bridge : Value, gr : Value) -> Value raise {
  if length(car(bridge)) == 2 {
    return car(bridge)
  }
  with_specials(
    [(q_ear_dfs_prev, make_hash_table()), (q_ear_dfs_visited, make_hash_table())],
    () => {
      let attachements = cadr(bridge)
      dfs_find_path(car(attachements), car(bridge), gr) |> ignore
      // should not happen since graphs are biconnected!
      if length(attachements) < 2 {
        merr("Too few attachements", []) |> ignore
      }
      let mut u = cadr(attachements)
      let mut path : Value = Nil
      let prev = symval(q_ear_dfs_prev)
      while gethash(u, prev).truthy() {
        path = cons(u, path)
        u = gethash(u, prev)
      }
      path = cons(u, path)
      path
    },
  )
}

///|
fn dfs_find_path(v : Value, bridge : Value, gr : Value) -> Value raise {
  let visited = symval(q_ear_dfs_visited)
  let prev = symval(q_ear_dfs_prev)
  sethash(v, visited, t) |> ignore
  for u in neighbors(v, gr).iter() {
    if !gethash(list([v, u]), symval(q_ear_h_edges)).truthy() {
      if gethash(u, visited) is Nil && member(u, bridge).truthy() {
        sethash(u, prev, v) |> ignore
        if !member(u, symval(q_ear_h_vertices)).truthy() {
          dfs_find_path(u, bridge, gr) |> ignore
        }
      }
    }
  }
  Nil
}

// ---------------------------------------------------------------------------
// adds the path to h and updates the embedding of h

///|
/// One end vertex `a` (followed by `b` on the path) of the path into the
/// embedding of the face.
fn share_graphs__embedd_end(a : Value, b : Value, face : Value) -> Unit raise {
  let embedding = symval(q_ear_embedding)
  let rface = reverse(face)
  if num_eq(a, car(face)) {
    let c = cadr(face)
    sethash(list([a, c]), embedding, b) |> ignore
    sethash(list([a, b]), embedding, car(rface)) |> ignore
  } else if num_eq(a, car(rface)) {
    let c = cadr(rface)
    sethash(list([a, b]), embedding, c) |> ignore
    sethash(list([a, car(face)]), embedding, b) |> ignore
  } else {
    let mut face = face
    while !num_eq(a, cadr(face)) {
      face = cdr(face)
    }
    sethash(list([a, caddr(face)]), embedding, b) |> ignore
    sethash(list([a, b]), embedding, car(face)) |> ignore
  }
}

///|
fn embedd_path(path : Value, face : Value) -> Value raise {
  // add path to h
  let mut inner = cdr(path)
  while cdr(inner).truthy() {
    share_graphs__push_special(q_ear_h_vertices, car(inner))
    set(q_ear_g_vertices, remove(car(inner), symval(q_ear_g_vertices))) |> ignore
    inner = cdr(inner)
  }
  let h_edges = symval(q_ear_h_edges)
  let mut inner = path
  while cdr(inner).truthy() {
    sethash(list([car(inner), cadr(inner)]), h_edges, t) |> ignore
    sethash(list([cadr(inner), car(inner)]), h_edges, t) |> ignore
    inner = cdr(inner)
  }

  // add vertices in the inside of the path into the embedding
  let embedding = symval(q_ear_embedding)
  let mut path_embedd = path
  while cddr(path_embedd).truthy() {
    let u = car(path_embedd)
    let v = cadr(path_embedd)
    let z = caddr(path_embedd)
    sethash(list([v, z]), embedding, u) |> ignore
    sethash(list([v, u]), embedding, z) |> ignore
    path_embedd = cdr(path_embedd)
  }

  // add the first vertex into the embedding
  share_graphs__embedd_end(car(path), cadr(path), face)

  // add the second vertex into the embedding
  let path = reverse(path)
  share_graphs__embedd_end(car(path), cadr(path), face)
  Nil
}

// ---------------------------------------------------------------------------
// this is the demoucron planarity test algorithm
// - g should be 2-connected

///|
fn demoucron(g : Value, return_walks : Value) -> Value raise {
  if num_gt(
      d_graph_size(g),
      num_sub(num_mul(Fix(3L), d_graph_order(g)), Fix(6L)),
    ) {
    return Nil
  }
  let g_vertices = cdr(d_vertices(g))
  with_specials(
    [
      (q_ear_h_vertices, Nil),
      (q_ear_bridges, Nil),
      (q_ear_h_edges, make_hash_table(kind=Equal)),
      (q_ear_g_vertices, g_vertices),
      (q_ear_embedding, make_hash_table(kind=Equal)),
    ],
    () => {
      let h_edges = symval(q_ear_h_edges)
      let embedding = symval(q_ear_embedding)
      // find a cycle - assumes there are no degree one vertices!
      set(q_ear_h_vertices, find_h_cycle(g)) |> ignore
      let h_vertices = symval(q_ear_h_vertices)
      let mut vrt = h_vertices
      while vrt.truthy() {
        sethash(list([car(vrt), cadr(vrt)]), h_edges, t) |> ignore
        sethash(list([cadr(vrt), car(vrt)]), h_edges, t) |> ignore
        vrt = cdr(vrt)
      }
      let v = car(h_vertices)
      let u = car(reverse(h_vertices))
      sethash(list([u, v]), h_edges, t) |> ignore
      sethash(list([v, u]), h_edges, t) |> ignore
      for v in h_vertices.iter() {
        set(q_ear_g_vertices, remove(v, symval(q_ear_g_vertices))) |> ignore
      }

      // embed h
      let mut cycle = h_vertices
      while cdr(cycle).truthy() {
        let u = car(cycle)
        let v = cadr(cycle)
        let z = if caddr(cycle) is Nil { car(h_vertices) } else { caddr(cycle) }
        sethash(list([v, z]), embedding, u) |> ignore
        sethash(list([v, u]), embedding, z) |> ignore
        cycle = cdr(cycle)
      }
      let u = car(reverse(h_vertices))
      let v = car(h_vertices)
      let z = cadr(h_vertices)
      sethash(list([v, z]), embedding, u) |> ignore
      sethash(list([v, u]), embedding, z) |> ignore

      // find the bridges in g-h
      find_bridges(g) |> ignore

      // find facial walks
      set(q_ear_facial_walks, Nil) |> ignore
      find_facial_walks(
        list([
          list([car(h_vertices), cadr(h_vertices)]),
          list([cadr(h_vertices), car(h_vertices)]),
        ]),
      )
      |> ignore
      while symval(q_ear_bridges).truthy() {
        if symval(q_d_demoucron_debug).truthy() {
          print(Str("++++++++++++++++++")) |> ignore
          print(Str("--- facial walks:")) |> ignore
          print(symval(q_ear_facial_walks)) |> ignore
          print(Str("---      bridges:")) |> ignore
          for b in symval(q_ear_bridges).iter() {
            print(b) |> ignore
          }
        }
        // for each bridge find facial walks in which it can be embedded
        match_bridges_to_walks() |> ignore
        let faces = symval(q_ear_available_faces)
        // select the bridge with the smallest number of available walks
        let mut bridge = car(symval(q_ear_bridges))
        for b in symval(q_ear_bridges).iter() {
          if length(gethash(b, faces)) < length(gethash(bridge, faces)) {
            bridge = b
          }
        }
        if symval(q_d_demoucron_debug).truthy() {
          print(Str("---    embedding:")) |> ignore
          print(bridge) |> ignore
        }
        // if the bridge can't be embedded, the graph is not planar
        if length(share_graphs__gethash_d(bridge, faces, bridge)) == 0 {
          return Nil
        }
        // find a path in the bridge
        let path = find_path(bridge, g)
        // embed the path
        embedd_path(path, car(gethash(bridge, faces))) |> ignore
        if symval(q_d_demoucron_debug).truthy() {
          print(Str("---         path:")) |> ignore
          print(path) |> ignore
        }
        set(
          q_ear_facial_walks,
          remove(car(gethash(bridge, faces)), symval(q_ear_facial_walks)),
        )
        |> ignore
        // find the facial walks of the embedding of h
        find_facial_walks(
          list([list([car(path), cadr(path)]), list([cadr(path), car(path)])]),
        )
        |> ignore
        // find new bridges
        find_bridges(g) |> ignore
      }

      // if we come here we have embedded the graph into the plane
      if return_walks.truthy() {
        cons(
          list([q_mlist, q_simp]),
          mapcar(u => cons(list([q_mlist, q_simp]), u), symval(q_ear_facial_walks)),
        )
      } else {
        t
      }
    },
  )
}

///|
fn d_planar_embedding(gr : Value) -> Value raise {
  require_graph(q_planar_embedding, Fix(1L), gr) |> ignore
  if !d_is_biconnected(gr).truthy() {
    share_graphs__error([Str("planar_embedding: the graph is not biconnected.")])
    |> ignore
  }
  demoucron(gr, t)
}

///|
fn d_is_planar(gr : Value) -> Value raise {
  require_graph(q_is_planar, Fix(1L), gr) |> ignore
  if num_lt(d_graph_order(gr), Fix(5L)) {
    return t
  }
  if num_gt(
      d_graph_size(gr),
      num_sub(num_mul(Fix(3L), d_graph_order(gr)), Fix(6L)),
    ) {
    return Nil
  }
  if !d_is_connected(gr).truthy() {
    return is_planar_unconnected(gr)
  }
  if num_lt(d_graph_size(gr), d_graph_order(gr)) {
    // gr is a tree
    return t
  }
  let bicomponents = d_biconnected_components(gr)
  for c in cdr(bicomponents).iter() {
    if length(c) > 4 {
      if !demoucron(d_induced_subgraph(c, gr), Nil).truthy() {
        return Nil
      }
    }
  }
  t
}

///|
fn is_planar_unconnected(g : Value) -> Value raise {
  for c in cdr(d_connected_components(g)).iter() {
    if !d_is_planar(d_induced_subgraph(c, g)).truthy() {
      return Nil
    }
  }
  t
}

///|
fn init_share_demoucron() -> Unit raise {
  ()
}
