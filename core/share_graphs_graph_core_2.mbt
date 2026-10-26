// Port of share/graphs/graph_core.lisp (part 2): graph properties
// (connectivity, matrices, girth, distances, bipartition, 2-connectivity,
// strong connectivity, topological sorting, flows, shortest paths, spanning
// trees, hamilton cycles, cliques, colorings), the Maxima-level hash tables
// and the top-level forms.
//
// GRAPHS - graph theory package for Maxima
// Copyright (C) 2007-2011 Andrej Vodopivec <andrej.vodopivec@gmail.com>
// (GPL v2 or later)

// ---------------------------------------------------------------------------
// Connected components

///|
fn d_connected_components(gr : Value) -> Value raise {
  require_graph(q_connected_components, Fix(1L), gr) |> ignore
  if num_eq(Fix(0L), share_graphs__graph_order(gr)) {
    return share_graphs__ml(Nil)
  }
  let mut components : Value = Nil
  let visited = make_hash_table()
  for v in vertices(gr).iter() {
    if !gethash(v, visited).truthy() {
      let mut c : Value = Nil
      let mut active : Value = Nil
      active = cons(v, active)
      while active.truthy() {
        let x = car(active)
        active = cdr(active)
        c = cons(x, c)
        sethash(x, visited, t) |> ignore
        for u in neighbors(x, gr).iter() {
          if !(gethash(u, visited).truthy() || member(u, active).truthy()) {
            active = cons(u, active)
          }
        }
      }
      components = cons(share_graphs__ml(c), components)
    }
  }
  share_graphs__ml(components)
}

///|
fn d_is_connected(gr : Value) -> Value raise {
  require_graph(q_is_connected, Fix(1L), gr) |> ignore
  lbool(num_le(d_length(d_connected_components(gr)), Fix(1L)))
}

///|
fn d_is_tree(gr : Value) -> Value raise {
  require_graph(q_is_tree, Fix(1L), gr) |> ignore
  if d_is_connected(gr).truthy() {
    lbool(
      num_eq(
        share_graphs__graph_order(gr),
        num_add(Fix(1L), share_graphs__graph_size(gr)),
      ),
    )
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// Reachable vertices

///|
fn d_reachable_vertices(v : Value, gr : Value) -> Value raise {
  require_graph_or_digraph(q_reachable_vertices, Fix(2L), gr) |> ignore
  require_vertex(q_reachable_vertices, Fix(1L), v) |> ignore
  require_vertex_in_graph(q_reachable_vertices, v, gr) |> ignore
  let order = if share_graphs__graph_p(gr) {
    share_graphs__graph_order(gr)
  } else {
    share_graphs__digraph_order(gr)
  }
  if num_eq(Fix(0L), order) {
    return share_graphs__ml(Nil)
  }
  let mut component : Value = Nil
  let visited = make_hash_table()
  if !gethash(v, visited).truthy() {
    let mut active : Value = Nil
    active = cons(v, active)
    while active.truthy() {
      let x = car(active)
      active = cdr(active)
      component = cons(x, component)
      sethash(x, visited, t) |> ignore
      let nb = if share_graphs__graph_p(gr) {
        neighbors(x, gr)
      } else {
        out_h_neighbors(x, gr)
      }
      for u in nb.iter() {
        if !(gethash(u, visited).truthy() || member(u, active).truthy()) {
          active = cons(u, active)
        }
      }
    }
  }
  share_graphs__ml(component)
}

// ---------------------------------------------------------------------------
// Adjacency matrix and Laplacian matrix

///|
/// `(setf (nth (1+ i) (nth (1+ j) m)) v)` with i, j the canonical names.
fn share_graphs__mat_set(m : Value, j : Value, i : Value, v : Value) -> Unit raise {
  share_graphs__setf_nth(to_int(i) + 1, nth(to_int(j) + 1, m), v) |> ignore
}

///|
fn d_adjacency_matrix(gr : Value) -> Value raise {
  require_graph_or_digraph(q_adjacency_matrix, Fix(1L), gr) |> ignore
  let n = if share_graphs__graph_p(gr) {
    share_graphs__graph_order(gr)
  } else {
    share_graphs__digraph_order(gr)
  }
  let m = d_zeromatrix(n, n)
  let names = get_canonical_names(vertices(gr))
  for e in edges(gr).iter() {
    share_graphs__mat_set(
      m,
      cdr(assoc(cadr(e), names)),
      cdr(assoc(car(e), names)),
      Fix(1L),
    )
    if share_graphs__graph_p(gr) {
      share_graphs__mat_set(
        m,
        cdr(assoc(car(e), names)),
        cdr(assoc(cadr(e), names)),
        Fix(1L),
      )
    }
  }
  m
}

///|
fn d_laplacian_matrix(gr : Value) -> Value raise {
  require_graph(q_laplacian_matrix, Fix(1L), gr) |> ignore
  let m = d_zeromatrix(share_graphs__graph_order(gr), share_graphs__graph_order(gr))
  let names = get_canonical_names(vertices(gr))
  for v in share_graphs__graph_vertices(gr).iter() {
    share_graphs__mat_set(
      m,
      cdr(assoc(v, names)),
      cdr(assoc(v, names)),
      int(length(neighbors(v, gr))),
    )
  }
  for e in share_graphs__graph_edges(gr).iter() {
    share_graphs__mat_set(
      m,
      cdr(assoc(cadr(e), names)),
      cdr(assoc(car(e), names)),
      Fix(-1L),
    )
    share_graphs__mat_set(
      m,
      cdr(assoc(car(e), names)),
      cdr(assoc(cadr(e), names)),
      Fix(-1L),
    )
  }
  m
}

///|
fn d_graph_charpoly(gr : Value, x : Value) -> Value raise {
  require_graph(q_graph_charpoly, Fix(1L), gr) |> ignore
  with_special(q_d_ratmx, t, () => d_charpoly(d_adjacency_matrix(gr), x))
}

///|
fn d_graph_eigenvalues(gr : Value) -> Value raise {
  require_graph(q_graph_eigenvalues, Fix(1L), gr) |> ignore
  with_special(q_d_ratmx, t, () => {
    mfuncall(q_d_eigenvalues, list1(d_adjacency_matrix(gr)))
  })
}

// ---------------------------------------------------------------------------
// girth, odd_girth

///|
fn d_girth(gr : Value) -> Value raise {
  require_graph(q_girth, Fix(1L), gr) |> ignore
  girth(gr, Nil)
}

///|
fn d_odd_girth(gr : Value) -> Value raise {
  require_graph(q_odd_girth, Fix(1L), gr) |> ignore
  girth(gr, t)
}

///|
fn girth(gr : Value, odd : Value) -> Value raise {
  let mut girth = to_int(share_graphs__graph_order(gr)) + 1
  for v in share_graphs__graph_vertices(gr).iter() {
    let visited = new_set(list1(v))
    let mut active = new_set(list1(v))
    let mut depth = 1
    while !(set_emptyp(active).truthy() || 2 * depth > girth || girth <= 3) {
      let next = new_set(Nil)
      for u in set_elements(active).iter() {
        for w in neighbors(u, gr).iter() {
          if !set_member(w, visited).truthy() {
            set_add(w, visited) |> ignore
            set_add(w, next) |> ignore
          } else {
            if set_member(w, active).truthy() {
              girth = 2 * depth - 1
            }
            if !odd.truthy() && set_member(w, next).truthy() {
              girth = if girth < 2 * depth { girth } else { 2 * depth }
            }
          }
        }
      }
      active = next
      depth = depth + 1
    }
  }
  if num_gt(int(girth), share_graphs__graph_order(gr)) {
    q_d_inf
  } else {
    int(girth)
  }
}

// ---------------------------------------------------------------------------
// diameter, radius

///|
fn d_vertex_eccentricity(v : Value, gr : Value) -> Value raise {
  require_graph(q_vertex_eccentricity, Fix(1L), gr) |> ignore
  require_vertex_in_graph(q_vertex_eccentricity, v, gr) |> ignore
  let ecc = eccentricity(list1(v), gr)
  gethash(v, ecc)
}

///|
fn eccentricity(v_list : Value, gr : Value) -> Value raise {
  if !d_is_connected(gr).truthy() {
    share_graphs__error([Str("eccentricity: graph is not connected.")])
    |> ignore
  }
  let ecc = make_hash_table()
  for v in v_list.iter() {
    let visited = new_set(list1(v))
    let mut active = new_set(list1(v))
    let mut depth = -1
    while !set_emptyp(active).truthy() {
      let next = new_set(Nil)
      for u in set_elements(active).iter() {
        for w in neighbors(u, gr).iter() {
          if !set_member(w, visited).truthy() {
            set_add(w, visited) |> ignore
            set_add(w, next) |> ignore
          }
        }
      }
      active = next
      depth = depth + 1
    }
    sethash(v, ecc, int(depth)) |> ignore
  }
  ecc
}

///|
fn d_diameter(gr : Value) -> Value raise {
  require_graph(q_diameter, Fix(1L), gr) |> ignore
  let ecc = eccentricity(vertices(gr), gr)
  let mut diameter : Value = Fix(0L)
  maphash((_, val) => if num_gt(val, diameter) { diameter = val }, ecc)
  diameter
}

///|
fn d_radius(gr : Value) -> Value raise {
  require_graph(q_radius, Fix(1L), gr) |> ignore
  let ecc = eccentricity(vertices(gr), gr)
  let mut radius = d_graph_order(gr)
  maphash((_, val) => if num_lt(val, radius) { radius = val }, ecc)
  radius
}

///|
fn d_graph_center(gr : Value) -> Value raise {
  require_graph(q_graph_center, Fix(1L), gr) |> ignore
  let ecc = eccentricity(vertices(gr), gr)
  let mut per : Value = Nil
  let mut radius = d_graph_order(gr)
  maphash((_, val) => if num_lt(val, radius) { radius = val }, ecc)
  maphash((key, val) => if num_eq(val, radius) { per = cons(key, per) }, ecc)
  share_graphs__ml(per)
}

///|
fn d_graph_periphery(gr : Value) -> Value raise {
  require_graph(q_graph_periphery, Fix(1L), gr) |> ignore
  let ecc = eccentricity(vertices(gr), gr)
  let mut center : Value = Nil
  let mut diameter : Value = Fix(0L)
  maphash((_, val) => if num_gt(val, diameter) { diameter = val }, ecc)
  maphash(
    (key, val) => if num_eq(val, diameter) { center = cons(key, center) },
    ecc,
  )
  share_graphs__ml(center)
}

// ---------------------------------------------------------------------------
// bipartition

///|
fn d_bipartition(gr : Value) -> Value raise {
  require_graph(q_bipartition, Fix(1L), gr) |> ignore
  if num_eq(share_graphs__graph_order(gr), Fix(0L)) {
    return share_graphs__ml(
      list([share_graphs__ml(Nil), share_graphs__ml(Nil)]),
    )
  }
  let components = cdr(d_connected_components(gr))
  let mut a : Value = Nil
  let mut b : Value = Nil
  for c in components.iter() {
    let partition = bi_partition(car(cdr(c)), gr)
    if partition is Nil {
      return share_graphs__ml(Nil)
    } else {
      a = append(a, car(partition))
      b = append(b, cadr(partition))
    }
  }
  share_graphs__ml(list([share_graphs__ml(a), share_graphs__ml(b)]))
}

///|
fn bi_partition(v : Value, gr : Value) -> Value raise {
  let mut a : Value = Nil
  let mut b : Value = Nil
  let visited = new_set(Nil)
  let mut active = list1(v)
  let colors = make_hash_table()
  sethash(v, colors, Fix(1L)) |> ignore
  while active.truthy() {
    let w = car(active)
    active = cdr(active)
    let wc = gethash(w, colors)
    set_add(w, visited) |> ignore
    if num_eq(wc, Fix(1L)) {
      a = cons(w, a)
    } else {
      b = cons(w, b)
    }
    for u in neighbors(w, gr).iter() {
      if set_member(u, visited).truthy() {
        if num_eq(gethash(u, colors), wc) {
          return Nil
        }
      } else if !member(u, active).truthy() {
        active = cons(u, active)
        sethash(u, colors, num_sub(Fix(1L), wc)) |> ignore
      }
    }
  }
  list([a, b])
}

///|
fn d_is_bipartite(gr : Value) -> Value raise {
  require_graph(q_is_bipartite, Fix(1L), gr) |> ignore
  lbool(num_gt(d_length(d_bipartition(gr)), Fix(1L)))
}

// ---------------------------------------------------------------------------
// 2-connectivity

///|
fn d_biconnected_components(gr : Value) -> Value raise {
  require_graph(q_biconnected_components, Fix(1L), gr) |> ignore
  if num_eq(Fix(0L), share_graphs__graph_order(gr)) {
    share_graphs__ml(Nil)
  } else {
    let mut bicomp = share_graphs__ml(Nil)
    let comp = cdr(d_connected_components(gr))
    for c in comp.iter() {
      if num_eq(d_length(c), Fix(1L)) {
        bicomp = d_append(list([bicomp, share_graphs__ml(list1(c))]))
      } else {
        bicomp = d_append(list([bicomp, bicomponents(d_first(c), gr)]))
      }
    }
    bicomp
  }
}

///|
fn d_is_biconnected(gr : Value) -> Value raise {
  require_graph(q_is_biconnected, Fix(1L), gr) |> ignore
  lbool(eql(d_length(d_biconnected_components(gr)), Fix(1L)))
}

///|
fn bicomponents(v : Value, gr : Value) -> Value raise {
  let mut bicomp : Value = Nil
  set(q_ear_dfs_bicomp_depth, Fix(0L)) |> ignore
  set(q_ear_dfs_bicomp_num, make_hash_table()) |> ignore
  set(q_ear_dfs_bicomp_low_pt, make_hash_table()) |> ignore
  set(q_ear_dfs_bicomp_edges, make_hash_table()) |> ignore
  set(q_ear_bicomponents, Nil) |> ignore
  for v in share_graphs__graph_vertices(gr).iter() {
    sethash(v, symval(q_ear_dfs_bicomp_num), Fix(0L)) |> ignore
  }
  dfs_bicomponents(gr, v) |> ignore
  for c in symval(q_ear_bicomponents).iter() {
    let mut curr_comp : Value = Nil
    for e in c.iter() {
      let u = car(e)
      let v = cadr(e)
      if !member(u, curr_comp).truthy() {
        curr_comp = cons(u, curr_comp)
      }
      if !member(v, curr_comp).truthy() {
        curr_comp = cons(v, curr_comp)
      }
    }
    bicomp = cons(
      share_graphs__ml(sort_list(curr_comp, (a, b) => num_lt(a, b))),
      bicomp,
    )
  }
  share_graphs__ml(bicomp)
}

///|
fn dfs_bicomponents(gr : Value, w : Value) -> Value raise {
  set(q_ear_dfs_bicomp_depth, num_add(symval(q_ear_dfs_bicomp_depth), Fix(1L)))
  |> ignore
  let num = symval(q_ear_dfs_bicomp_num)
  let low_pt = symval(q_ear_dfs_bicomp_low_pt)
  sethash(w, num, symval(q_ear_dfs_bicomp_depth)) |> ignore
  sethash(w, low_pt, symval(q_ear_dfs_bicomp_depth)) |> ignore
  for u in neighbors(w, gr).iter() {
    if num_lt(gethash(u, num), gethash(w, num)) {
      set(q_ear_dfs_bicomp_edges, cons(list([w, u]), symval(q_ear_dfs_bicomp_edges)))
      |> ignore
    }
    if num_eq(Fix(0L), gethash(u, num)) {
      dfs_bicomponents(gr, u) |> ignore
      if num_ge(gethash(u, low_pt), gethash(w, num)) {
        let mut e : Value = Fix(0L)
        let mut comp : Value = Nil
        let wu = list([w, u])
        while !equal(e, wu) {
          let edges_ = symval(q_ear_dfs_bicomp_edges)
          e = car(edges_)
          set(q_ear_dfs_bicomp_edges, cdr(edges_)) |> ignore
          comp = cons(e, comp)
        }
        set(q_ear_bicomponents, cons(comp, symval(q_ear_bicomponents))) |> ignore
      } else {
        sethash(w, low_pt, num_min(gethash(w, low_pt), gethash(u, low_pt)))
        |> ignore
      }
    } else {
      sethash(w, low_pt, num_min(gethash(w, low_pt), gethash(u, num))) |> ignore
    }
  }
  Nil
}

// ---------------------------------------------------------------------------
// strong connectivity

///|
fn d_strong_components(gr : Value) -> Value raise {
  require_digraph(q_strong_components, Fix(1L), gr) |> ignore
  if num_eq(Fix(0L), share_graphs__digraph_order(gr)) {
    share_graphs__ml(Nil)
  } else {
    let mut res : Value = Nil
    set(q_ear_scon_low, make_hash_table()) |> ignore
    set(q_ear_scon_dfn, make_hash_table()) |> ignore
    set(q_ear_scon_comp, Nil) |> ignore
    set(q_ear_scon_st, Nil) |> ignore
    set(q_ear_scon_vrt, share_graphs__digraph_vertices(gr)) |> ignore
    while symval(q_ear_scon_vrt).truthy() {
      set(q_ear_scon_depth, Fix(0L)) |> ignore
      dfs_strong_components(gr, car(symval(q_ear_scon_vrt))) |> ignore
      for c in symval(q_ear_scon_comp).iter() {
        res = cons(c, res)
      }
      set(q_ear_scon_comp, Nil) |> ignore
    }
    share_graphs__ml(res)
  }
}

///|
fn d_is_sconnected(gr : Value) -> Value raise {
  require_digraph(q_strong_components, Fix(1L), gr) |> ignore
  lbool(eql(d_length(d_strong_components(gr)), Fix(1L)))
}

///|
fn dfs_strong_components(gr : Value, v : Value) -> Value raise {
  set(q_ear_scon_depth, num_add(symval(q_ear_scon_depth), Fix(1L))) |> ignore
  let dfn = symval(q_ear_scon_dfn)
  let low = symval(q_ear_scon_low)
  sethash(v, dfn, symval(q_ear_scon_depth)) |> ignore
  sethash(v, low, symval(q_ear_scon_depth)) |> ignore
  set(q_ear_scon_vrt, share_graphs__remove1(v, symval(q_ear_scon_vrt))) |> ignore
  set(q_ear_scon_st, cons(v, symval(q_ear_scon_st))) |> ignore
  for u in neighbors(v, gr).iter() {
    if gethash(u, dfn).truthy() {
      if num_lt(gethash(u, dfn), gethash(v, dfn)) &&
        member(u, symval(q_ear_scon_st)).truthy() {
        sethash(v, low, num_min(gethash(v, low), gethash(u, dfn))) |> ignore
      }
    } else {
      dfs_strong_components(gr, u) |> ignore
      sethash(v, low, num_min(gethash(v, low), gethash(u, low))) |> ignore
    }
  }
  if num_eq(gethash(v, low), gethash(v, dfn)) {
    let pop = () => {
      let st = symval(q_ear_scon_st)
      set(q_ear_scon_st, cdr(st)) |> ignore
      car(st)
    }
    let mut x = pop()
    let mut comp : Value = Nil
    while !num_eq(x, v) {
      comp = cons(x, comp)
      x = pop()
    }
    comp = cons(x, comp)
    set(q_ear_scon_comp, cons(share_graphs__ml(comp), symval(q_ear_scon_comp)))
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// topological sorting

///|
fn d_topological_sort(dag : Value) -> Value raise {
  require_digraph(q_topological_sort, Fix(1L), dag) |> ignore
  let in_degrees = make_hash_table()
  let mut q : Value = Nil
  let mut n = d_graph_size(dag)
  let mut s : Value = Nil
  for v in vertices(dag).iter() {
    sethash(v, in_degrees, Fix(0L)) |> ignore
  }
  for e in edges(dag).iter() {
    share_graphs__incf_hash(cadr(e), in_degrees, Fix(1L)) |> ignore
  }
  for v in vertices(dag).iter() {
    if num_eq(gethash(v, in_degrees), Fix(0L)) {
      q = cons(v, q)
    }
  }
  while length(q) > 0 {
    let v = car(q)
    q = cdr(q)
    s = cons(v, s)
    for u in out_h_neighbors(v, dag).iter() {
      share_graphs__incf_hash(u, in_degrees, Fix(-1L)) |> ignore
      n = num_sub(n, Fix(1L))
      if num_eq(gethash(u, in_degrees), Fix(0L)) {
        q = cons(u, q)
      }
    }
  }
  if num_eq(n, Fix(0L)) {
    share_graphs__ml(reverse(s))
  } else {
    share_graphs__ml(Nil)
  }
}

// ---------------------------------------------------------------------------
// max_flow (augmenting paths)

///|
fn d_max_flow(net : Value, source : Value, sink : Value) -> Value raise {
  require_digraph(q_max_flow, Fix(1L), net) |> ignore
  require_vertex(q_max_flow, Fix(2L), source) |> ignore
  require_vertex(q_max_flow, Fix(3L), sink) |> ignore
  require_vertex_in_graph(q_max_flow, source, net) |> ignore
  require_vertex_in_graph(q_max_flow, sink, net) |> ignore
  with_special(q_d_ratprint, Nil, () => {
    let d = make_hash_table()
    let mut active : Value = Nil
    let mut lbls = make_hash_table()
    let flow = make_hash_table(kind=Equal)
    let mut val : Value = Fix(0L)
    for e in share_graphs__digraph_edges(net).iter() {
      sethash(e, flow, Fix(0L)) |> ignore
    }
    for v in share_graphs__digraph_vertices(net).iter() {
      sethash(v, d, q_d_inf) |> ignore
    }
    sethash(source, lbls, list([source, Fix(-1L), q_d_inf])) |> ignore
    active = cons(source, active)
    while active.truthy() {
      let v = car(active)
      active = cdr(active)
      for w in out_h_neighbors(v, net).iter() {
        let vw = list([v, w])
        if gethash(w, lbls) is Nil &&
          mlsp(gethash(vw, flow), {
            let ew = get_h_edge_h_weight(vw, net)
            if ew.truthy() {
              ew
            } else {
              Fix(1L)
            }
          }).truthy() {
          let ew = get_h_edge_h_weight(vw, net)
          sethash(
            w,
            d,
            mfuncall(
              q_d_min,
              list([
                sub_star(if ew.truthy() { ew } else { Fix(1L) }, gethash(vw, flow)),
                gethash(v, d),
              ]),
            ),
          )
          |> ignore
          sethash(w, lbls, list([v, Fix(1L), gethash(w, d)])) |> ignore
          active = cons(w, active)
        }
      }
      for w in in_h_neighbors(v, net).iter() {
        let wv = list([w, v])
        if gethash(w, lbls) is Nil && mgrp(gethash(wv, flow), Fix(0L)).truthy() {
          sethash(
            w,
            d,
            mfuncall(q_d_min, list([gethash(wv, flow), gethash(v, d)])),
          )
          |> ignore
          sethash(w, lbls, list([v, Fix(-1L), gethash(w, d)])) |> ignore
          active = cons(w, active)
        }
      }
      if gethash(sink, lbls).truthy() {
        let dd = caddr(gethash(sink, lbls))
        let mut w = sink
        val = add_star(list([dd, val]))
        while !num_eq(w, source) {
          let v1 = car(gethash(w, lbls))
          let vl = cadr(gethash(w, lbls))
          if num_eq(vl, Fix(1L)) {
            let k = list([v1, w])
            sethash(k, flow, add_star(list([gethash(k, flow), dd]))) |> ignore
          } else {
            let k = list([w, v1])
            sethash(k, flow, sub_star(gethash(k, flow), dd)) |> ignore
          }
          w = v1
        }
        lbls = make_hash_table()
        sethash(source, lbls, list([source, Fix(-1L), q_d_inf])) |> ignore
        for v1 in share_graphs__digraph_vertices(net).iter() {
          sethash(v1, d, q_d_inf) |> ignore
        }
        active = list1(source)
      }
    }
    let mut max_flow : Value = Nil
    for e in share_graphs__digraph_edges(net).iter() {
      max_flow = cons(
        share_graphs__ml(list([share_graphs__ml(e), gethash(e, flow)])),
        max_flow,
      )
    }
    share_graphs__ml(list([val, share_graphs__ml(max_flow)]))
  })
}

// ---------------------------------------------------------------------------
// shortest path

///|
fn d_shortest_path(u : Value, v : Value, g : Value) -> Value raise {
  require_graph_or_digraph(q_shortest_path, Fix(3L), g) |> ignore
  require_vertex(q_shortest_path, Fix(1L), u) |> ignore
  require_vertex(q_shortest_path, Fix(2L), v) |> ignore
  require_vertex_in_graph(q_shortest_path, v, g) |> ignore
  require_vertex_in_graph(q_shortest_path, u, g) |> ignore
  let mut active = make_hash_table()
  let visited = make_hash_table()
  let previous = make_hash_table()
  sethash(u, active, t) |> ignore
  while !(hash_table_count(active) == 0 || gethash(v, visited).truthy()) {
    let next = make_hash_table()
    maphash(
      (w, _) => {
        sethash(w, visited, t) |> ignore
        for x in neighbors(w, g).iter() {
          if !(gethash(x, active).truthy() ||
            gethash(x, visited).truthy() ||
            gethash(x, next).truthy()) {
            sethash(x, previous, w) |> ignore
            sethash(x, next, t) |> ignore
          }
        }
      },
      active,
    )
    active = next
  }
  if gethash(v, visited).truthy() {
    let mut path = list1(v)
    let mut x = v
    while !num_eq(x, u) {
      x = gethash(x, previous)
      path = cons(x, path)
    }
    share_graphs__ml(path)
  } else {
    share_graphs__ml(Nil)
  }
}

///|
fn d_vertex_distance(u : Value, v : Value, g : Value) -> Value raise {
  require_graph_or_digraph(q_shortest_path, Fix(3L), g) |> ignore
  require_vertex(q_shortest_path, Fix(1L), u) |> ignore
  require_vertex(q_shortest_path, Fix(2L), v) |> ignore
  require_vertex_in_graph(q_shortest_path, v, g) |> ignore
  require_vertex_in_graph(q_shortest_path, u, g) |> ignore
  let d = d_length(d_shortest_path(u, v, g))
  if num_gt(d, Fix(0L)) {
    num_sub(d, Fix(1L))
  } else {
    q_d_inf
  }
}

// ---------------------------------------------------------------------------
// minimum spanning tree

///|
fn edge_weight_1(e : Value, gr : Value) -> Value raise {
  let w = gethash(e, share_graphs__graph_edge_weights(gr))
  if w.truthy() {
    w
  } else {
    Fix(1L)
  }
}

///|
fn graph_edges_with_weights(gr : Value) -> Value raise {
  let edges = share_graphs__graph_edges(gr)
  let mut edges_with_weights : Value = Nil
  for e in edges.iter() {
    edges_with_weights = cons(list([e, edge_weight_1(e, gr)]), edges_with_weights)
  }
  edges_with_weights
}

///|
fn edges_by_weights(gr : Value) -> Value raise {
  let edges = graph_edges_with_weights(gr)
  sort_list(edges, (u, v) => mlsp(cadr(u), cadr(v)).truthy())
}

///|
fn in_same_part(u : Value, v : Value, p : Value) -> Value raise {
  let mut up = u
  let mut vp = v
  while !num_eq(up, gethash(up, p)) {
    let up1 = gethash(up, p)
    sethash(up, p, gethash(up1, p)) |> ignore
    up = gethash(up, p)
  }
  while !num_eq(vp, gethash(vp, p)) {
    let vp1 = gethash(vp, p)
    sethash(vp, p, gethash(vp1, p)) |> ignore
    vp = gethash(vp, p)
  }
  lbool(num_eq(up, vp))
}

///|
fn join_parts(u : Value, v : Value, p : Value) -> Value raise {
  let mut up = u
  let mut vp = v
  while !num_eq(up, gethash(up, p)) {
    up = gethash(up, p)
  }
  while !num_eq(vp, gethash(vp, p)) {
    vp = gethash(vp, p)
  }
  sethash(up, p, gethash(vp, p))
}

///|
fn d_minimum_spanning_tree(gr : Value) -> Value raise {
  require_graph(q_minimum_spanning_tree, Fix(1L), gr) |> ignore
  let edges = edges_by_weights(gr)
  let tr = share_graphs__make_graph()
  let part = make_hash_table()
  for v in share_graphs__graph_vertices(gr).iter() {
    add_h_vertex(v, tr) |> ignore
    sethash(v, part, v) |> ignore
  }
  for e in edges.iter() {
    let u = caar(e)
    let v = cadar(e)
    if !in_same_part(u, v, part).truthy() {
      add_h_edge(list([u, v]), tr) |> ignore
      join_parts(u, v, part) |> ignore
    }
  }
  tr
}

// ---------------------------------------------------------------------------
// hamilton cycle

///|
fn d_hamilton_cycle(gr : Value) -> Value raise {
  require_graph(q_hamilton_cycle, Fix(1L), gr) |> ignore
  let v0 = d_first_vertex(gr)
  with_specials([(q_ear_hamilton_cycle, Nil), (q_ear_v0, v0)], () => {
    if !d_is_biconnected(gr).truthy() {
      return share_graphs__ml(Nil)
    }
    hamilton_h_cycle(list1(symval(q_ear_v0)), gr) |> ignore
    share_graphs__ml(reverse(symval(q_ear_hamilton_cycle)))
  })
}

///|
fn hamilton_h_cycle(part : Value, gr : Value) -> Value raise {
  if symval(q_ear_hamilton_cycle).truthy() {
    return Nil
  }
  let order = if share_graphs__graph_p(gr) {
    share_graphs__graph_order(gr)
  } else {
    share_graphs__digraph_order(gr)
  }
  if num_eq(int(length(part)), order) {
    if member(car(last(part)), neighbors(car(part), gr)).truthy() {
      set(q_ear_hamilton_cycle, append(last(part), part)) |> ignore
    }
  }
  for v in neighbors(car(part), gr).iter() {
    if member(v, part) is Nil {
      if length(part) < 3 {
        hamilton_h_cycle(cons(v, part), gr) |> ignore
      } else {
        let gr1 = d_copy_graph(gr)
        let in_part = cdr(reverse(part))
        d_remove_vertices(cons(list([q_mlist, q_simp]), in_part), gr1) |> ignore
        let v0 = symval(q_ear_v0)
        if !member(v, neighbors(v0, gr)).truthy() {
          d_add_edge(share_graphs__ml(list([v, v0])), gr1) |> ignore
        }
        if d_is_biconnected(gr1).truthy() {
          hamilton_h_cycle(cons(v, part), gr) |> ignore
        }
      }
    }
  }
  Nil
}

///|
fn d_hamilton_path(gr : Value) -> Value raise {
  require_graph(q_hamilton_path, Fix(1L), gr) |> ignore
  // first check if there exists a HC
  let hc = d_hamilton_cycle(gr)
  if cdr(hc).truthy() {
    return d_rest(hc)
  }
  // check with all non-edges
  let grc = d_complement_graph(gr)
  for v in vertices(gr).iter() {
    for u in neighbors(v, grc).iter() {
      if num_lt(v, u) {
        let found = with_specials([(q_ear_v0, v), (q_ear_hamilton_cycle, Nil)], () => {
          let part = list([u, v])
          hamilton_h_cycle(part, gr) |> ignore
          if symval(q_ear_hamilton_cycle).truthy() {
            Some(share_graphs__ml(cdr(reverse(symval(q_ear_hamilton_cycle)))))
          } else {
            None
          }
        })
        if found is Some(r) {
          return r
        }
      }
    }
  }
  share_graphs__ml(Nil)
}

// ---------------------------------------------------------------------------
// maximum clique

///|
fn d_vertices_by_degree(gr : Value) -> Value raise {
  require_graph(q_vertices_by_degrees, Fix(1L), gr) |> ignore
  cons(list([q_mlist, q_simp]), vertices_h_by_h_degrees(gr))
}

///|
fn vertices_h_by_h_degrees(gr : Value) -> Value raise {
  let mut vrt : Value = Nil
  for v in vertices(gr).iter() {
    vrt = cons(list([v, int(length(neighbors(v, gr)))]), vrt)
  }
  vrt = sort_list(vrt, (u, v) => num_gt(cadr(u), cadr(v)))
  mapcar(x => car(x), vrt)
}

///|
fn greedy_color(gr : Value) -> Value raise {
  let coloring = make_hash_table()
  let available_colors = make_hash_table()
  let mut tmp : Value = Nil
  for i in 0..<to_int(share_graphs__graph_order(gr)) {
    tmp = cons(int(i), tmp)
  }
  tmp = reverse(tmp)
  for v in share_graphs__graph_vertices(gr).iter() {
    sethash(v, available_colors, copy_tree(tmp)) |> ignore
  }
  for v in vertices_h_by_h_degrees(gr).iter() {
    let c = car(gethash(v, available_colors))
    sethash(v, coloring, c) |> ignore
    for u in neighbors(v, gr).iter() {
      sethash(
        u,
        available_colors,
        share_graphs__remove1(c, gethash(u, available_colors)),
      )
      |> ignore
    }
  }
  coloring
}

///|
fn d_max_clique(gr : Value) -> Value raise {
  require_graph(q_max_clique, Fix(1L), gr) |> ignore
  set(q_ear_maximum_clique, Nil) |> ignore
  let h = d_copy_graph(gr)
  while !(
      num_ge(
        int(length(symval(q_ear_maximum_clique))),
        share_graphs__graph_order(h),
      ) ||
      num_gt(int(length(symval(q_ear_maximum_clique))), d_first(d_max_degree(h)))
    ) {
    let coloring = greedy_color(h)
    let v = funcall(q_d_second, [d_max_degree(h)])
    extend_clique(list1(v), neighbors(v, h), coloring, h) |> ignore
    remove_h_vertex(v, h) |> ignore
  }
  share_graphs__ml(
    sort_list(symval(q_ear_maximum_clique), (a, b) => num_lt(a, b)),
  )
}

///|
fn d_min_vertex_cover(gr : Value) -> Value raise {
  require_graph(q_min_vertex_cover, Fix(1L), gr) |> ignore
  let bipart = d_bipartition(gr)
  if cdr(bipart) is Nil {
    let mut vc : Value = Nil
    let mc = cdr(d_max_clique(d_complement_graph(gr)))
    for v in vertices(gr).iter() {
      if !member(v, mc).truthy() {
        vc = cons(v, vc)
      }
    }
    share_graphs__ml(vc)
  } else {
    maximum_matching_bipartite(gr, cadr(bipart), caddr(bipart), cover=t)
  }
}

///|
fn d_max_independent_set(gr : Value) -> Value raise {
  require_graph(q_max_independent_set, Fix(1L), gr) |> ignore
  if d_is_bipartite(gr).truthy() {
    let mut mis : Value = Nil
    let vc = cdr(d_min_vertex_cover(gr))
    for v in vertices(gr).iter() {
      if !member(v, vc).truthy() {
        mis = cons(v, mis)
      }
    }
    share_graphs__ml(mis)
  } else {
    d_max_clique(d_complement_graph(gr))
  }
}

///|
fn extend_clique(
  clique : Value,
  neigh : Value,
  coloring : Value,
  gr : Value,
) -> Value raise {
  let mut neigh = neigh
  if length(neigh) == 0 {
    // did we get to a maximal clique
    if length(clique) > length(symval(q_ear_maximum_clique)) {
      set(q_ear_maximum_clique, clique) |> ignore
      return Nil
    }
    Nil
  } else {
    // can we do better?
    let mut colors : Value = Nil
    for x in neigh.iter() {
      if !member(gethash(x, coloring), colors).truthy() {
        colors = cons(gethash(x, coloring), colors)
      }
    }
    if length(clique) + length(colors) > length(symval(q_ear_maximum_clique)) {
      // try improving
      while length(neigh) != 0 {
        let x = car(neigh)
        let new_clique = cons(x, clique)
        let mut new_neigh : Value = Nil
        for y in neigh.iter() {
          if is_h_edge_h_in_h_graph(list([num_min(x, y), num_max(x, y)]), gr).truthy() {
            new_neigh = cons(y, new_neigh)
          }
        }
        extend_clique(new_clique, new_neigh, coloring, gr) |> ignore
        neigh = remove(x, neigh)
      }
    }
    Nil
  }
}

// ---------------------------------------------------------------------------
// colorings

///|
fn d_vertex_coloring(g : Value) -> Value raise {
  require_graph(q_vertex_coloring, Fix(1L), g) |> ignore
  let col = dsatur(g)
  let mut res : Value = Nil
  let mut chnumber : Value = Fix(0L)
  for v in vertices(g).iter() {
    res = cons(share_graphs__ml(list([v, gethash(v, col)])), res)
    chnumber = num_max(chnumber, gethash(v, col))
  }
  share_graphs__ml(list([chnumber, share_graphs__ml(res)]))
}

///|
fn d_chromatic_number(g : Value) -> Value raise {
  require_graph(q_chromatic_number, Fix(1L), g) |> ignore
  d_first(d_vertex_coloring(g))
}

///|
fn d_edge_coloring(gr : Value) -> Value raise {
  require_graph(q_edge_coloring, Fix(1L), gr) |> ignore
  let edge_list = get_canonical_names(share_graphs__graph_edges(gr))
  let n = share_graphs__graph_size(gr)
  let g = d_empty_graph(n)
  let nn = to_int(n)
  for i in 0..<nn {
    for j in (i + 1)..<nn {
      let e = car(rassoc(int(i), edge_list))
      let f = car(rassoc(int(j), edge_list))
      if member(car(e), f).truthy() || member(cadr(e), f).truthy() {
        add_h_edge(list([int(i), int(j)]), g) |> ignore
      }
    }
  }
  let coloring = dsatur(g)
  let mut ch_index : Value = Fix(-1L)
  let mut res : Value = Nil
  for i in 0..<nn {
    res = cons(
      share_graphs__ml(
        list([
          share_graphs__ml(car(rassoc(int(i), edge_list))),
          gethash(int(i), coloring),
        ]),
      ),
      res,
    )
    ch_index = num_max(ch_index, gethash(int(i), coloring))
  }
  share_graphs__ml(list([ch_index, share_graphs__ml(res)]))
}

///|
fn d_chromatic_index(g : Value) -> Value raise {
  require_graph(q_chromatic_index, Fix(1L), g) |> ignore
  d_first(d_vertex_coloring(d_line_graph(g)))
}

///|
fn dsatur(g : Value) -> Value raise {
  if length(vertices(g)) < 2 {
    let col = make_hash_table()
    for v in vertices(g).iter() {
      sethash(v, col, Fix(1L)) |> ignore
    }
    return col
  }
  let mut x : Value = Nil
  let vsize = length(vertices(g))
  let mut opt_chnumber = vsize + 1
  let mut back = false
  let mut i = 0
  let mut k = 0
  let mut free_color = 0
  let mut xindex = 0
  let mut stop = false
  let clique = greedy_clique(g)
  let clique_size = length(clique)
  let mut start = clique_size
  let a : Array[Value] = Array::make(vsize, Fix(0L))
  let f = make_hash_table()
  let f_opt = make_hash_table()
  let number_of_used_colors = make_hash_table(kind=Equal)
  let dsat = make_hash_table()
  let uncolored = make_hash_table()
  let gi = (k : Value, tbl : Value) => to_int(gethash(k, tbl))
  let used = (v : Value, c : Int) => to_int(
    share_graphs__gethash_d(list([v, int(c)]), number_of_used_colors, Fix(0L)),
  )

  // Prepare data
  for v in clique.iter() {
    a[i] = v
    sethash(v, f, int(i + 1)) |> ignore
    i = i + 1
  }
  for v in vertices(g).iter() {
    sethash(v, dsat, Fix(0L)) |> ignore
    sethash(v, uncolored, int(length(neighbors(v, g)))) |> ignore
    if !member(v, clique).truthy() {
      a[i] = v
      i = i + 1
      sethash(v, f, Fix(0L)) |> ignore
    }
  }
  for v in clique.iter() {
    for u in neighbors(v, g).iter() {
      share_graphs__incf_hash(u, uncolored, Fix(-1L)) |> ignore
      sethash(list([u, gethash(v, f)]), number_of_used_colors, Fix(1L)) |> ignore
      share_graphs__incf_hash(u, dsat, Fix(1L)) |> ignore
    }
  }
  while true {
    let mut i = start
    while !(i == vsize || stop) {
      // Choose new vertex x
      if back {
        xindex = start
        x = a[xindex]
      } else {
        let mut mdsat = -1
        let mut munc = -1
        for j in i..<vsize {
          if gi(a[j], dsat) > mdsat ||
            (gi(a[j], dsat) == mdsat && gi(a[j], uncolored) > munc) {
            x = a[j]
            xindex = j
            mdsat = gi(x, dsat)
            munc = gi(x, uncolored)
          }
        }
      }
      // Choose free color
      free_color = 0
      if back {
        back = false
        k = gi(x, f) + 1
      } else {
        k = 1
      }
      let mut j = k
      while !(j >= opt_chnumber || free_color > 0) {
        if used(x, j) == 0 {
          free_color = j
        }
        j = j + 1
      }
      if free_color > 0 {
        // Color vertex x
        sethash(x, f, int(free_color)) |> ignore
        // Update dsat index
        for u in neighbors(x, g).iter() {
          share_graphs__incf_hash(
            list([u, int(free_color)]),
            number_of_used_colors,
            Fix(1L),
            default=Fix(0L),
          )
          |> ignore
          if used(u, free_color) == 1 {
            share_graphs__incf_hash(u, dsat, Fix(1L)) |> ignore
          }
          share_graphs__incf_hash(u, uncolored, Fix(-1L)) |> ignore
        }
        // Update A
        let tmp = a[i]
        a[i] = a[xindex]
        a[xindex] = tmp
      } else {
        // Unable to extend coloring - backtrack
        start = i - 1
        stop = true
        back = true
      }
      i = i + 1
    }
    stop = false
    if back {
      // We have a backtrack step
      if start < clique_size {
        return f_opt
      }
      x = a[start]
      k = gi(x, f)
      // Delete the color of x
      for v in neighbors(x, g).iter() {
        share_graphs__incf_hash(list([v, int(k)]), number_of_used_colors, Fix(-1L))
        |> ignore
        share_graphs__incf_hash(v, uncolored, Fix(1L)) |> ignore
        if used(v, k) == 0 {
          share_graphs__incf_hash(v, dsat, Fix(-1L)) |> ignore
        }
      }
    } else {
      // We have a coloring!
      // Save new optimal coloring
      opt_chnumber = 0
      for v in vertices(g).iter() {
        sethash(v, f_opt, gethash(v, f)) |> ignore
        opt_chnumber = if opt_chnumber > gi(v, f) {
          opt_chnumber
        } else {
          gi(v, f)
        }
      }
      // Find new start
      start = -1
      let mut i = 0
      while !(start > -1) {
        if opt_chnumber == gi(a[i], f_opt) {
          start = i - 1
        }
        i = i + 1
      }
      back = true
      if start < clique_size || opt_chnumber == clique_size {
        return f_opt
      }
      // Delete colors from start
      for i in start..<vsize {
        for v in neighbors(a[i], g).iter() {
          let c = gi(a[i], f)
          share_graphs__incf_hash(
            list([v, int(c)]),
            number_of_used_colors,
            Fix(-1L),
          )
          |> ignore
          share_graphs__incf_hash(v, uncolored, Fix(1L)) |> ignore
          if used(v, c) == 0 {
            share_graphs__incf_hash(v, dsat, Fix(-1L)) |> ignore
          }
        }
      }
    }
  }
  f_opt
}

///|
fn greedy_clique(g : Value) -> Value raise {
  let mut clique : Value = Nil
  for v in vertices(g).iter() {
    let tmp_clique = extend_greedy_clique(list1(v), neighbors(v, g), g)
    if length(tmp_clique) > length(clique) {
      clique = tmp_clique
    }
  }
  clique
}

///|
fn extend_greedy_clique(clique : Value, neigh : Value, g : Value) -> Value raise {
  if 0 == length(neigh) {
    return clique
  }
  if 1 == length(neigh) {
    return cons(car(neigh), clique)
  }
  let mut u : Value = Nil
  let mut new_neigh : Value = Nil
  for v in neigh.iter() {
    let mut tmp_neigh = copy_tree(neigh)
    for w in neigh.iter() {
      if !member(w, neighbors(v, g)).truthy() {
        tmp_neigh = remove(w, tmp_neigh)
      }
    }
    if length(tmp_neigh) >= length(new_neigh) {
      u = v
      new_neigh = tmp_neigh
    }
  }
  if u.truthy() {
    extend_greedy_clique(cons(u, clique), new_neigh, g)
  } else {
    clique
  }
}

// ---------------------------------------------------------------------------
// Expose lisp hashtable

///|
fn d_hash_table() -> Value raise {
  make_hash_table(kind=Equal)
}

///|
fn d_get_hash(elt_ : Value, ht : Value, default? : Value = Nil) -> Value raise {
  if !hash_table_p(ht) {
    share_graphs__error([Str("Second argument to `get_hash' is not a hash table!")])
    |> ignore
  }
  share_graphs__gethash_d(elt_, ht, default)
}

///|
fn d_set_hash(elt_ : Value, ht : Value, value : Value) -> Value raise {
  if !hash_table_p(ht) {
    share_graphs__error([Str("Second argument to `set_hash' is not a hash table!")])
    |> ignore
  }
  sethash(elt_, ht, value) |> ignore
  value
}

///|
fn d_hash_table_data(ht : Value) -> Value raise {
  if !hash_table_p(ht) {
    share_graphs__error([
      Str("First argument to `hash_table_info' is not a hash table!"),
    ])
    |> ignore
  }
  let mut res : Value = Nil
  maphash((key, val) => res = cons(mk_simp(q_marrow, [key, val]), res), ht)
  cons(list([q_mlist, q_simp]), res)
}

// ---------------------------------------------------------------------------
// This function is needed for draw_graph (get the temporary file to write in)

///|
fn d_temp_filename(file : Value) -> Value raise {
  if !stringp(file) {
    share_graphs__error([Str("Argument to `temp_filename' is not a string")])
    |> ignore
  }
  plot_temp_file(file)
}

///|
fn d_read_string(str : Value) -> Value raise {
  if !stringp(str) {
    share_graphs__error([Str("Argument to `read_string' is not a string")])
    |> ignore
  }
  let num = match str {
    Str(s) => lread(s)
    _ => Nil
  }
  if numberp(num) {
    num
  } else {
    str
  }
}

// ---------------------------------------------------------------------------
// top-level forms

///|
fn init_share_graph_core() -> Unit raise {
  d_put(q_d_graphs, Flo(2.0), q_d_version) |> ignore
  // The :print-function options of the graph and digraph defstructs.
  @lisp.struct_print_functions["graph"] = lfunc("graph-print-function", args => {
    format(args[1], "GRAPH(~a vertices, ~a edges)", [
      share_graphs__graph_order(args[0]),
      share_graphs__graph_size(args[0]),
    ])
  })
  @lisp.struct_print_functions["digraph"] = lfunc(
    "digraph-print-function",
    args => {
      format(args[1], "DIGRAPH(~a vertices, ~a arcs)", [
        share_graphs__digraph_order(args[0]),
        share_graphs__digraph_size(args[0]),
      ])
    },
  )
  // (defvar *dfs-bicomp-num* ()) ... (defvar *maximum-clique* ())
  defvar_init(q_ear_dfs_bicomp_num, Nil)
  defvar_init(q_ear_dfs_bicomp_low_pt, Nil)
  defvar_init(q_ear_dfs_bicomp_edges, Nil)
  defvar_init(q_ear_bicomponents, Nil)
  defvar_init(q_ear_hamilton_cycle, Nil)
  defvar_init(q_ear_maximum_clique, Nil)
}
