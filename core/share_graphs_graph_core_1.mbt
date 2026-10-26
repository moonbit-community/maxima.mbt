// Port of share/graphs/graph_core.lisp (part 1): the graph and digraph
// datastructures, vertex and edge operations, a set implementation using
// hash tables and the graph constructors.
//
// GRAPHS - graph theory package for Maxima
// Copyright (C) 2007-2011 Andrej Vodopivec <andrej.vodopivec@gmail.com>
// (GPL v2 or later)
//
// The CL defstructs `graph` and `digraph` are `make_struct` instances (they
// are Maxima-level values); their :print-function is installed by
// `init_share_graph_core`. The slot accessors `graph-order` ... are the
// private helpers `share_graphs__graph_order` ... below; like the CL
// accessors they signal a type error on an object of the wrong type.

///|
fn share_graphs__graph_p(x : Value) -> Bool {
  struct_typep(x, "graph")
}

///|
fn share_graphs__digraph_p(x : Value) -> Bool {
  struct_typep(x, "digraph")
}

///|
/// `(make-graph)`: slots size order vertices vertex-labels vertex-positions
/// edges edge-weights neighbors.
fn share_graphs__make_graph() -> Value {
  make_struct("graph", [
    Fix(0L),
    Fix(0L),
    Nil,
    make_hash_table(),
    Nil,
    Nil,
    make_hash_table(kind=Equal),
    make_hash_table(),
  ])
}

///|
/// `(make-digraph)`: slots size order vertices vertex-labels edges
/// vertex-positions edge-weights in-neighbors out-neighbors.
fn share_graphs__make_digraph() -> Value {
  make_struct("digraph", [
    Fix(0L),
    Fix(0L),
    Nil,
    make_hash_table(),
    Nil,
    Nil,
    make_hash_table(kind=Equal),
    make_hash_table(),
    make_hash_table(),
  ])
}

///|
/// `((mlist simp) ,@l)`
fn share_graphs__ml(l : Value) -> Value {
  cons(list([q_mlist, q_simp]), l)
}

///|
/// `($error ,@args)`
fn share_graphs__error(args : Array[Value]) -> Value raise {
  d_error(list(args))
}

///|
/// `(remove x l :count 1)`
fn share_graphs__remove1(x : Value, l : Value) -> Value {
  let r = []
  let mut p = l
  while p is Cons(c) {
    if eql(x, c.car) {
      return append(list(r), c.cdr)
    }
    r.push(c.car)
    p = c.cdr
  }
  list(r)
}

///|
/// `(remove x l :test #'equal :count 1)`
fn share_graphs__remove1_equal(x : Value, l : Value) -> Value {
  let r = []
  let mut p = l
  while p is Cons(c) {
    if equal(x, c.car) {
      return append(list(r), c.cdr)
    }
    r.push(c.car)
    p = c.cdr
  }
  list(r)
}

///|
/// `(apply #'max l)`
fn share_graphs__max_list(l : Value) -> Value raise {
  match l {
    Cons(c) => {
      let mut m = c.car
      for x in c.cdr.iter() {
        m = num_max(m, x)
      }
      if !numberp(m) {
        raise type_error(m, "real")
      }
      m
    }
    _ => raise LispError::SimpleError("invalid number of arguments: 0")
  }
}

///|
/// `(apply #'min l)`
fn share_graphs__min_list(l : Value) -> Value raise {
  match l {
    Cons(c) => {
      let mut m = c.car
      for x in c.cdr.iter() {
        m = num_min(m, x)
      }
      if !numberp(m) {
        raise type_error(m, "real")
      }
      m
    }
    _ => raise LispError::SimpleError("invalid number of arguments: 0")
  }
}

///|
/// `(setf (nth n l) v)`
fn share_graphs__setf_nth(n : Int, l : Value, v : Value) -> Value {
  rplaca(nthcdr(n, l), v) |> ignore
  v
}

///|
/// `(gethash k table default)`
fn share_graphs__gethash_d(k : Value, table : Value, default : Value) -> Value raise {
  let (v, found) = gethash2(k, table)
  if found {
    v
  } else {
    default
  }
}

///|
/// `(incf (gethash k table [default]) delta)`
fn share_graphs__incf_hash(
  k : Value,
  table : Value,
  delta : Value,
  default? : Value = Nil,
) -> Value raise {
  sethash(k, table, num_add(share_graphs__gethash_d(k, table, default), delta))
}

///|
/// `(remhash k table)`. The port's hash tables iterate in insertion order but
/// keep a removed key's old position when it is re-added; SBCL instead reuses
/// the freed slot for the next new entry. For the stack-like use in the
/// isomorphism search both agree with "insertion order of the live entries",
/// which this helper provides by dropping the key from the order log.
fn share_graphs__remhash(k : Value, table : Value) -> Unit raise {
  remhash(k, table) |> ignore
  match table {
    Hash(h) => {
      let neworder = []
      for x in h.order {
        let same = match h.kind {
          Eq => eq(x, k)
          Eql => eql(x, k)
          Equal => equal(x, k)
          Equalp => equalp(x, k)
        }
        if !same {
          neworder.push(x)
        }
      }
      h.order = neworder
    }
    _ => ()
  }
}

///|
/// `(string= a b)` on string designators.
fn share_graphs__string_eq(a : Value, b : Value) -> Bool raise {
  fn designator(x : Value) -> String raise {
    match x {
      Str(s) => s
      Sym(s) => s.name
      Char(c) => c.to_string()
      Nil => "nil"
      _ => raise type_error(x, "string-designator")
    }
  }

  designator(a) == designator(b)
}

///|
/// CL `pi`
let share_graphs__pi : Value = Flo(@math.PI)

///|
/// `(graph-size x)`
fn share_graphs__graph_size(x : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_ref(x, 0)
}

///|
fn share_graphs__set_graph_size(x : Value, v : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_set(x, 0, v)
}

///|
/// `(graph-order x)`
fn share_graphs__graph_order(x : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_ref(x, 1)
}

///|
fn share_graphs__set_graph_order(x : Value, v : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_set(x, 1, v)
}

///|
/// `(graph-vertices x)`
fn share_graphs__graph_vertices(x : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_ref(x, 2)
}

///|
fn share_graphs__set_graph_vertices(x : Value, v : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_set(x, 2, v)
}

///|
/// `(graph-vertex-labels x)`
fn share_graphs__graph_vertex_labels(x : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_ref(x, 3)
}

///|
fn share_graphs__set_graph_vertex_labels(x : Value, v : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_set(x, 3, v)
}

///|
/// `(graph-vertex-positions x)`
fn share_graphs__graph_vertex_positions(x : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_ref(x, 4)
}

///|
fn share_graphs__set_graph_vertex_positions(x : Value, v : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_set(x, 4, v)
}

///|
/// `(graph-edges x)`
fn share_graphs__graph_edges(x : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_ref(x, 5)
}

///|
fn share_graphs__set_graph_edges(x : Value, v : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_set(x, 5, v)
}

///|
/// `(graph-edge-weights x)`
fn share_graphs__graph_edge_weights(x : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_ref(x, 6)
}

///|
fn share_graphs__set_graph_edge_weights(x : Value, v : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_set(x, 6, v)
}

///|
/// `(graph-neighbors x)`
fn share_graphs__graph_neighbors(x : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_ref(x, 7)
}

///|
fn share_graphs__set_graph_neighbors(x : Value, v : Value) -> Value raise {
  if !share_graphs__graph_p(x) {
    raise type_error(x, "graph")
  }
  struct_set(x, 7, v)
}

///|
/// `(digraph-size x)`
fn share_graphs__digraph_size(x : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_ref(x, 0)
}

///|
fn share_graphs__set_digraph_size(x : Value, v : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_set(x, 0, v)
}

///|
/// `(digraph-order x)`
fn share_graphs__digraph_order(x : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_ref(x, 1)
}

///|
fn share_graphs__set_digraph_order(x : Value, v : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_set(x, 1, v)
}

///|
/// `(digraph-vertices x)`
fn share_graphs__digraph_vertices(x : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_ref(x, 2)
}

///|
fn share_graphs__set_digraph_vertices(x : Value, v : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_set(x, 2, v)
}

///|
/// `(digraph-vertex-labels x)`
fn share_graphs__digraph_vertex_labels(x : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_ref(x, 3)
}

///|
fn share_graphs__set_digraph_vertex_labels(x : Value, v : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_set(x, 3, v)
}

///|
/// `(digraph-edges x)`
fn share_graphs__digraph_edges(x : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_ref(x, 4)
}

///|
fn share_graphs__set_digraph_edges(x : Value, v : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_set(x, 4, v)
}

///|
/// `(digraph-vertex-positions x)`
fn share_graphs__digraph_vertex_positions(x : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_ref(x, 5)
}

///|
fn share_graphs__set_digraph_vertex_positions(x : Value, v : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_set(x, 5, v)
}

///|
/// `(digraph-edge-weights x)`
fn share_graphs__digraph_edge_weights(x : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_ref(x, 6)
}

///|
fn share_graphs__set_digraph_edge_weights(x : Value, v : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_set(x, 6, v)
}

///|
/// `(digraph-in-neighbors x)`
fn share_graphs__digraph_in_neighbors(x : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_ref(x, 7)
}

///|
fn share_graphs__set_digraph_in_neighbors(x : Value, v : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_set(x, 7, v)
}

///|
/// `(digraph-out-neighbors x)`
fn share_graphs__digraph_out_neighbors(x : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_ref(x, 8)
}

///|
fn share_graphs__set_digraph_out_neighbors(x : Value, v : Value) -> Value raise {
  if !share_graphs__digraph_p(x) {
    raise type_error(x, "digraph")
  }
  struct_set(x, 8, v)
}


///|
fn require_graph(m : Value, ar : Value, gr : Value) -> Value raise {
  if !share_graphs__graph_p(gr) {
    share_graphs__error([
      format(Nil, "Argument ~a to `~a' is not a graph:", [ar, m]),
      gr,
    ])
  } else {
    Nil
  }
}

///|
fn require_digraph(m : Value, ar : Value, gr : Value) -> Value raise {
  if !share_graphs__digraph_p(gr) {
    share_graphs__error([
      format(Nil, "Argument ~a to `~a' is not a directed graph:", [ar, m]),
      gr,
    ])
  } else {
    Nil
  }
}

///|
fn require_graph_or_digraph(m : Value, ar : Value, gr : Value) -> Value raise {
  if !(share_graphs__graph_p(gr) || share_graphs__digraph_p(gr)) {
    share_graphs__error([
      format(Nil, "Argument ~a to `~a' is not a graph:", [ar, m]),
      gr,
    ])
  } else {
    Nil
  }
}

///|
fn d_print_graph(gr : Value) -> Value raise {
  require_graph_or_digraph(q_print_graph, Fix(1L), gr) |> ignore
  if share_graphs__graph_p(gr) {
    format(t, "~%Graph on ~d vertices with ~d edges.", [
      share_graphs__graph_order(gr),
      share_graphs__graph_size(gr),
    ])
    |> ignore
    if num_gt(share_graphs__graph_order(gr), Fix(0L)) {
      format(t, "~%Adjacencies:", []) |> ignore
    }
    for v in share_graphs__graph_vertices(gr).iter() {
      format(t, "~% ~2d :", [v]) |> ignore
      for u in neighbors(v, gr).iter() {
        format(t, " ~2d", [u]) |> ignore
      }
    }
  } else {
    format(t, "~%Digraph on ~d vertices with ~d arcs.", [
      share_graphs__digraph_order(gr),
      share_graphs__digraph_size(gr),
    ])
    |> ignore
    if num_gt(share_graphs__digraph_order(gr), Fix(0L)) {
      format(t, "~%Adjacencies:", []) |> ignore
    }
    for v in share_graphs__digraph_vertices(gr).iter() {
      format(t, "~% ~2d :", [v]) |> ignore
      for u in out_h_neighbors(v, gr).iter() {
        format(t, " ~2d", [u]) |> ignore
      }
    }
  }
  format(t, "~%", []) |> ignore
  q_d_done
}

///|
fn d_is_graph(x : Value) -> Value raise {
  lbool(share_graphs__graph_p(x))
}

///|
fn d_is_digraph(x : Value) -> Value raise {
  lbool(share_graphs__digraph_p(x))
}

///|
fn d_is_graph_or_digraph(x : Value) -> Value raise {
  lbool(share_graphs__graph_p(x) || share_graphs__digraph_p(x))
}

///|
fn d_graph_order(gr : Value) -> Value raise {
  require_graph_or_digraph(q_graph_order, Fix(1L), gr) |> ignore
  if share_graphs__graph_p(gr) {
    share_graphs__graph_order(gr)
  } else {
    share_graphs__digraph_order(gr)
  }
}

///|
fn d_graph_size(gr : Value) -> Value raise {
  require_graph_or_digraph(q_graph_size, Fix(1L), gr) |> ignore
  if share_graphs__graph_p(gr) {
    share_graphs__graph_size(gr)
  } else {
    share_graphs__digraph_size(gr)
  }
}

///|
fn d_get_positions(gr : Value) -> Value raise {
  require_graph_or_digraph(q_get_positions, Fix(1L), gr) |> ignore
  if share_graphs__graph_p(gr) {
    share_graphs__graph_vertex_positions(gr)
  } else {
    share_graphs__digraph_vertex_positions(gr)
  }
}

///|
fn d_set_positions(pos : Value, gr : Value) -> Value raise {
  require_graph_or_digraph(q_set_positions, Fix(2L), gr) |> ignore
  if share_graphs__graph_p(gr) {
    share_graphs__set_graph_vertex_positions(gr, pos)
  } else {
    share_graphs__set_digraph_vertex_positions(gr, pos)
  }
}

///|
fn d_copy_graph(gr : Value) -> Value raise {
  require_graph_or_digraph(q_copy_graph, Fix(1L), gr) |> ignore
  if share_graphs__graph_p(gr) {
    let g = share_graphs__make_graph()
    for v in share_graphs__graph_vertices(gr).iter() {
      add_h_vertex(v, g) |> ignore
      let l = get_h_vertex_h_label(v, gr)
      if l.truthy() {
        set_h_vertex_h_label(v, l, g) |> ignore
      }
    }
    for e in share_graphs__graph_edges(gr).iter() {
      add_h_edge(e, g) |> ignore
      let w = get_h_edge_h_weight(e, gr)
      if w.truthy() {
        set_h_edge_h_weight(e, w, g) |> ignore
      }
    }
    d_set_positions(d_get_positions(gr), g) |> ignore
    g
  } else {
    let g = share_graphs__make_digraph()
    for v in share_graphs__digraph_vertices(gr).iter() {
      add_h_vertex(v, g) |> ignore
      let l = get_h_vertex_h_label(v, gr)
      if l.truthy() {
        set_h_vertex_h_label(v, l, g) |> ignore
      }
    }
    for e in share_graphs__digraph_edges(gr).iter() {
      add_h_edge(e, g) |> ignore
      let w = get_h_edge_h_weight(e, gr)
      if w.truthy() {
        set_h_edge_h_weight(e, w, g) |> ignore
      }
    }
    d_set_positions(d_get_positions(gr), g) |> ignore
    g
  }
}

///|
fn d_new_graph() -> Value raise {
  share_graphs__make_graph()
}

// ---------------------------------------------------------------------------
// vertex operations

///|
fn d_vertices(gr : Value) -> Value raise {
  require_graph_or_digraph(q_vertices, Fix(1L), gr) |> ignore
  let vrt = vertices(gr)
  share_graphs__ml(copy_list(vrt))
}

///|
fn vertices(gr : Value) -> Value raise {
  if share_graphs__graph_p(gr) {
    share_graphs__graph_vertices(gr)
  } else {
    share_graphs__digraph_vertices(gr)
  }
}

///|
fn require_vertex(m : Value, i : Value, v : Value) -> Value raise {
  if !integerp(v) {
    share_graphs__error([
      Str("Argument"),
      i,
      Str("to"),
      m,
      Str("is not a valid vertex."),
    ])
  } else {
    Nil
  }
}

///|
fn is_vertex_in_graph(i : Value, gr : Value) -> Value raise {
  let tbl = if share_graphs__graph_p(gr) {
    share_graphs__graph_neighbors(gr)
  } else {
    share_graphs__digraph_out_neighbors(gr)
  }
  let v = share_graphs__gethash_d(i, tbl, q_not_in_graph)
  lbool(!equal(v, q_not_in_graph))
}

///|
fn require_vertex_in_graph(m : Value, i : Value, gr : Value) -> Value raise {
  if !is_vertex_in_graph(i, gr).truthy() {
    share_graphs__error([m, Str(": vertex not in graph.")])
  } else {
    Nil
  }
}

///|
fn d_is_vertex_in_graph(i : Value, gr : Value) -> Value raise {
  require_vertex(q_vertex_in_graph, Fix(1L), i) |> ignore
  require_graph_or_digraph(q_vertex_in_graph, Fix(2L), gr) |> ignore
  is_vertex_in_graph(i, gr)
}

///|
fn d_add_vertex(i : Value, gr? : Value = Nil) -> Value raise {
  let mut i = i
  let mut gr = gr
  if gr is Nil {
    gr = i
    i = num_add(Fix(1L), share_graphs__max_list(vertices(gr)))
  }
  require_vertex(q_add_vertex, Fix(1L), i) |> ignore
  require_graph_or_digraph(q_add_vertex, Fix(2L), gr) |> ignore
  if is_vertex_in_graph(i, gr).truthy() {
    share_graphs__error([Str("add_vertex: vertex is already in the graph!")])
    |> ignore
  }
  add_h_vertex(i, gr) |> ignore
  i
}

///|
fn d_add_vertices(vl : Value, gr : Value) -> Value raise {
  let mut vl = vl
  require_graph_or_digraph(q_add_vertices, Fix(2L), gr) |> ignore
  if !(integerp(vl) || d_listp(vl).truthy()) {
    share_graphs__error([Str("Argument 1 to add_vertices is not a list.")])
    |> ignore
  }
  if d_listp(vl).truthy() {
    for v in cdr(vl).iter() {
      d_add_vertex(v, gr~) |> ignore
    }
  } else {
    let n = vl
    vl = Nil
    for _ in 0..<to_int(n) {
      vl = cons(d_add_vertex(gr), vl)
    }
    vl = cons(list([q_mlist, q_simp]), reverse(vl))
  }
  vl
}

///|
fn add_h_vertex(i : Value, gr : Value) -> Value raise {
  if share_graphs__graph_p(gr) {
    share_graphs__set_graph_order(
      gr,
      num_add(share_graphs__graph_order(gr), Fix(1L)),
    )
    |> ignore
    share_graphs__set_graph_vertices(
      gr,
      cons(i, share_graphs__graph_vertices(gr)),
    )
    |> ignore
    share_graphs__set_graph_vertex_positions(gr, Nil) |> ignore
    sethash(i, share_graphs__graph_neighbors(gr), Nil)
  } else {
    share_graphs__set_digraph_order(
      gr,
      num_add(share_graphs__digraph_order(gr), Fix(1L)),
    )
    |> ignore
    share_graphs__set_digraph_vertices(
      gr,
      cons(i, share_graphs__digraph_vertices(gr)),
    )
    |> ignore
    share_graphs__set_digraph_vertex_positions(gr, Nil) |> ignore
    sethash(i, share_graphs__digraph_in_neighbors(gr), Nil) |> ignore
    sethash(i, share_graphs__digraph_out_neighbors(gr), Nil)
  }
}

///|
fn neighbors(i : Value, gr : Value) -> Value raise {
  gethash(
    i,
    if share_graphs__graph_p(gr) {
      share_graphs__graph_neighbors(gr)
    } else {
      share_graphs__digraph_out_neighbors(gr)
    },
  )
}

///|
fn in_h_neighbors(i : Value, gr : Value) -> Value raise {
  gethash(i, share_graphs__digraph_in_neighbors(gr))
}

///|
fn out_h_neighbors(i : Value, gr : Value) -> Value raise {
  gethash(i, share_graphs__digraph_out_neighbors(gr))
}

///|
fn d_neighbors(i : Value, gr : Value) -> Value raise {
  require_vertex(q_neighbors, Fix(1L), i) |> ignore
  require_graph(q_neighbors, Fix(2L), gr) |> ignore
  require_vertex_in_graph(q_neighbors, i, gr) |> ignore
  share_graphs__ml(copy_list(neighbors(i, gr)))
}

///|
fn d_out_neighbors(i : Value, gr : Value) -> Value raise {
  require_vertex(q_out_neighbors, Fix(1L), i) |> ignore
  require_digraph(q_out_neighbors, Fix(2L), gr) |> ignore
  require_vertex_in_graph(q_out_neighbors, i, gr) |> ignore
  share_graphs__ml(copy_list(out_h_neighbors(i, gr)))
}

///|
fn d_in_neighbors(i : Value, gr : Value) -> Value raise {
  require_vertex(q_in_neighbors, Fix(1L), i) |> ignore
  require_digraph(q_in_neighbors, Fix(2L), gr) |> ignore
  require_vertex_in_graph(q_in_neighbors, i, gr) |> ignore
  share_graphs__ml(copy_list(in_h_neighbors(i, gr)))
}

///|
fn d_degree_sequence(gr : Value) -> Value raise {
  require_graph(q_degree_sequence, Fix(1L), gr) |> ignore
  let mut s : Value = Nil
  for v in share_graphs__graph_vertices(gr).iter() {
    s = cons(int(length(neighbors(v, gr))), s)
  }
  s = sort_list(s, (a, b) => num_lt(a, b))
  share_graphs__ml(s)
}

///|
fn d_remove_vertex(v : Value, gr : Value) -> Value raise {
  require_vertex(q_remove_vertex, Fix(1L), v) |> ignore
  require_graph_or_digraph(q_remove_vertex, Fix(2L), gr) |> ignore
  require_vertex_in_graph(q_remove_vertex, v, gr) |> ignore
  clear_h_vertex_h_label(v, gr) |> ignore
  remove_h_vertex(v, gr)
}

///|
fn d_remove_vertices(vl : Value, gr : Value) -> Value raise {
  require_graph_or_digraph(q_remove_vertices, Fix(2L), gr) |> ignore
  if !d_listp(vl).truthy() {
    share_graphs__error([Str("Argument 1 to remove_vertices is not a list.")])
    |> ignore
  }
  for v in cdr(vl).iter() {
    d_remove_vertex(v, gr) |> ignore
  }
  q_d_done
}

///|
fn remove_h_vertex(v : Value, gr : Value) -> Value raise {
  if share_graphs__graph_p(gr) {
    for u in neighbors(v, gr).iter() {
      let e = list([num_min(u, v), num_max(u, v)])
      remove_h_edge(e, gr) |> ignore
    }
    clear_h_vertex_h_label(v, gr) |> ignore
    if share_graphs__graph_vertex_positions(gr).truthy() {
      share_graphs__set_graph_vertex_positions(
        gr,
        cons(
          list([q_mlist, q_simp]),
          remove_if(
            x => num_eq(cadr(x), v),
            cdr(share_graphs__graph_vertex_positions(gr)),
          ),
        ),
      )
      |> ignore
    }
    share_graphs__set_graph_vertices(
      gr,
      share_graphs__remove1(v, share_graphs__graph_vertices(gr)),
    )
    |> ignore
    remhash(v, share_graphs__graph_neighbors(gr)) |> ignore
    share_graphs__set_graph_order(
      gr,
      num_sub(share_graphs__graph_order(gr), Fix(1L)),
    )
    |> ignore
  } else {
    for u in out_h_neighbors(v, gr).iter() {
      remove_h_edge(list([v, u]), gr) |> ignore
    }
    for u in in_h_neighbors(v, gr).iter() {
      remove_h_edge(list([u, v]), gr) |> ignore
    }
    clear_h_vertex_h_label(v, gr) |> ignore
    if share_graphs__digraph_vertex_positions(gr).truthy() {
      share_graphs__set_digraph_vertex_positions(
        gr,
        cons(
          list([q_mlist, q_simp]),
          remove_if(
            x => num_eq(cadr(x), v),
            cdr(share_graphs__digraph_vertex_positions(gr)),
          ),
        ),
      )
      |> ignore
    }
    share_graphs__set_digraph_vertices(
      gr,
      share_graphs__remove1(v, share_graphs__digraph_vertices(gr)),
    )
    |> ignore
    remhash(v, share_graphs__digraph_in_neighbors(gr)) |> ignore
    remhash(v, share_graphs__digraph_out_neighbors(gr)) |> ignore
    share_graphs__set_digraph_order(
      gr,
      num_sub(share_graphs__digraph_order(gr), Fix(1L)),
    )
    |> ignore
  }
  q_d_done
}

///|
fn d_first_vertex(gr : Value) -> Value raise {
  require_graph_or_digraph(q_first_vertex, Fix(1L), gr) |> ignore
  let n = if share_graphs__graph_p(gr) {
    share_graphs__graph_order(gr)
  } else {
    share_graphs__digraph_order(gr)
  }
  if num_eq(Fix(0L), n) {
    share_graphs__error([Str("first_vertex: no first vertex in an empty graph.")])
  } else {
    car(vertices(gr))
  }
}

///|
fn d_max_degree(gr : Value) -> Value raise {
  require_graph(q_max_degree, Fix(1L), gr) |> ignore
  if num_eq(Fix(0L), share_graphs__graph_order(gr)) {
    share_graphs__error([Str("max_degree: no max degree in an empty graph.")])
  } else {
    let mut v = car(share_graphs__graph_vertices(gr))
    let mut d = length(neighbors(v, gr))
    for u in share_graphs__graph_vertices(gr).iter() {
      if length(neighbors(u, gr)) > d {
        d = length(neighbors(u, gr))
        v = u
      }
    }
    share_graphs__ml(list([int(d), v]))
  }
}

///|
fn d_min_degree(gr : Value) -> Value raise {
  require_graph(q_min_degree, Fix(1L), gr) |> ignore
  if num_eq(Fix(0L), share_graphs__graph_order(gr)) {
    share_graphs__error([Str("min_degree: no min degree in an empty graph.")])
  } else {
    let mut v = car(share_graphs__graph_vertices(gr))
    let mut d = length(neighbors(v, gr))
    for u in share_graphs__graph_vertices(gr).iter() {
      if length(neighbors(u, gr)) < d {
        d = length(neighbors(u, gr))
        v = u
      }
    }
    share_graphs__ml(list([int(d), v]))
  }
}

///|
fn d_average_degree(gr : Value) -> Value raise {
  require_graph(q_average_degee, Fix(1L), gr) |> ignore
  mul_star(
    list([
      Fix(2L),
      div_star(share_graphs__graph_size(gr), share_graphs__graph_order(gr)),
    ]),
  )
}

///|
fn d_vertex_degree(v : Value, gr : Value) -> Value raise {
  require_vertex(q_vertex_degree, Fix(1L), v) |> ignore
  require_graph(q_vertex_degree, Fix(2L), gr) |> ignore
  require_vertex_in_graph(q_vertex_degree, v, gr) |> ignore
  int(length(neighbors(v, gr)))
}

///|
fn d_vertex_in_degree(v : Value, gr : Value) -> Value raise {
  require_vertex(q_vertex_in_degree, Fix(1L), v) |> ignore
  require_digraph(q_vertex_in_degree, Fix(2L), gr) |> ignore
  require_vertex_in_graph(q_vertex_in_degree, v, gr) |> ignore
  int(length(in_h_neighbors(v, gr)))
}

///|
fn d_vertex_out_degree(v : Value, gr : Value) -> Value raise {
  require_vertex(q_vertex_out_degree, Fix(1L), v) |> ignore
  require_digraph(q_vertex_out_degree, Fix(2L), gr) |> ignore
  require_vertex_in_graph(q_vertex_out_degree, v, gr) |> ignore
  int(length(out_h_neighbors(v, gr)))
}

///|
fn d_get_vertex_label(v : Value, gr : Value, default? : Value = Nil) -> Value raise {
  require_vertex(q_get_vertex_label, Fix(1L), v) |> ignore
  require_graph_or_digraph(q_get_vertex_label, Fix(2L), gr) |> ignore
  require_vertex_in_graph(q_vertex_label, v, gr) |> ignore
  let l = get_h_vertex_h_label(v, gr)
  if l.truthy() {
    l
  } else {
    default
  }
}

///|
fn get_h_vertex_h_label(v : Value, gr : Value) -> Value raise {
  gethash(
    v,
    if share_graphs__graph_p(gr) {
      share_graphs__graph_vertex_labels(gr)
    } else {
      share_graphs__digraph_vertex_labels(gr)
    },
  )
}

///|
fn d_get_unique_vertex_by_label(l : Value, gr : Value) -> Value raise {
  if !stringp(l) {
    merr(
      "get_unique_vertex_by_label: first argument must be a string; found ~M",
      [l],
    )
    |> ignore
  }
  require_graph_or_digraph(q_get_unique_vertex_by_label, Fix(2L), gr) |> ignore
  get_h_unique_h_vertex_h_by_h_label(l, gr)
}

///|
fn get_h_unique_h_vertex_h_by_h_label(l : Value, gr : Value) -> Value raise {
  let vv = get_h_all_h_vertices_h_by_h_label(l, gr)
  if vv is Nil {
    Nil
  } else if length(vv) == 1 {
    car(vv)
  } else {
    merr(
      "get_unique_vertex_by_label: two or more vertices have the same label ~:M",
      [l],
    )
  }
}

///|
fn get_h_all_h_vertices_h_by_h_label(l : Value, gr : Value) -> Value raise {
  let mut vv : Value = Nil
  maphash(
    (v, l1) => if share_graphs__string_eq(l1, l) { vv = cons(v, vv) },
    if share_graphs__graph_p(gr) {
      share_graphs__graph_vertex_labels(gr)
    } else {
      share_graphs__digraph_vertex_labels(gr)
    },
  )
  sort_list(vv, (a, b) => num_lt(a, b))
}

///|
fn d_get_all_vertices_by_label(l : Value, gr : Value) -> Value raise {
  if !stringp(l) {
    merr(
      "get_all_vertices_by_label: first argument must be a string; found ~M",
      [l],
    )
    |> ignore
  }
  require_graph_or_digraph(q_get_all_vertices_by_label, Fix(2L), gr) |> ignore
  cons(list1(q_mlist), get_h_all_h_vertices_h_by_h_label(l, gr))
}

///|
fn d_clear_vertex_label(v : Value, gr : Value) -> Value raise {
  require_vertex(q_clear_vertex_label, Fix(1L), v) |> ignore
  require_graph_or_digraph(q_clear_vertex_label, Fix(2L), gr) |> ignore
  require_vertex_in_graph(q_clear_label, v, gr) |> ignore
  clear_h_vertex_h_label(v, gr)
}

///|
fn clear_h_vertex_h_label(v : Value, gr : Value) -> Value raise {
  remhash(
    v,
    if share_graphs__graph_p(gr) {
      share_graphs__graph_vertex_labels(gr)
    } else {
      share_graphs__digraph_vertex_labels(gr)
    },
  )
  |> ignore
  q_d_done
}

///|
fn d_set_vertex_label(v : Value, l : Value, gr : Value) -> Value raise {
  require_vertex(q_set_vertex_label, Fix(1L), v) |> ignore
  require_graph_or_digraph(q_set_vertex_label, Fix(3L), gr) |> ignore
  require_vertex_in_graph(q_set_label, v, gr) |> ignore
  set_h_vertex_h_label(v, l, gr)
}

///|
fn set_h_vertex_h_label(v : Value, l : Value, gr : Value) -> Value raise {
  sethash(
    v,
    if share_graphs__graph_p(gr) {
      share_graphs__graph_vertex_labels(gr)
    } else {
      share_graphs__digraph_vertex_labels(gr)
    },
    l,
  )
  |> ignore
  q_d_done
}

// ---------------------------------------------------------------------------
// edge operations

///|
fn require_medge(m : Value, ar : Value, e : Value) -> Value raise {
  if !(d_listp(e).truthy() && eql(Fix(2L), d_length(e))) {
    share_graphs__error([
      Str("Argument"),
      ar,
      Str("to"),
      m,
      Str("is not an edge (0)."),
    ])
  } else {
    let u = d_first(e)
    let v = funcall(q_d_second, [e])
    if !(integerp(u) && integerp(v)) {
      share_graphs__error([
        Str("Argument"),
        ar,
        Str("to"),
        m,
        Str("is not an edge (1)."),
      ])
      |> ignore
    }
    if eq(u, v) {
      share_graphs__error([
        Str("Argument"),
        ar,
        Str("to"),
        m,
        Str("is not an edge (2)."),
      ])
    } else {
      Nil
    }
  }
}

///|
fn require_edge_in_graph(m : Value, e : Value, gr : Value) -> Value raise {
  if !is_h_edge_h_in_h_graph(e, gr).truthy() {
    share_graphs__error([m, Str(": edge not in graph.")])
  } else {
    Nil
  }
}

///|
fn m_edge_to_l_edge(e : Value) -> Value raise {
  let uv = cdr(e)
  list([share_graphs__min_list(uv), share_graphs__max_list(uv)])
}

///|
fn m_edge_to_l_dedge(e : Value) -> Value raise {
  let uv = cdr(e)
  list([car(uv), cadr(uv)])
}

///|
fn l_edge_to_m_edge(e : Value) -> Value raise {
  share_graphs__ml(e)
}

///|
fn d_is_edge_in_graph(e : Value, gr : Value) -> Value raise {
  require_medge(q_is_edge_in_graph, Fix(1L), e) |> ignore
  require_graph_or_digraph(q_is_edge_in_graph, Fix(2L), gr) |> ignore
  if share_graphs__graph_p(gr) {
    is_h_edge_h_in_h_graph(m_edge_to_l_edge(e), gr)
  } else {
    is_h_edge_h_in_h_graph(m_edge_to_l_dedge(e), gr)
  }
}

///|
fn is_h_edge_h_in_h_graph(e : Value, gr : Value) -> Value raise {
  if share_graphs__graph_p(gr) {
    lbool(member(cadr(e), neighbors(car(e), gr)).truthy())
  } else {
    lbool(member(cadr(e), out_h_neighbors(car(e), gr)).truthy())
  }
}

///|
fn d_add_edge(e : Value, gr : Value) -> Value raise {
  require_medge(q_add_edge, Fix(1L), e) |> ignore
  require_graph_or_digraph(q_add_edge, Fix(2L), gr) |> ignore
  let e1 = if share_graphs__graph_p(gr) {
    m_edge_to_l_edge(e)
  } else {
    m_edge_to_l_dedge(e)
  }
  let u = car(e1)
  let v = cadr(e1)
  if !(is_vertex_in_graph(u, gr).truthy() && is_vertex_in_graph(v, gr).truthy()) {
    share_graphs__error([Str("add_edge: end vertices are not in graph!")])
    |> ignore
  } else if eq(u, v) {
    share_graphs__error([Str("add_edge: end vertices are equal!")]) |> ignore
  } else if is_h_edge_h_in_h_graph(e1, gr).truthy() {
    share_graphs__error([Str("add_edge: edge already in graph!")]) |> ignore
  }
  add_h_edge(e1, gr)
}

///|
fn d_add_edges(el : Value, gr : Value) -> Value raise {
  require_graph_or_digraph(q_add_edges, Fix(2L), gr) |> ignore
  if !d_listp(el).truthy() {
    share_graphs__error([Str("Argument 1 to add_edges is not a list!")])
    |> ignore
  } else {
    for e in cdr(el).iter() {
      require_medge(q_add_edges, Fix(1L), e) |> ignore
      d_add_edge(e, gr) |> ignore
    }
  }
  q_d_done
}

///|
fn add_h_edge(e : Value, gr : Value) -> Value raise {
  let u = car(e)
  let v = cadr(e)
  if share_graphs__graph_p(gr) {
    let nb = share_graphs__graph_neighbors(gr)
    sethash(u, nb, cons(v, gethash(u, nb))) |> ignore
    sethash(v, nb, cons(u, gethash(v, nb))) |> ignore
    share_graphs__set_graph_edges(gr, cons(e, share_graphs__graph_edges(gr)))
    |> ignore
    share_graphs__set_graph_size(
      gr,
      num_add(share_graphs__graph_size(gr), Fix(1L)),
    )
    |> ignore
  } else {
    let onb = share_graphs__digraph_out_neighbors(gr)
    let inb = share_graphs__digraph_in_neighbors(gr)
    sethash(u, onb, cons(v, gethash(u, onb))) |> ignore
    sethash(v, inb, cons(u, gethash(v, inb))) |> ignore
    share_graphs__set_digraph_edges(gr, cons(e, share_graphs__digraph_edges(gr)))
    |> ignore
    share_graphs__set_digraph_size(
      gr,
      num_add(share_graphs__digraph_size(gr), Fix(1L)),
    )
    |> ignore
  }
  q_d_done
}

///|
fn add_h_edges(elist : Value, gr : Value) -> Value raise {
  for e in elist.iter() {
    add_h_edge(e, gr) |> ignore
  }
  Nil
}

///|
fn d_edges(gr : Value) -> Value raise {
  require_graph_or_digraph(q_edges, Fix(1L), gr) |> ignore
  let e = mapcar(u => share_graphs__ml(copy_list(u)), edges(gr))
  share_graphs__ml(e)
}

///|
fn edges(gr : Value) -> Value raise {
  if share_graphs__graph_p(gr) {
    share_graphs__graph_edges(gr)
  } else {
    share_graphs__digraph_edges(gr)
  }
}

///|
fn d_remove_edge(e : Value, gr : Value) -> Value raise {
  require_medge(q_remove_edge, Fix(1L), e) |> ignore
  require_graph_or_digraph(q_remove_edge, Fix(2L), gr) |> ignore
  if !d_is_edge_in_graph(e, gr).truthy() {
    share_graphs__error([Str("remove_edge: edge"), e, Str("is not in graph.")])
    |> ignore
  }
  remove_h_edge(
    if share_graphs__graph_p(gr) {
      m_edge_to_l_edge(e)
    } else {
      m_edge_to_l_dedge(e)
    },
    gr,
  )
}

///|
fn d_remove_edges(el : Value, gr : Value) -> Value raise {
  require_graph_or_digraph(q_remove_edges, Fix(2L), gr) |> ignore
  if !d_listp(el).truthy() {
    share_graphs__error([Str("Argument 1 to remove_edges is not a list.")])
    |> ignore
  }
  for e in cdr(el).iter() {
    d_remove_edge(e, gr) |> ignore
  }
  q_d_done
}

///|
fn remove_h_edge(e : Value, gr : Value) -> Value raise {
  let u = car(e)
  let v = cadr(e)
  if share_graphs__graph_p(gr) {
    let nb = share_graphs__graph_neighbors(gr)
    sethash(u, nb, share_graphs__remove1(v, gethash(u, nb))) |> ignore
    sethash(v, nb, share_graphs__remove1(u, gethash(v, nb))) |> ignore
    clear_h_edge_h_weight(e, gr) |> ignore
    share_graphs__set_graph_size(
      gr,
      num_sub(share_graphs__graph_size(gr), Fix(1L)),
    )
    |> ignore
    share_graphs__set_graph_edges(
      gr,
      share_graphs__remove1_equal(list([u, v]), share_graphs__graph_edges(gr)),
    )
    |> ignore
  } else {
    let onb = share_graphs__digraph_out_neighbors(gr)
    let inb = share_graphs__digraph_in_neighbors(gr)
    sethash(u, onb, share_graphs__remove1(v, gethash(u, onb))) |> ignore
    sethash(v, inb, share_graphs__remove1(u, gethash(v, inb))) |> ignore
    clear_h_edge_h_weight(e, gr) |> ignore
    share_graphs__set_digraph_size(
      gr,
      num_sub(share_graphs__digraph_size(gr), Fix(1L)),
    )
    |> ignore
    share_graphs__set_digraph_edges(
      gr,
      share_graphs__remove1_equal(list([u, v]), share_graphs__digraph_edges(gr)),
    )
    |> ignore
  }
  q_d_done
}

///|
fn d_contract_edge(e : Value, gr : Value) -> Value raise {
  require_medge(q_contract_edge, Fix(1L), e) |> ignore
  require_graph(q_contract_edge, Fix(2L), gr) |> ignore
  let e1 = m_edge_to_l_edge(e)
  let u = car(e1)
  let v = cadr(e1)
  for x in neighbors(v, gr).iter() {
    if !num_eq(x, u) {
      let e2 = list([num_min(x, u), num_max(x, u)])
      if !is_h_edge_h_in_h_graph(e2, gr).truthy() {
        add_h_edge(e2, gr) |> ignore
      }
    }
  }
  remove_h_vertex(v, gr) |> ignore
  q_d_done
}

///|
fn d_contract_edges(el : Value, gr : Value) -> Value raise {
  require_graph_or_digraph(q_contract_edges, Fix(2L), gr) |> ignore
  if !d_listp(el).truthy() {
    share_graphs__error([Str("Argument 1 to contract_edges is not a list.")])
    |> ignore
  }
  for e in cdr(el).iter() {
    d_contract_edge(e, gr) |> ignore
  }
  q_d_done
}

///|
fn d_get_edge_weight(
  e : Value,
  gr : Value,
  default? : Value = Nil,
  not_present? : Value = Nil,
) -> Value raise {
  require_medge(q_get_edge_weight, Fix(1L), e) |> ignore
  require_graph_or_digraph(q_get_edge_weight, Fix(2L), gr) |> ignore
  if !d_is_edge_in_graph(e, gr).truthy() {
    if not_present is Nil {
      share_graphs__error([Str("get_edge_weight: edge not in graph")]) |> ignore
    } else {
      return not_present
    }
  }
  let w = if share_graphs__graph_p(gr) {
    get_h_edge_h_weight(m_edge_to_l_edge(e), gr)
  } else {
    get_h_edge_h_weight(m_edge_to_l_dedge(e), gr)
  }
  if w.truthy() {
    w
  } else if default.truthy() {
    default
  } else {
    Fix(1L)
  }
}

///|
fn get_h_edge_h_weight(e : Value, gr : Value) -> Value raise {
  let edge_weights = if share_graphs__graph_p(gr) {
    share_graphs__graph_edge_weights(gr)
  } else {
    share_graphs__digraph_edge_weights(gr)
  }
  gethash(e, edge_weights)
}

///|
fn d_clear_edge_weight(e : Value, gr : Value) -> Value raise {
  require_medge(q_clear_edge_weight, Fix(1L), e) |> ignore
  require_graph_or_digraph(q_clear_edge_weight, Fix(2L), gr) |> ignore
  if !d_is_edge_in_graph(e, gr).truthy() {
    share_graphs__error([Str("clear_edge_weight: edge not in graph")]) |> ignore
  }
  if share_graphs__graph_p(gr) {
    clear_h_edge_h_weight(m_edge_to_l_edge(e), gr)
  } else {
    clear_h_edge_h_weight(m_edge_to_l_dedge(e), gr)
  }
}

///|
fn clear_h_edge_h_weight(e : Value, gr : Value) -> Value raise {
  let edge_weights = if share_graphs__graph_p(gr) {
    share_graphs__graph_edge_weights(gr)
  } else {
    share_graphs__digraph_edge_weights(gr)
  }
  remhash(e, edge_weights) |> ignore
  q_d_done
}

///|
fn d_set_edge_weight(e : Value, w : Value, gr : Value) -> Value raise {
  require_medge(q_set_edge_weight, Fix(1L), e) |> ignore
  require_graph_or_digraph(q_set_edge_weight, Fix(3L), gr) |> ignore
  if !d_is_edge_in_graph(e, gr).truthy() {
    share_graphs__error([Str("set_edge_weight: edge not in graph")]) |> ignore
  }
  if share_graphs__graph_p(gr) {
    set_h_edge_h_weight(m_edge_to_l_edge(e), w, gr)
  } else {
    set_h_edge_h_weight(m_edge_to_l_dedge(e), w, gr)
  }
}

///|
fn set_h_edge_h_weight(e : Value, w : Value, gr : Value) -> Value raise {
  let edge_weights = if share_graphs__graph_p(gr) {
    share_graphs__graph_edge_weights(gr)
  } else {
    share_graphs__digraph_edge_weights(gr)
  }
  sethash(e, edge_weights, w) |> ignore
  q_d_done
}

///|
fn d_connect_vertices(sources : Value, sinks : Value, gr : Value) -> Value raise {
  require_graph(q_connect_vertices, Fix(3L), gr) |> ignore
  let sources = if d_listp(sources).truthy() {
    cdr(sources)
  } else {
    list1(sources)
  }
  let sinks = if d_listp(sinks).truthy() { cdr(sinks) } else { list1(sinks) }
  for u in sources.iter() {
    for v in sinks.iter() {
      d_add_edge(share_graphs__ml(list([u, v])), gr) |> ignore
    }
  }
  q_d_done
}

///|
fn d_subdivide_edge(e : Value, gr : Value) -> Value raise {
  require_graph(q_subdivide_edge, Fix(2L), gr) |> ignore
  require_edge_in_graph(q_subdivide_edge, m_edge_to_l_edge(e), gr) |> ignore
  let new_vertex = num_add(Fix(1L), share_graphs__max_list(vertices(gr)))
  let x = d_first(e)
  let y = funcall(q_d_second, [e])
  d_remove_edge(share_graphs__ml(list([x, y])), gr) |> ignore
  d_add_vertex(new_vertex, gr~) |> ignore
  d_add_edge(share_graphs__ml(list([x, new_vertex])), gr) |> ignore
  d_add_edge(share_graphs__ml(list([y, new_vertex])), gr) |> ignore
  q_d_done
}

// ---------------------------------------------------------------------------
// implementation of a set using hash tables (defstruct ht-set (content))

///|
fn share_graphs__ht_set_content(set_ : Value) -> Value raise {
  if !struct_typep(set_, "ht-set") {
    raise type_error(set_, "ht-set")
  }
  struct_ref(set_, 0)
}

///|
fn new_set(initial_content : Value) -> Value raise {
  let set_ = make_struct("ht-set", [make_hash_table()])
  for obj in initial_content.iter() {
    set_add(obj, set_) |> ignore
  }
  set_
}

///|
fn set_member(obj : Value, set_ : Value) -> Value raise {
  gethash(obj, share_graphs__ht_set_content(set_))
}

///|
fn set_add(obj : Value, set_ : Value) -> Value raise {
  sethash(obj, share_graphs__ht_set_content(set_), t)
}

///|
fn set_remove(obj : Value, set_ : Value) -> Value raise {
  lbool(remhash(obj, share_graphs__ht_set_content(set_)))
}

///|
fn set_emptyp(set_ : Value) -> Value raise {
  lbool(hash_table_count(share_graphs__ht_set_content(set_)) == 0)
}

///|
fn set_elements(set_ : Value) -> Value raise {
  let mut elts : Value = Nil
  maphash((key, _) => elts = cons(key, elts), share_graphs__ht_set_content(set_))
  elts
}

// ---------------------------------------------------------------------------
// graph definitions

///|
fn d_empty_graph(n : Value) -> Value raise {
  let gr = share_graphs__make_graph()
  for i in 0..<to_int(n) {
    add_h_vertex(int(i), gr) |> ignore
  }
  gr
}

///|
fn d_empty_digraph(n : Value) -> Value raise {
  let gr = share_graphs__make_digraph()
  for i in 0..<to_int(n) {
    add_h_vertex(int(i), gr) |> ignore
  }
  gr
}

///|
fn d_create_graph(v_list : Value, e_list : Value, dir? : Value = Nil) -> Value raise {
  let mut directed = false
  // check if the graph is a directed graph
  if atom(dir) {
    if dir.truthy() {
      directed = true
    }
  } else if eq(caar(dir), q_mequal) &&
    eq(cadr(dir), q_d_directed) &&
    eq(caddr(dir), t) {
    directed = true
  }
  if !(integerp(v_list) || d_listp(v_list).truthy()) {
    share_graphs__error([Str("Argument 1 to create_graph is not a list.")])
    |> ignore
  }
  if !d_listp(e_list).truthy() {
    share_graphs__error([Str("Argument 2 to create_graph is not a list.")])
    |> ignore
  }
  let gr = if directed {
    share_graphs__make_digraph()
  } else {
    share_graphs__make_graph()
  }
  if integerp(v_list) {
    for v in 0..<to_int(v_list) {
      d_add_vertex(int(v), gr~) |> ignore
    }
  } else {
    for v in reverse(cdr(v_list)).iter() {
      if d_listp(v).truthy() {
        d_add_vertex(d_first(v), gr~) |> ignore
        d_set_vertex_label(d_first(v), funcall(q_d_second, [v]), gr) |> ignore
      } else {
        d_add_vertex(v, gr~) |> ignore
      }
    }
  }
  for e in cdr(e_list).iter() {
    if d_listp(d_first(e)).truthy() {
      d_add_edge(d_first(e), gr) |> ignore
      d_set_edge_weight(d_first(e), funcall(q_d_second, [e]), gr) |> ignore
    } else {
      d_add_edge(e, gr) |> ignore
    }
  }
  gr
}

///|
fn d_cycle_graph(n : Value) -> Value raise {
  let g = d_empty_graph(n)
  let mut pos : Value = Nil
  let nn = to_int(n)
  for i in 0..<(nn - 1) {
    add_h_edge(list([int(i), int(i + 1)]), g) |> ignore
  }
  add_h_edge(list([Fix(0L), num_sub(n, Fix(1L))]), g) |> ignore
  for i in 0..<nn {
    // (* i 2 pi (/ n))
    let x = num_mul(
      num_mul(num_mul(int(i), Fix(2L)), share_graphs__pi),
      num_div(Fix(1L), n),
    )
    pos = cons(
      share_graphs__ml(
        list([int(i), share_graphs__ml(list([ftake(q_p_cos, [x]), ftake(q_p_sin, [x])]))]),
      ),
      pos,
    )
  }
  d_set_positions(cons(list([q_mlist, q_simp]), pos), g) |> ignore
  g
}

///|
fn d_cycle_digraph(n : Value) -> Value raise {
  let g = d_empty_digraph(n)
  for i in 0..<(to_int(n) - 1) {
    add_h_edge(list([int(i), int(i + 1)]), g) |> ignore
  }
  add_h_edge(list([num_sub(n, Fix(1L)), Fix(0L)]), g) |> ignore
  g
}

///|
fn d_path_graph(n : Value) -> Value raise {
  let g = d_empty_graph(n)
  let mut pos : Value = Nil
  let nn = to_int(n)
  for i in 0..<(nn - 1) {
    add_h_edge(list([int(i), int(i + 1)]), g) |> ignore
  }
  for i in 0..<nn {
    pos = cons(
      share_graphs__ml(list([int(i), share_graphs__ml(list([int(i), Fix(0L)]))])),
      pos,
    )
  }
  d_set_positions(cons(list([q_mlist, q_simp]), pos), g) |> ignore
  g
}

///|
fn d_path_digraph(n : Value) -> Value raise {
  let g = d_empty_digraph(n)
  for i in 0..<(to_int(n) - 1) {
    add_h_edge(list([int(i), int(i + 1)]), g) |> ignore
  }
  g
}

///|
fn d_petersen_graph(n? : Value = Nil, d? : Value = Nil) -> Value raise {
  let mut n = n
  let mut d = d
  if d is Nil {
    n = Fix(5L)
    d = Fix(2L)
  } else if !(integerp(n) && integerp(d)) {
    share_graphs__error([Str("Arguments to petersen_graph are not integers!")])
    |> ignore
  }
  let g = d_empty_graph(num_mul(Fix(2L), n))
  let mut positions : Value = Nil
  let nn = to_int(n)
  for ii in 0..<nn {
    let i = int(ii)
    add_h_edge(list([i, num_add(n, i)]), g) |> ignore
    if !num_eq(n, num_mul(Fix(2L), d)) || num_lt(i, d) {
      let u = num_add(i, n)
      let v = num_add(num_mod(num_add(i, d), n), n)
      let e1 = num_min(v, u)
      let e2 = num_max(v, u)
      add_h_edge(list([e1, e2]), g) |> ignore
    }
    let u = num_mod(num_add(i, Fix(1L)), n)
    let e1 = num_min(u, i)
    let e2 = num_max(u, i)
    add_h_edge(list([e1, e2]), g) |> ignore
  }
  for ii in 0..<nn {
    let i = int(ii)
    let x = num_div(num_mul(num_mul(Fix(2L), i), share_graphs__pi), n)
    positions = cons(
      share_graphs__ml(
        list([i, share_graphs__ml(list([ftake(q_p_sin, [x]), ftake(q_p_cos, [x])]))]),
      ),
      positions,
    )
    positions = cons(
      share_graphs__ml(
        list([
          num_add(n, i),
          share_graphs__ml(
            list([
              num_mul(Flo(0.66), ftake(q_p_sin, [x])),
              num_mul(Flo(0.66), ftake(q_p_cos, [x])),
            ]),
          ),
        ]),
      ),
      positions,
    )
  }
  share_graphs__set_graph_vertex_positions(
    g,
    cons(list([q_mlist, q_simp]), positions),
  )
  |> ignore
  g
}

///|
fn d_complement_graph(gr : Value) -> Value raise {
  require_graph(q_complement_graph, Fix(1L), gr) |> ignore
  let co = share_graphs__make_graph()
  let vrt = vertices(gr)
  for v in vrt.iter() {
    add_h_vertex(v, co) |> ignore
  }
  for u in vrt.iter() {
    for v in vrt.iter() {
      if num_lt(u, v) && !is_h_edge_h_in_h_graph(list([u, v]), gr).truthy() {
        add_h_edge(list([u, v]), co) |> ignore
      }
    }
  }
  share_graphs__set_graph_vertex_positions(
    co,
    share_graphs__graph_vertex_positions(gr),
  )
  |> ignore
  co
}

///|
fn d_complete_graph(n : Value) -> Value raise {
  if !(integerp(n) && num_ge(n, Fix(0L))) {
    share_graphs__error([
      Str("Argument 1 to complete_graph is not a positive integer"),
    ])
    |> ignore
  }
  let g = d_empty_graph(n)
  let mut pos : Value = Nil
  let nn = to_int(n)
  for i in 0..<nn {
    for j in (i + 1)..<nn {
      add_h_edge(list([int(i), int(j)]), g) |> ignore
    }
  }
  for i in 0..<nn {
    let x = num_div(num_mul(num_mul(Fix(2L), int(i)), share_graphs__pi), n)
    pos = cons(
      share_graphs__ml(
        list([int(i), share_graphs__ml(list([ftake(q_p_cos, [x]), ftake(q_p_sin, [x])]))]),
      ),
      pos,
    )
  }
  share_graphs__set_graph_vertex_positions(g, cons(list([q_mlist, q_simp]), pos))
  |> ignore
  g
}

///|
fn d_from_adjacency_matrix(m : Value) -> Value raise {
  if !d_matrixp(m).truthy() {
    share_graphs__error([Str("Argument 1 to from_adjacency_matrix is not a matrix")])
    |> ignore
  }
  if !num_eq(d_length(m), d_length(d_first(m))) {
    share_graphs__error([
      Str("Argument 1 to from_adjacency_matrix is not a square matrix"),
    ])
    |> ignore
  }
  let n = d_length(m)
  let g = d_empty_graph(n)
  let nn = to_int(n)
  for i in 0..<nn {
    for j in (i + 1)..<nn {
      if !num_eq(Fix(0L), nth(i + 1, nth(j + 1, m))) {
        add_h_edge(list([int(i), int(j)]), g) |> ignore
      }
    }
  }
  g
}

///|
fn d_graph_union(gr_list : Value) -> Value raise {
  let n = length(gr_list)
  if n == 0 {
    d_empty_graph(Fix(0L))
  } else if n == 1 {
    car(gr_list)
  } else if n == 2 {
    graph_h_union(car(gr_list), cadr(gr_list))
  } else {
    graph_h_union(car(gr_list), d_graph_union(cdr(gr_list)))
  }
}

///|
fn graph_h_union(g1 : Value, g2 : Value) -> Value raise {
  require_graph(q_graph_union, Fix(1L), g1) |> ignore
  require_graph(q_graph_union, Fix(2L), g2) |> ignore
  let g = share_graphs__make_graph()
  let n = num_add(Fix(1L), share_graphs__max_list(share_graphs__graph_vertices(g1)))
  for v in share_graphs__graph_vertices(g1).iter() {
    add_h_vertex(v, g) |> ignore
  }
  for e in share_graphs__graph_edges(g1).iter() {
    add_h_edge(e, g) |> ignore
  }
  for v in share_graphs__graph_vertices(g2).iter() {
    add_h_vertex(num_add(n, v), g) |> ignore
  }
  for e in share_graphs__graph_edges(g2).iter() {
    add_h_edge(list([num_add(n, car(e)), num_add(n, cadr(e))]), g) |> ignore
  }
  g
}

///|
fn d_graph_join(g1 : Value, g2 : Value) -> Value raise {
  require_graph(q_graph_join, Fix(1L), g1) |> ignore
  require_graph(q_graph_join, Fix(2L), g2) |> ignore
  let g = share_graphs__make_graph()
  let n = num_add(Fix(1L), share_graphs__max_list(share_graphs__graph_vertices(g1)))
  for v in share_graphs__graph_vertices(g1).iter() {
    add_h_vertex(v, g) |> ignore
  }
  for e in share_graphs__graph_edges(g1).iter() {
    add_h_edge(e, g) |> ignore
  }
  for v in share_graphs__graph_vertices(g2).iter() {
    add_h_vertex(num_add(n, v), g) |> ignore
  }
  for e in share_graphs__graph_edges(g2).iter() {
    add_h_edge(list([num_add(n, car(e)), num_add(n, cadr(e))]), g) |> ignore
  }
  for v in share_graphs__graph_vertices(g1).iter() {
    for u in share_graphs__graph_vertices(g2).iter() {
      add_h_edge(list([v, num_add(n, u)]), g) |> ignore
    }
  }
  g
}

///|
fn get_canonical_names(l : Value) -> Value raise {
  let mut names : Value = Nil
  let mut i = 0
  for v in l.iter() {
    names = cons(cons(v, int(i)), names)
    i = i + 1
  }
  names
}

///|
fn d_graph_product(gr_list : Value) -> Value raise {
  let n = length(gr_list)
  if n == 0 {
    d_empty_graph(Fix(0L))
  } else if n == 1 {
    car(gr_list)
  } else if n == 2 {
    graph_h_product(car(gr_list), cadr(gr_list))
  } else {
    graph_h_product(car(gr_list), d_graph_product(cdr(gr_list)))
  }
}

///|
fn graph_h_product(g1 : Value, g2 : Value) -> Value raise {
  require_graph(q_graph_product, Fix(1L), g1) |> ignore
  require_graph(q_graph_product, Fix(2L), g2) |> ignore
  let names1 = get_canonical_names(share_graphs__graph_vertices(g1))
  let names2 = get_canonical_names(share_graphs__graph_vertices(g2))
  let size1 = share_graphs__graph_order(g1)
  let size2 = share_graphs__graph_order(g2)
  let size = num_mul(size1, size2)
  let g = d_empty_graph(size)
  for e in share_graphs__graph_edges(g1).iter() {
    for v in share_graphs__graph_vertices(g2).iter() {
      let v1 = cdr(assoc(car(e), names1))
      let v2 = cdr(assoc(cadr(e), names1))
      let u = cdr(assoc(v, names2))
      let f = list([
        num_add(num_mul(u, size1), v1),
        num_add(num_mul(u, size1), v2),
      ])
      let f = list([share_graphs__min_list(f), share_graphs__max_list(f)])
      add_h_edge(f, g) |> ignore
    }
  }
  for e in share_graphs__graph_edges(g2).iter() {
    for v in share_graphs__graph_vertices(g1).iter() {
      let v1 = cdr(assoc(car(e), names2))
      let v2 = cdr(assoc(cadr(e), names2))
      let u = cdr(assoc(v, names1))
      let f = list([
        num_add(num_mul(v1, size1), u),
        num_add(num_mul(v2, size1), u),
      ])
      let f = list([share_graphs__min_list(f), share_graphs__max_list(f)])
      add_h_edge(f, g) |> ignore
    }
  }
  g
}

///|
fn d_line_graph(gr : Value) -> Value raise {
  require_graph(q_line_graph, Fix(1L), gr) |> ignore
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
  g
}

///|
fn d_random_graph(n : Value, p : Value) -> Value raise {
  if !integerp(n) {
    share_graphs__error([Str("Argument 1 to random_graph is not an integer")])
    |> ignore
  }
  if !floatp(d_float(p)) {
    share_graphs__error([Str("Argument 2 to random_graph is not a float")])
    |> ignore
  }
  let g = d_empty_graph(n)
  let p = d_float(p)
  let nn = to_int(n)
  for i in 0..<nn {
    for j in (i + 1)..<nn {
      if num_lt(mt_random(Flo(1.0)), p) {
        add_h_edge(list([int(i), int(j)]), g) |> ignore
      }
    }
  }
  g
}

///|
fn d_random_graph1(n : Value, m : Value) -> Value raise {
  if !integerp(n) {
    share_graphs__error([Str("Argument 1 to random_graph is not an integer")])
    |> ignore
  }
  if !integerp(m) {
    share_graphs__error([Str("Argument 2 to random_graph is not an integer")])
    |> ignore
  }
  let nn1 = num_mul(n, num_sub(n, Fix(1L)))
  if num_lt(nn1, num_mul(Fix(2L), m)) {
    share_graphs__error([Str("random_graph1: no such graph")]) |> ignore
  }
  if num_lt(nn1, num_mul(Fix(4L), m)) {
    return d_complement_graph(
      d_random_graph1(n, num_sub(num_div(nn1, Fix(2L)), m)),
    )
  }
  let g = d_empty_graph(n)
  let mut i : Value = Fix(0L)
  while !num_eq(i, m) {
    let u = mt_random(n)
    let v = mt_random(n)
    if !num_eq(u, v) {
      let e = list([num_min(u, v), num_max(u, v)])
      if !is_h_edge_h_in_h_graph(e, g).truthy() {
        i = num_add(i, Fix(1L))
        add_h_edge(e, g) |> ignore
      }
    }
  }
  g
}

///|
fn d_random_bipartite_graph(a : Value, b : Value, p : Value) -> Value raise {
  if !integerp(a) {
    share_graphs__error([Str("Argument 1 to random graph is not an integer")])
    |> ignore
  }
  if !integerp(b) {
    share_graphs__error([Str("Argument b to random graph is not an integer")])
    |> ignore
  }
  let g = d_empty_graph(num_add(a, b))
  for x in 0..<to_int(a) {
    for y in 0..<to_int(b) {
      if num_lt(mt_random(Flo(1.0)), p) {
        add_h_edge(list([int(x), num_add(a, int(y))]), g) |> ignore
      }
    }
  }
  g
}

///|
fn d_random_digraph(n : Value, p : Value) -> Value raise {
  if !integerp(n) {
    share_graphs__error([Str("Argument 1 to random_digraph is not an integer")])
    |> ignore
  }
  if !floatp(d_float(p)) {
    share_graphs__error([Str("Argument 2 to random_digraph is not a float")])
    |> ignore
  }
  let g = d_empty_digraph(n)
  let p = d_float(p)
  let nn = to_int(n)
  for i in 0..<nn {
    for j in 0..<nn {
      if i != j && num_lt(mt_random(Flo(1.0)), p) {
        add_h_edge(list([int(i), int(j)]), g) |> ignore
      }
    }
  }
  g
}

///|
fn d_random_tournament(n : Value) -> Value raise {
  if !(integerp(n) && num_ge(n, Fix(0L))) {
    share_graphs__error([
      Str("Argument 1 to random_tournament is not a positive integer"),
    ])
    |> ignore
  }
  let g = d_empty_digraph(n)
  let nn = to_int(n)
  for i in 0..<nn {
    for j in (i + 1)..<nn {
      if i != j && num_lt(mt_random(Flo(1.0)), Flo(0.5)) {
        add_h_edge(list([int(i), int(j)]), g) |> ignore
      } else {
        add_h_edge(list([int(j), int(i)]), g) |> ignore
      }
    }
  }
  g
}

///|
fn d_random_tree(n : Value) -> Value raise {
  if !(integerp(n) && num_ge(n, Fix(0L))) {
    share_graphs__error([Str("Argument 1 to random_tree is not a positive integer")])
    |> ignore
  }
  let tr = d_empty_graph(n)
  let mut vrt = share_graphs__remove1(Fix(0L), share_graphs__graph_vertices(tr))
  let mut tree_vrt = list1(Fix(0L))
  for _ in 0..<(to_int(n) - 1) {
    let u = nth(to_int(mt_random(int(length(vrt)))), vrt)
    let v = nth(to_int(mt_random(int(length(tree_vrt)))), tree_vrt)
    vrt = share_graphs__remove1(u, vrt)
    tree_vrt = cons(u, tree_vrt)
    add_h_edge(list([num_min(u, v), num_max(u, v)]), tr) |> ignore
  }
  tr
}

///|
fn d_underlying_graph(gr : Value) -> Value raise {
  require_digraph(q_underlying_graph, Fix(1L), gr) |> ignore
  let g = share_graphs__make_graph()
  for v in vertices(gr).iter() {
    add_h_vertex(v, g) |> ignore
  }
  for e in share_graphs__digraph_edges(gr).iter() {
    let u = car(e)
    let v = cadr(e)
    let e1 = list([share_graphs__min_list(e), share_graphs__max_list(e)])
    if !is_h_edge_h_in_h_graph(e1, g).truthy() {
      add_h_edge(list([u, v]), g) |> ignore
    }
  }
  g
}

///|
fn d_induced_subgraph(vl : Value, gr : Value) -> Value raise {
  require_graph(Fix(2L), q_induced_subgraph, gr) |> ignore
  if !d_listp(vl).truthy() {
    share_graphs__error([Str("First argument to induced_subgraph is not a list.")])
    |> ignore
  }
  let v_l = cdr(vl)
  let g = share_graphs__make_graph()
  for v in v_l.iter() {
    if !is_vertex_in_graph(v, gr).truthy() {
      share_graphs__error([
        Str("induced_subgraph: second argument is not a list of vertices"),
      ])
      |> ignore
    }
    add_h_vertex(v, g) |> ignore
    let l = get_h_vertex_h_label(v, gr)
    if l.truthy() {
      set_h_vertex_h_label(v, l, g) |> ignore
    }
  }
  for e in share_graphs__graph_edges(gr).iter() {
    let u = car(e)
    let v = cadr(e)
    if member(u, v_l).truthy() && member(v, v_l).truthy() {
      add_h_edge(e, g) |> ignore
    }
  }
  g
}

///|
fn d_wheel_graph(n : Value) -> Value raise {
  if !(integerp(n) && num_ge(n, Fix(3L))) {
    share_graphs__error([
      Str("wheel_graph: first argument is no an integer greater than 3"),
    ])
    |> ignore
  }
  let g = d_cycle_graph(n)
  let mut positions : Value = Nil
  add_h_vertex(n, g) |> ignore
  let nn = to_int(n)
  for i in 0..<nn {
    add_h_edge(list([int(i), n]), g) |> ignore
  }
  for i in 0..<nn {
    let x = num_div(num_mul(num_mul(Fix(2L), int(i)), share_graphs__pi), n)
    positions = cons(
      share_graphs__ml(
        list([int(i), share_graphs__ml(list([ftake(q_p_sin, [x]), ftake(q_p_cos, [x])]))]),
      ),
      positions,
    )
  }
  positions = cons(
    share_graphs__ml(list([n, share_graphs__ml(list([Fix(0L), Fix(0L)]))])),
    positions,
  )
  d_set_positions(cons(list([q_mlist, q_simp]), positions), g) |> ignore
  g
}

///|
fn d_circulant_graph(n : Value, l : Value) -> Value raise {
  if !(integerp(n) && num_gt(n, Fix(0L))) {
    share_graphs__error([
      Str("Argument 1 to circulant_graph is not a positive integer."),
    ])
    |> ignore
  }
  if !d_listp(l).truthy() {
    share_graphs__error([Str("Argument 2 to circulant_graph is not a list.")])
    |> ignore
  }
  let g = d_empty_graph(n)
  let mut positions : Value = Nil
  let nn = to_int(n)
  for d in cdr(l).iter() {
    if !(integerp(d) && num_gt(d, Fix(0L))) {
      share_graphs__error([
        Str("Argument 2 to circulant graph is no a list of positive integers"),
      ])
      |> ignore
    }
    for i in 0..<nn {
      let e = list([int(i), num_mod(num_add(int(i), d), n)])
      let e = list([share_graphs__min_list(e), share_graphs__max_list(e)])
      add_h_edge(e, g) |> ignore
    }
  }
  for i in 0..<nn {
    let x = div_star(mul_star(list([Flo(2.0), int(i), share_graphs__pi])), n)
    positions = cons(
      share_graphs__ml(
        list([int(i), share_graphs__ml(list([ftake(q_p_sin, [x]), ftake(q_p_cos, [x])]))]),
      ),
      positions,
    )
  }
  d_set_positions(cons(list([q_mlist, q_simp]), positions), g) |> ignore
  g
}
