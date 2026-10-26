// Port of share/graphs/dijkstra.lisp: a binary heap priority queue and
// Dijkstra's algorithm for weighted shortest paths.
//
// GRAPHS - graph theory package for Maxima
// Copyright (C) 2008 Andrej Vodopivec <andrej.vodopivec@gmail.com>
// (GPL v2 or later)
//
// The defstruct graphs-pqueue (data last max index weights) is a
// `make_struct("graphs-pqueue", ...)` instance.

///|
fn share_graphs__make_pqueue() -> Value {
  make_struct("graphs-pqueue", [
    make_array([129], initial=Fix(0L)),
    Fix(0L),
    Fix(128L),
    make_hash_table(),
    make_hash_table(),
  ])
}

///|
fn share_graphs__pq_slot(queue : Value, i : Int) -> Value raise {
  if !struct_typep(queue, "graphs-pqueue") {
    raise type_error(queue, "graphs-pqueue")
  }
  struct_ref(queue, i)
}

///|
fn share_graphs__pq_data(queue : Value) -> Value raise {
  share_graphs__pq_slot(queue, 0)
}

///|
fn share_graphs__pq_last(queue : Value) -> Int raise {
  to_int(share_graphs__pq_slot(queue, 1))
}

///|
fn share_graphs__pq_set_last(queue : Value, n : Int) -> Unit raise {
  share_graphs__pq_slot(queue, 1) |> ignore
  struct_set(queue, 1, int(n)) |> ignore
}

///|
fn share_graphs__pq_index(queue : Value) -> Value raise {
  share_graphs__pq_slot(queue, 3)
}

///|
fn share_graphs__pq_weights(queue : Value) -> Value raise {
  share_graphs__pq_slot(queue, 4)
}

///|
fn share_graphs__pq_aref(queue : Value, i : Int) -> Value raise {
  aref1(share_graphs__pq_data(queue), i)
}

///|
fn share_graphs__pq_aset(queue : Value, i : Int, v : Value) -> Unit raise {
  aset1(share_graphs__pq_data(queue), i, v) |> ignore
}

///|
/// `(rotatef (aref data i) (aref data j))` and the same for the index
/// entries of the two (swapped) elements.
fn share_graphs__pq_swap(queue : Value, i : Int, j : Int) -> Unit raise {
  let a = share_graphs__pq_aref(queue, i)
  share_graphs__pq_aset(queue, i, share_graphs__pq_aref(queue, j))
  share_graphs__pq_aset(queue, j, a)
  let index = share_graphs__pq_index(queue)
  let ki = share_graphs__pq_aref(queue, i)
  let kj = share_graphs__pq_aref(queue, j)
  let vi = gethash(ki, index)
  sethash(ki, index, gethash(kj, index)) |> ignore
  sethash(kj, index, vi) |> ignore
}

///|
/// Move the element at `ind` with weight `w` up the heap.
fn share_graphs__pq_up(queue : Value, ind : Int, w : Value) -> Unit raise {
  let mut ind = ind
  let mut ind_new = ind / 2
  while ind > 1 &&
    mlsp(
      w,
      gethash(share_graphs__pq_aref(queue, ind_new), share_graphs__pq_weights(queue)),
    ).truthy() {
    share_graphs__pq_swap(queue, ind, ind_new)
    ind = ind_new
    ind_new = ind / 2
  }
}

///|
fn graphs_pqueue_insert(v : Value, w : Value, queue : Value) -> Value raise {
  if share_graphs__pq_last(queue) == 0 {
    // insert into an empty queue
    share_graphs__pq_set_last(queue, 1)
    share_graphs__pq_aset(queue, 1, v)
    sethash(v, share_graphs__pq_index(queue), Fix(1L)) |> ignore
    sethash(v, share_graphs__pq_weights(queue), w)
  } else {
    // resize the queue if needed
    let max = to_int(share_graphs__pq_slot(queue, 2))
    if max == share_graphs__pq_last(queue) {
      let new_array = adjust_array(share_graphs__pq_data(queue), [1 + max * 2])
      struct_set(queue, 0, new_array) |> ignore
      struct_set(queue, 2, int(max * 2)) |> ignore
    }
    // insert the element
    let last = share_graphs__pq_last(queue) + 1
    share_graphs__pq_set_last(queue, last)
    share_graphs__pq_aset(queue, last, v)
    sethash(v, share_graphs__pq_index(queue), int(last)) |> ignore
    sethash(v, share_graphs__pq_weights(queue), w) |> ignore
    // balance the queue
    share_graphs__pq_up(queue, last, w)
    Nil
  }
}

///|
fn graphs_pqueue_emptyp(queue : Value) -> Value raise {
  lbool(share_graphs__pq_last(queue) == 0)
}

///|
fn graphs_pqueue_first(queue : Value) -> Value raise {
  share_graphs__pq_aref(queue, 1)
}

///|
fn graphs_pqueue_get_weight(v : Value, queue : Value) -> Value raise {
  gethash(v, share_graphs__pq_weights(queue))
}

///|
fn graphs_pqueue_pop(queue : Value) -> Value raise {
  if graphs_pqueue_emptyp(queue).truthy() {
    return Nil
  }
  let top = graphs_pqueue_first(queue)
  let last = share_graphs__pq_aref(queue, share_graphs__pq_last(queue))
  let mut pos = 1
  // remove the top element
  remhash(top, share_graphs__pq_weights(queue)) |> ignore
  remhash(top, share_graphs__pq_index(queue)) |> ignore
  share_graphs__pq_set_last(queue, share_graphs__pq_last(queue) - 1)
  // put the last element into the first position
  share_graphs__pq_aset(queue, 1, last)
  sethash(last, share_graphs__pq_index(queue), Fix(1L)) |> ignore
  // rebalance the queue
  let weights = share_graphs__pq_weights(queue)
  while true {
    // find the min child
    let mut min_child = 2 * pos
    if min_child > share_graphs__pq_last(queue) {
      return top
    }
    if min_child + 1 <= share_graphs__pq_last(queue) &&
      mlsp(
        gethash(share_graphs__pq_aref(queue, min_child + 1), weights),
        gethash(share_graphs__pq_aref(queue, min_child), weights),
      ).truthy() {
      min_child = min_child + 1
    }
    // rotate if needed
    if mlsp(
        gethash(share_graphs__pq_aref(queue, pos), weights),
        gethash(share_graphs__pq_aref(queue, min_child), weights),
      ).truthy() {
      return top
    }
    share_graphs__pq_swap(queue, pos, min_child)
    pos = min_child
  }
  top
}

///|
fn graphs_pqueue_contains(v : Value, queue : Value) -> Value raise {
  lbool(
    !eq(
      share_graphs__gethash_d(v, share_graphs__pq_weights(queue), q_not_contained),
      q_not_contained,
    ),
  )
}

///|
fn graphs_pqueue_set_weight(v : Value, w : Value, queue : Value) -> Value raise {
  sethash(v, share_graphs__pq_weights(queue), w) |> ignore
  let pos = to_int(gethash(v, share_graphs__pq_index(queue)))
  // rebalance the queue
  share_graphs__pq_up(queue, pos, w)
  Nil
}

// ---------------------------------------------------------------------------
// Dijkstra's algorithm for weighted shortest paths

///|
fn dijkstra(v : Value, v1 : Value, g : Value) -> (Value, Value) raise {
  let previous = make_hash_table()
  let distance = make_hash_table()
  let mut cont = true
  let mut my_inf : Value = Fix(1L)
  let pq = share_graphs__make_pqueue()
  for e in cdr(d_edges(g)).iter() {
    my_inf = add_star(
      list([my_inf, d_abs(d_get_edge_weight(e, g, default=Fix(1L)))]),
    )
  }
  // initialize the pqueue
  for u in vertices(g).iter() {
    if num_eq(u, v) {
      graphs_pqueue_insert(u, Fix(0L), pq) |> ignore
      sethash(u, distance, Fix(0L)) |> ignore
    } else {
      graphs_pqueue_insert(u, my_inf, pq) |> ignore
      sethash(u, distance, my_inf) |> ignore
    }
  }
  // find the shortest path
  while cont && !graphs_pqueue_emptyp(pq).truthy() {
    // find the closest remaining vertex
    let u = graphs_pqueue_pop(pq)
    let u_distance = gethash(u, distance)
    if eq(gethash(u, distance), q_d_inf) || num_eq(u, v1) {
      cont = false
    } else {
      let nb = if share_graphs__graph_p(g) {
        neighbors(u, g)
      } else {
        out_h_neighbors(u, g)
      }
      for w in nb.iter() {
        if graphs_pqueue_contains(w, pq).truthy() {
          let alt = add_star(
            list([u_distance, d_get_edge_weight(share_graphs__ml(list([u, w])), g)]),
          )
          if mlsp(alt, graphs_pqueue_get_weight(w, pq)).truthy() {
            sethash(w, previous, u) |> ignore
            sethash(w, distance, alt) |> ignore
            graphs_pqueue_set_weight(w, alt, pq) |> ignore
          }
        }
      }
    }
  }
  for v in vertices(g).iter() {
    if equal(gethash(v, distance), my_inf) {
      sethash(v, distance, q_d_inf) |> ignore
    }
  }
  (distance, previous)
}

///|
fn d_shortest_weighted_path(v : Value, u : Value, g : Value) -> Value raise {
  require_graph_or_digraph(q_shortest_weighted_path, Fix(3L), g) |> ignore
  require_vertex(q_shortest_weighted_path, Fix(1L), v) |> ignore
  require_vertex_in_graph(q_shortest_weighted_path, v, g) |> ignore
  require_vertex(q_shortest_weighted_path, Fix(2L), u) |> ignore
  require_vertex_in_graph(q_shortest_weighted_path, u, g) |> ignore
  let (l, prev) = dijkstra(v, u, g)
  let l = gethash(u, l)
  if eq(l, q_d_inf) {
    share_graphs__ml(list([q_d_inf, share_graphs__ml(Nil)]))
  } else {
    let mut tu = u
    let mut p = list1(u)
    while !num_eq(tu, v) {
      tu = gethash(tu, prev)
      p = cons(tu, p)
    }
    share_graphs__ml(list([l, share_graphs__ml(p)]))
  }
}

///|
fn init_share_dijkstra() -> Unit raise {
  ()
}
