// Port of share/graphs/matching.lisp: maximum matchings (augmenting paths
// for bipartite graphs, Edmonds' blossom algorithm for general graphs).
//
// GRAPHS - graph theory package for Maxima
// Copyright (C) 2008 Andrej Vodopivec <andrej.vodopivec@gmail.com>
// (GPL v2 or later)
//
// The specials *matching-state* ... *matching-path* (defvar without a
// value) are bound by maximum-matching-general.

///|
fn d_max_matching(gr : Value) -> Value raise {
  require_graph(q_maximum_matching, Fix(1L), gr) |> ignore
  let partition = cdr(d_bipartition(gr))
  if partition is Nil {
    maximum_matching_general(gr)
  } else {
    maximum_matching_bipartite(gr, cdr(car(partition)), cdr(cadr(partition)))
  }
}

// ---------------------------------------------------------------------------
// the bipartite case

///|
fn maximum_matching_bipartite(
  gr : Value,
  a : Value,
  b : Value,
  cover? : Value = Nil,
) -> Value raise {
  let matching = make_hash_table()
  let mut done = false

  // greedy matching
  for e in edges(gr).iter() {
    let u = car(e)
    let v = cadr(e)
    if gethash(u, matching) is Nil && gethash(v, matching) is Nil {
      sethash(u, matching, v) |> ignore
      sethash(v, matching, u) |> ignore
    }
  }

  // augment the matching
  while !done {
    done = true
    let mut au : Value = Nil
    let mut bu : Value = Nil

    // find unmatched vertices
    for u in a.iter() {
      if gethash(u, matching) is Nil {
        au = cons(u, au)
      }
    }
    for u in b.iter() {
      if gethash(u, matching) is Nil {
        bu = cons(u, bu)
      }
    }

    // find augmenting path
    if !(au is Nil || bu is Nil) {
      let prev = make_hash_table()
      let mut new1 = au
      let mut new2 : Value = Nil
      let mut x : Value = Nil
      while new1.truthy() {
        // add edges in M^c
        new2 = Nil
        for u in new1.iter() {
          for v in neighbors(u, gr).iter() {
            if gethash(v, prev) is Nil &&
              (gethash(v, matching) is Nil ||
              !num_eq(gethash(v, matching), u)) {
              sethash(v, prev, u) |> ignore
              new2 = cons(v, new2)
            }
          }
        }
        new1 = Nil

        // add edges in M
        for v in new2.iter() {
          let u = gethash(v, matching)
          if u.truthy() {
            new1 = cons(u, new1)
            sethash(u, prev, v) |> ignore
          }
        }
      }

      // check for augmenting path
      for v in bu.iter() {
        if x.truthy() {
          break
        }
        if gethash(v, prev).truthy() {
          x = v
        }
      }

      // extend the matching
      if x.truthy() {
        done = false
        while x.truthy() {
          let u = x
          let v = gethash(x, prev)
          sethash(u, matching, v) |> ignore
          sethash(v, matching, u) |> ignore
          x = gethash(v, prev)
        }
      }
    }
  }
  if cover is Nil {
    // we want the matching
    let mut mmatching : Value = Nil
    maphash(
      (u, v) => if num_lt(u, v) {
        mmatching = cons(share_graphs__ml(list([u, v])), mmatching)
      },
      matching,
    )
    cons(list([q_mlist, q_simp]), mmatching)
  } else {
    // we want the vertex cover
    get_cover_from_matching(gr, a, matching)
  }
}

///|
fn get_cover_from_matching(gr : Value, a : Value, matching : Value) -> Value raise {
  let mut au : Value = Nil
  let mut cov : Value = Nil
  for x in cdr(a).iter() {
    if gethash(x, matching) is Nil {
      au = cons(x, au)
    }
  }
  if au is Nil {
    share_graphs__ml(sort_list(cdr(a), (p, q) => num_lt(p, q)))
  } else {
    // construct the Hungarian tree
    let prev = make_hash_table()
    let mut new1 = au
    let mut new2 : Value = Nil
    while new1.truthy() {
      // add edges in M^c
      new2 = Nil
      for u in new1.iter() {
        for v in neighbors(u, gr).iter() {
          if gethash(v, prev) is Nil &&
            (gethash(v, matching) is Nil || !num_eq(gethash(v, matching), u)) {
            sethash(v, prev, u) |> ignore
            new2 = cons(v, new2)
          }
        }
      }
      new1 = Nil
      // add edges in M
      for v in new2.iter() {
        let u = gethash(v, matching)
        if u.truthy() {
          new1 = cons(u, new1)
          sethash(u, prev, v) |> ignore
        }
      }
    }
    maphash(
      (u, v) => if member(v, a).truthy() {
        if gethash(v, prev) is Nil {
          cov = cons(v, cov)
        } else {
          cov = cons(u, cov)
        }
      },
      matching,
    )
    share_graphs__ml(sort_list(cov, (p, q) => num_lt(p, q)))
  }
}

// ---------------------------------------------------------------------------
// set partition using hash-tables

///|
fn main_vertex(v : Value, sp : Value) -> Value raise {
  let mut m = v
  while !num_eq(m, gethash(m, sp)) {
    m = gethash(m, sp)
  }
  sethash(v, sp, m) |> ignore
  m
}

///|
fn join_sets(v : Value, u : Value, sp : Value) -> Value raise {
  let k = main_vertex(u, sp)
  sethash(k, sp, main_vertex(v, sp))
}

///|
fn set_main_vertex(m : Value, v : Value, sp : Value) -> Value raise {
  sethash(main_vertex(v, sp), sp, m) |> ignore
  sethash(m, sp, m)
}

// ---------------------------------------------------------------------------
// the general case

///|
fn maximum_matching_general(gr : Value) -> Value raise {
  with_special(q_ear_matching_matching, make_hash_table(), () => {
    let mm = symval(q_ear_matching_matching)
    let mut done = false

    // greedy matching
    for e in edges(gr).iter() {
      let u = car(e)
      let v = cadr(e)
      if gethash(u, mm) is Nil && gethash(v, mm) is Nil {
        sethash(u, mm, v) |> ignore
        sethash(v, mm, u) |> ignore
      }
    }

    // augment the matching
    while !done {
      done = true
      with_specials(
        [
          (q_ear_matching_state, Nil),
          (q_ear_matching_bridge, make_hash_table()),
          (q_ear_matching_prev, make_hash_table()),
        ],
        () => {
          let mut unmatched_vertices : Value = Nil
          let mut dfsnum : Value = Nil
          let mut dfsnum_curr = 0
          let mut vertex_partition : Value = Nil
          let mut active_edges : Value = Nil
          let mut x : Value = Nil

          // find unmatched vertices
          for v in vertices(gr).iter() {
            if gethash(v, mm) is Nil {
              unmatched_vertices = cons(v, unmatched_vertices)
            }
          }
          for first_vertex in unmatched_vertices.iter() {
            if x.truthy() {
              break
            }
            dfsnum = make_hash_table()
            dfsnum_curr = 0
            set(q_ear_matching_state, make_hash_table()) |> ignore
            set(q_ear_matching_bridge, make_hash_table()) |> ignore
            vertex_partition = make_hash_table()
            set(q_ear_matching_state, make_hash_table()) |> ignore
            sethash(first_vertex, symval(q_ear_matching_state), q_a) |> ignore
            active_edges = Nil
            for v in vertices(gr).iter() {
              sethash(v, vertex_partition, v) |> ignore
            }
            for u in neighbors(first_vertex, gr).iter() {
              active_edges = cons(list([first_vertex, u]), active_edges)
            }

            // find augmenting path
            while active_edges.truthy() && x is Nil {
              let state = symval(q_ear_matching_state)
              let bridge = symval(q_ear_matching_bridge)
              let prev = symval(q_ear_matching_prev)
              let e = car(active_edges)
              active_edges = cdr(active_edges)
              let v = car(e)
              let w = cadr(e)
              let v_main = main_vertex(v, vertex_partition)
              let w_main = main_vertex(w, vertex_partition)
              if gethash(v_main, dfsnum) is Nil {
                sethash(v_main, dfsnum, int(dfsnum_curr)) |> ignore
                dfsnum_curr = dfsnum_curr + 1
              }
              if member(w_main, unmatched_vertices).truthy() &&
                !num_eq(w_main, first_vertex) {
                // we found an augmented path
                sethash(w_main, prev, v) |> ignore
                x = w_main
              } else if gethash(w_main, state) is Nil {
                // we didn't visit w yet
                sethash(w_main, state, q_b) |> ignore
                let z = gethash(w_main, mm)
                sethash(z, state, q_a) |> ignore
                for x in neighbors(z, gr).iter() {
                  if !num_eq(x, w_main) {
                    active_edges = cons(list([z, x]), active_edges)
                  }
                }
                sethash(w_main, prev, v) |> ignore
              } else if !num_eq(w_main, v_main) &&
                eql(gethash(w_main, state), q_a) {
                // found a blossom
                let mut fst : Value = Nil
                let mut lst : Value = Nil
                let mut b : Value = Nil
                if num_gt(gethash(w_main, dfsnum), gethash(v_main, dfsnum)) {
                  fst = w_main
                  lst = v_main
                  b = list([w, v])
                } else {
                  fst = v_main
                  lst = w_main
                  b = list([v, w])
                }
                let mut tmp_vrt = fst
                while !num_eq(tmp_vrt, lst) {
                  sethash(tmp_vrt, bridge, b) |> ignore
                  join_sets(lst, tmp_vrt, vertex_partition) |> ignore
                  if eql(gethash(tmp_vrt, state), q_a) {
                    tmp_vrt = main_vertex(gethash(tmp_vrt, mm), vertex_partition)
                    for u in neighbors(tmp_vrt, gr).iter() {
                      let u = main_vertex(u, vertex_partition)
                      active_edges = cons(list([tmp_vrt, u]), active_edges)
                    }
                  } else {
                    tmp_vrt = main_vertex(gethash(tmp_vrt, prev), vertex_partition)
                  }
                }
              }
            }

            // augment the path
            if x.truthy() {
              done = false
              with_special(q_ear_matching_path, list1(x), () => {
                find_augmenting_path(
                  first_vertex,
                  gethash(x, symval(q_ear_matching_prev)),
                )
                |> ignore
                while symval(q_ear_matching_path).truthy() {
                  let path = symval(q_ear_matching_path)
                  let a = car(path)
                  let b = cadr(path)
                  sethash(a, mm, b) |> ignore
                  sethash(b, mm, a) |> ignore
                  set(q_ear_matching_path, cddr(path)) |> ignore
                }
              })
            }
          }
        },
      )
    }
    let mut matching : Value = Nil
    maphash(
      (u, v) => if num_lt(u, v) {
        matching = cons(share_graphs__ml(list([u, v])), matching)
      },
      mm,
    )
    cons(list([q_mlist, q_simp]), matching)
  })
}

///|
fn share_graphs__push_path(x : Value) -> Unit {
  set(q_ear_matching_path, cons(x, symval(q_ear_matching_path))) |> ignore
}

///|
/// returns the path from b to a
fn find_augmenting_path(a : Value, b : Value) -> Value raise {
  let state = symval(q_ear_matching_state)
  let mm = symval(q_ear_matching_matching)
  let prev = symval(q_ear_matching_prev)
  let bridge = symval(q_ear_matching_bridge)
  if num_eq(a, b) {
    share_graphs__push_path(a)
  } else if eql(gethash(b, state), q_a) {
    share_graphs__push_path(b)
    share_graphs__push_path(gethash(b, mm))
    find_augmenting_path(a, gethash(gethash(b, mm), prev)) |> ignore
  } else {
    share_graphs__push_path(b)
    find_augmenting_path_1(gethash(b, mm), car(gethash(b, bridge))) |> ignore
    find_augmenting_path(a, cadr(gethash(b, bridge))) |> ignore
  }
  symval(q_ear_matching_path)
}

///|
fn find_augmenting_path_1(a : Value, b : Value) -> Value raise {
  let state = symval(q_ear_matching_state)
  let mm = symval(q_ear_matching_matching)
  let prev = symval(q_ear_matching_prev)
  let bridge = symval(q_ear_matching_bridge)
  if num_eq(a, b) {
    share_graphs__push_path(a)
  } else if eql(gethash(b, state), q_a) {
    find_augmenting_path_1(a, gethash(gethash(b, mm), prev)) |> ignore
    share_graphs__push_path(gethash(b, mm))
    share_graphs__push_path(b)
  } else {
    find_augmenting_path_1(a, cadr(gethash(b, bridge))) |> ignore
    find_augmenting_path(gethash(b, mm), car(gethash(b, bridge))) |> ignore
    share_graphs__push_path(b)
  }
  symval(q_ear_matching_path)
}

///|
fn init_share_matching() -> Unit raise {
  ()
}
