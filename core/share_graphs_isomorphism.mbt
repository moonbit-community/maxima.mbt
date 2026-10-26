// Port of share/graphs/isomorphism.lisp: graph isomorphism by extending
// partial mappings (VF2-like search).
//
// GRAPHS - graph theory package for Maxima
// Copyright (C) 2008 Andrej Vodopivec <andrej.vodopivec@gmail.com>
// (GPL v2 or later)

///|
fn d_is_isomorphic(gr1 : Value, gr2 : Value) -> Value raise {
  let o1 = d_graph_order(gr1)
  let o2 = d_graph_order(gr2)
  if num_eq(Fix(0L), o1) && num_eq(o1, o2) {
    return t
  }
  if share_graphs__graph_p(gr1) &&
    share_graphs__graph_p(gr2) &&
    isomorphism_graphs(gr1, gr2).truthy() {
    return t
  }
  if share_graphs__digraph_p(gr1) &&
    share_graphs__digraph_p(gr2) &&
    isomorphism_digraphs(gr1, gr2).truthy() {
    return t
  }
  Nil
}

///|
fn share_graphs__iso_result(iso : Value) -> Value raise {
  let mut res : Value = Nil
  if iso.truthy() {
    maphash((key, val) => res = cons(mk_simp(q_marrow, [key, val]), res), iso)
  }
  cons(list([q_mlist, q_simp]), res)
}

///|
fn d_isomorphism(gr1 : Value, gr2 : Value) -> Value raise {
  if share_graphs__graph_p(gr1) {
    if share_graphs__graph_p(gr2) {
      share_graphs__iso_result(isomorphism_graphs(gr1, gr2))
    } else {
      merr("Wrong inputs to isomorphism", [])
    }
  } else if share_graphs__digraph_p(gr1) {
    if share_graphs__digraph_p(gr2) {
      share_graphs__iso_result(isomorphism_digraphs(gr1, gr2))
    } else {
      merr("Wrong inputs to isomorphism", [])
    }
  } else {
    merr("Wrong inputs to isomorphism", [])
  }
}

///|
fn isomorphism_graphs(gr1 : Value, gr2 : Value) -> Value raise {
  let mut gr1 = gr1
  let mut gr2 = gr2
  // check the degree sequences
  let mut gr1_degrees = cdr(d_degree_sequence(gr1))
  let mut gr2_degrees = cdr(d_degree_sequence(gr2))
  if length(gr1_degrees) != length(gr2_degrees) {
    return Nil
  }
  while gr1_degrees.truthy() && gr2_degrees.truthy() {
    if !num_eq(car(gr1_degrees), car(gr2_degrees)) {
      return Nil
    }
    gr1_degrees = cdr(gr1_degrees)
    gr2_degrees = cdr(gr2_degrees)
  }
  if gr1_degrees.truthy() || gr2_degrees.truthy() {
    return Nil
  }
  let n = share_graphs__graph_order(gr1)
  let m = share_graphs__graph_size(gr1)
  if num_lt(num_mul(n, num_sub(n, Fix(1L))), num_mul(Fix(4L), m)) {
    gr1 = d_complement_graph(gr1)
    gr2 = d_complement_graph(gr2)
  }
  let mapping = make_hash_table()
  extend_isomorphism_graphs(mapping, Nil, Nil, Nil, Nil, gr1, gr2)
}

///|
fn extend_isomorphism_graphs(
  mapping : Value,
  m1 : Value,
  m2 : Value,
  out1 : Value,
  out2 : Value,
  gr1 : Value,
  gr2 : Value,
) -> Value raise {
  // check if we have found an isomorphism
  if num_eq(int(length(m1)), d_graph_order(gr1)) {
    return mapping
  }
  // compute the new candidates for matching
  let mut n_set : Value = Nil
  let mut m : Value = Nil
  if out1.truthy() {
    if out2 is Nil {
      return Nil
    }
    n_set = out1
    m = share_graphs__min_list(out2)
  } else if out2.truthy() {
    return Nil
  } else {
    for v in vertices(gr1).iter() {
      if !member(v, m1).truthy() {
        n_set = cons(v, n_set)
      }
    }
    let mut m_set : Value = Nil
    for v in vertices(gr2).iter() {
      if !member(v, m2).truthy() {
        m_set = cons(v, m_set)
      }
    }
    m = share_graphs__min_list(m_set)
  }

  // try extending the mapping
  for n in n_set.iter() {
    // we have a pair (n->m)
    let mut ok = true
    // n and m must have the same degree
    if !num_eq(d_vertex_degree(n, gr1), d_vertex_degree(m, gr2)) {
      ok = false
    }
    // check if adjacencies are preserved
    for x in m1.iter() {
      if !ok {
        break
      }
      if member(x, neighbors(n, gr1)).truthy() {
        if !member(gethash(x, mapping), neighbors(m, gr2)).truthy() {
          ok = false
        }
      } else if member(gethash(x, mapping), neighbors(m, gr2)).truthy() {
        ok = false
      }
    }
    if ok {
      // compute the new state
      let mut out1_prime : Value = Nil
      let mut out2_prime : Value = Nil
      let m1_prime = cons(n, m1)
      let m2_prime = cons(m, m2)
      // compute new out sets
      for v in m1_prime.iter() {
        for u in neighbors(v, gr1).iter() {
          if !(member(u, out1_prime).truthy() || member(u, m1_prime).truthy()) {
            out1_prime = cons(u, out1_prime)
          }
        }
      }
      for v in m2_prime.iter() {
        for u in neighbors(v, gr2).iter() {
          if !(member(u, out2_prime).truthy() || member(u, m2_prime).truthy()) {
            out2_prime = cons(u, out2_prime)
          }
        }
      }
      // if we are compatible try extending
      if length(out1_prime) == length(out2_prime) {
        sethash(n, mapping, m) |> ignore
        let extended = extend_isomorphism_graphs(
          mapping, m1_prime, m2_prime, out1_prime, out2_prime, gr1, gr2,
        )
        if extended.truthy() {
          return extended
        }
        share_graphs__remhash(n, mapping)
      }
    }
  }
  Nil
}

///|
fn isomorphism_digraphs(gr1 : Value, gr2 : Value) -> Value raise {
  // check the degree sequences
  let mut indegrees1 : Value = Nil
  let mut outdegrees1 : Value = Nil
  let mut indegrees2 : Value = Nil
  let mut outdegrees2 : Value = Nil
  for v in vertices(gr1).iter() {
    indegrees1 = cons(d_vertex_in_degree(v, gr1), indegrees1)
    outdegrees1 = cons(d_vertex_out_degree(v, gr1), outdegrees1)
  }
  for v in vertices(gr2).iter() {
    indegrees2 = cons(d_vertex_in_degree(v, gr2), indegrees2)
    outdegrees2 = cons(d_vertex_out_degree(v, gr2), outdegrees2)
  }
  indegrees1 = sort_list(indegrees1, (a, b) => num_lt(a, b))
  indegrees2 = sort_list(indegrees2, (a, b) => num_lt(a, b))
  outdegrees1 = sort_list(outdegrees1, (a, b) => num_lt(a, b))
  outdegrees2 = sort_list(outdegrees2, (a, b) => num_lt(a, b))
  while indegrees1.truthy() && indegrees2.truthy() {
    if !(
        num_eq(car(indegrees1), car(indegrees2)) &&
        num_eq(car(outdegrees1), car(outdegrees2))
      ) {
      return Nil
    }
    indegrees1 = cdr(indegrees1)
    indegrees2 = cdr(indegrees2)
    outdegrees1 = cdr(outdegrees1)
    outdegrees2 = cdr(outdegrees2)
  }
  if indegrees1.truthy() || indegrees2.truthy() {
    return Nil
  }
  let mapping = make_hash_table()
  extend_isomorphism_digraphs(mapping, Nil, Nil, Nil, Nil, Nil, Nil, gr1, gr2)
}

///|
fn extend_isomorphism_digraphs(
  mapping : Value,
  m1 : Value,
  m2 : Value,
  out1 : Value,
  out2 : Value,
  in1 : Value,
  in2 : Value,
  gr1 : Value,
  gr2 : Value,
) -> Value raise {
  // check if we have found an isomorphism
  if num_eq(int(length(m1)), d_graph_order(gr1)) {
    return mapping
  }
  // compute the new candidates for matching
  let mut n_set : Value = Nil
  let mut m : Value = Nil
  if out1.truthy() {
    if out2 is Nil {
      return Nil
    }
    n_set = out1
    m = share_graphs__min_list(out2)
  } else if out2.truthy() {
    return Nil
  } else if in1.truthy() {
    if in2 is Nil {
      return Nil
    }
    n_set = in1
    m = share_graphs__min_list(in2)
  } else {
    for v in vertices(gr1).iter() {
      if !member(v, m1).truthy() {
        n_set = cons(v, n_set)
      }
    }
    let mut m_set : Value = Nil
    for v in vertices(gr2).iter() {
      if !member(v, m2).truthy() {
        m_set = cons(v, m_set)
      }
    }
    m = share_graphs__min_list(m_set)
  }

  // try extending the mapping
  for n in n_set.iter() {
    // we have a pair (n->m)
    let mut ok = true
    // n and m must have the same degree
    if !(
        num_eq(d_vertex_in_degree(n, gr1), d_vertex_in_degree(m, gr2)) &&
        num_eq(d_vertex_out_degree(n, gr1), d_vertex_out_degree(m, gr2))
      ) {
      ok = false
    }
    // check if adjacencies are preserved (the Lisp code tests the
    // out-neighbors twice)
    for x in m1.iter() {
      if !ok {
        break
      }
      for _ in 0..<2 {
        if member(x, out_h_neighbors(n, gr1)).truthy() {
          if !member(gethash(x, mapping), out_h_neighbors(m, gr2)).truthy() {
            ok = false
          }
        } else if member(gethash(x, mapping), out_h_neighbors(m, gr2)).truthy() {
          ok = false
        }
      }
    }
    if ok {
      // compute the new state
      let mut out1_prime : Value = Nil
      let mut out2_prime : Value = Nil
      let mut in1_prime : Value = Nil
      let mut in2_prime : Value = Nil
      let m1_prime = cons(n, m1)
      let m2_prime = cons(m, m2)
      // compute new out sets
      for v in m1_prime.iter() {
        for u in in_h_neighbors(v, gr1).iter() {
          if !(member(u, in1_prime).truthy() || member(u, m1_prime).truthy()) {
            in1_prime = cons(u, in1_prime)
          }
        }
        for u in out_h_neighbors(v, gr1).iter() {
          if !(member(u, out1_prime).truthy() || member(u, m1_prime).truthy()) {
            out1_prime = cons(u, out1_prime)
          }
        }
      }
      for v in m2_prime.iter() {
        for u in in_h_neighbors(v, gr2).iter() {
          if !(member(u, in2_prime).truthy() || member(u, m2_prime).truthy()) {
            in2_prime = cons(u, in2_prime)
          }
        }
        for u in out_h_neighbors(v, gr2).iter() {
          if !(member(u, out2_prime).truthy() || member(u, m2_prime).truthy()) {
            out2_prime = cons(u, out2_prime)
          }
        }
      }
      // if we are compatible try extending
      if length(out1_prime) == length(out2_prime) &&
        length(in1_prime) == length(in2_prime) {
        sethash(n, mapping, m) |> ignore
        let extended = extend_isomorphism_digraphs(
          mapping, m1_prime, m2_prime, out1_prime, out2_prime, in1_prime, in2_prime,
          gr1, gr2,
        )
        if extended.truthy() {
          return extended
        }
        share_graphs__remhash(n, mapping)
      }
    }
  }
  Nil
}

///|
fn init_share_isomorphism() -> Unit raise {
  ()
}
