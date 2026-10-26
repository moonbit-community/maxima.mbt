// Port of share/graphs/graph6.lisp: read/write support for the graph6 and
// sparse6 formats (http://cs.anu.edu.au/~bdm/data/formats.txt) and for dig6
// (graph6 for directed graphs, used in SAGE).
//
// GRAPHS - graph theory package for Maxima
// Copyright (C) 2007 Andrej Vodopivec <andrej.vodopivec@gmail.com>
// (GPL v2 or later)

// ---------------------------------------------------------------------------
// helper functions

///|
fn get_n(n : Value) -> Value raise {
  if num_lt(n, Fix(63L)) {
    list1(num_add(n, Fix(63L)))
  } else {
    list([
      Fix(126L),
      num_add(Fix(63L), logand(Fix(63L), ash(n, -12))),
      num_add(Fix(63L), logand(Fix(63L), ash(n, -6))),
      num_add(Fix(63L), logand(Fix(63L), n)),
    ])
  }
}

///|
fn get_r(n : Value) -> Value raise {
  let mut n = n
  let mut val : Value = Nil
  while num_gt(n, Fix(0L)) {
    val = cons(num_add(Fix(63L), logand(n, Fix(63L))), val)
    n = ash(n, -6)
  }
  val
}

///|
/// `(format nil "~{~c~}" (mapcar #'code-char codes))`
fn share_graphs__codes_string(prefix : String, codes : Value) -> Value raise {
  let sb = StringBuilder::new()
  sb.write_string(prefix)
  for c in codes.iter() {
    sb.write_char(code_char(to_int(c)))
  }
  Str(sb.to_string())
}

///|
/// `(subseq s start end)` on a string (`end` = -1: to the end).
fn share_graphs__subseq(s : String, start : Int, end : Int) -> String raise {
  let chars = string_chars(s)
  let end = if end < 0 { chars.length() } else { end }
  if start < 0 || start > end || end > chars.length() {
    raise LispError::SimpleError(
      "The bounding indices \{start} and \{end} are bad for a sequence of length \{chars.length()}.",
    )
  }
  let sb = StringBuilder::new()
  for i in start..<end {
    sb.write_char(chars[i])
  }
  sb.to_string()
}

///|
/// `(mapcar #'char-code (coerce str 'list))`
fn share_graphs__string_codes(s : String) -> Value {
  let r = []
  for c in s {
    r.push(int(char_code(c)))
  }
  list(r)
}

///|
/// `(with-open-file (stream fl :direction :output :if-exists :supersede)
///    (dolist (g (cdr graphs)) (format stream "~a~%" (encode g))))`
fn share_graphs__export(
  graphs : Value,
  fl : Value,
  encode : (Value) -> Value raise,
) -> Unit raise {
  let sb = StringBuilder::new()
  for g in cdr(graphs).iter() {
    sb.write_string(princ_to_string(encode(g)))
    sb.write_char('\n')
  }
  match fl {
    Str(name) => write_file(name, sb.to_string())
    _ => ()
  }
}

///|
/// The lines of the file `fl`, read with `read-line`, decoded and collected
/// in reverse order.
fn share_graphs__import(fl : Value, decode : (Value) -> Value raise) -> Value raise {
  let name = match fl {
    Str(s) => s
    _ => ""
  }
  let stream = open_input_file(name)
  let mut lst : Value = Nil
  while read_line(stream~) is Some(line) {
    lst = cons(decode(Str(line)), lst)
  }
  share_graphs__ml(lst)
}

// ---------------------------------------------------------------------------
// encode to graph6 string

///|
fn d_graph6_encode(gr : Value) -> Value raise {
  require_graph(q_graph6_decode, Fix(1L), gr) |> ignore
  graph6_string(gr)
}

///|
fn graph6_string(gr : Value) -> Value raise {
  let n = d_graph_order(gr)
  let names = get_canonical_names(vertices(gr))
  // encode edges
  let mut e_val : Value = Fix(1L)
  let nn = to_int(n)
  for i in 1..<nn {
    for j in 0..<i {
      let u = car(rassoc(int(i), names))
      let v = car(rassoc(int(j), names))
      e_val = ash(e_val, 1)
      if is_h_edge_h_in_h_graph(list([num_min(u, v), num_max(u, v)]), gr).truthy() {
        e_val = num_add(e_val, Fix(1L))
      }
    }
  }
  // add zeros to the right
  let n1 = num_mod(num_div(num_mul(n, num_sub(n, Fix(1L))), Fix(2L)), Fix(6L))
  if !num_eq(n1, Fix(0L)) {
    e_val = ash(e_val, 6 - to_int(n1))
  }
  // change bits to string
  share_graphs__codes_string("", append(get_n(n), cdr(get_r(e_val))))
}

///|
fn d_graph6_export(graphs : Value, fl : Value) -> Value raise {
  if !stringp(fl) {
    merr("`graph6_export': second argument is not a string.", []) |> ignore
  }
  if !d_listp(graphs).truthy() {
    merr("`graph6_export': first argument is not a list.", []) |> ignore
  }
  share_graphs__export(graphs, fl, d_graph6_encode)
  q_done
}

// ---------------------------------------------------------------------------
// decode from graph6 string

///|
/// The number of vertices and the remaining bytes of a graph6/sparse6/dig6
/// string.
fn share_graphs__read_n(bits : Value) -> (Value, Value) raise {
  if num_lt(car(bits), Fix(126L)) {
    (num_sub(car(bits), Fix(63L)), cdr(bits))
  } else {
    let bits = cdr(bits)
    (
      num_add(
        num_add(
          ash(num_sub(car(bits), Fix(63L)), 12),
          ash(num_sub(cadr(bits), Fix(63L)), 6),
        ),
        num_sub(caddr(bits), Fix(63L)),
      ),
      cdddr(bits),
    )
  }
}

///|
fn d_graph6_decode(str : Value) -> Value raise {
  // get a lisp string
  if !stringp(str) {
    merr("`graph6_decode': argument is not a string.", []) |> ignore
  }
  let mut s = match str {
    Str(s) => s
    _ => ""
  }
  // read bits from string
  if string_length(s) > 10 && share_graphs__subseq(s, 0, 10) == ">>graph6<<" {
    s = share_graphs__subseq(s, 10, -1)
  }
  // check if it is actually sparse6
  if share_graphs__subseq(s, 0, 1) == ":" {
    merr("`graph6_decode': wrong format.", []) |> ignore
  }
  // read the data
  let mut e_val : Value = Fix(0L)
  let bits = share_graphs__string_codes(s)
  let (n, e_bits) = share_graphs__read_n(bits)
  for v in e_bits.iter() {
    e_val = ash(e_val, 6)
    e_val = num_add(e_val, num_sub(v, Fix(63L)))
  }
  // remove trailing zeros
  let n1 = num_mod(num_div(num_mul(n, num_sub(n, Fix(1L))), Fix(2L)), Fix(6L))
  if !num_eq(n1, Fix(0L)) {
    e_val = ash(e_val, to_int(n1) - 6)
  }
  // construct graph
  let g = d_empty_graph(n)
  let mut i = to_int(n) - 1
  while i >= 0 {
    let mut j = i - 1
    while j >= 0 {
      if num_gt(logand(e_val, Fix(1L)), Fix(0L)) {
        add_h_edge(list([int(j), int(i)]), g) |> ignore
      }
      e_val = ash(e_val, -1)
      j = j - 1
    }
    i = i - 1
  }
  g
}

///|
fn d_graph6_import(fl : Value) -> Value raise {
  if !stringp(fl) {
    merr("`graph6_import': argument is not a string.", []) |> ignore
  }
  share_graphs__import(fl, d_graph6_decode)
}

// ---------------------------------------------------------------------------
// decode from sparse6 string

///|
fn d_sparse6_decode(str : Value) -> Value raise {
  // get a lisp string
  if !stringp(str) {
    merr("`sparse6_decode': argument is not a string.", []) |> ignore
  }
  let mut s = match str {
    Str(s) => s
    _ => ""
  }
  // read bits from string
  if string_length(s) > 11 && share_graphs__subseq(s, 0, 11) == ">>sparse6<<" {
    s = share_graphs__subseq(s, 11, -1)
  }
  // the first character must be ':' and it is ignored
  if share_graphs__subseq(s, 0, 1) != ":" {
    merr("`sparse6_decode': wrong format.", []) |> ignore
  }
  s = share_graphs__subseq(s, 1, -1)
  // read the data
  let mut e_val : Value = Fix(0L)
  let bits = share_graphs__string_codes(s)
  let (n, e_bits) = share_graphs__read_n(bits)
  for v in e_bits.iter() {
    e_val = ash(e_val, 6)
    e_val = num_add(e_val, num_sub(v, Fix(63L)))
  }
  // find k
  let k = integer_length(num_sub(n, Fix(1L)))
  // construct g
  let g = d_empty_graph(n)
  let mut v : Value = Fix(0L)
  let mut i = integer_length(e_val) - 1
  while i >= k {
    let bi = if logbitp(i, e_val) { 1 } else { 0 }
    i = i - 1
    let mut xi : Value = Fix(0L)
    for _ in 0..<k {
      xi = ash(xi, 1)
      if logbitp(i, e_val) {
        xi = num_add(xi, Fix(1L))
      }
      i = i - 1
    }
    if bi == 1 {
      v = num_add(v, Fix(1L))
    }
    if num_gt(xi, v) {
      v = xi
    } else if !num_ge(v, n) {
      d_add_edge(share_graphs__ml(list([xi, v])), g) |> ignore
    }
    if num_ge(v, n) {
      i = 0
    }
  }
  g
}

///|
fn d_sparse6_import(fl : Value) -> Value raise {
  if !stringp(fl) {
    merr("`sparse6_import': argument is not a string.", []) |> ignore
  }
  share_graphs__import(fl, d_sparse6_decode)
}

// ---------------------------------------------------------------------------
// encode to sparse6 string

///|
fn d_sparse6_encode(gr : Value) -> Value raise {
  require_graph(q_sparse_encode, Fix(1L), gr) |> ignore
  sparse6_string(gr)
}

///|
fn sparse6_string(gr : Value) -> Value raise {
  let vrt = reverse(vertices(gr))
  let n = d_graph_order(gr)
  let k = integer_length(num_sub(n, Fix(1L)))
  let names = get_canonical_names(vrt)
  let mut edges = mapcar(
    u => list([cdr(assoc(car(u), names)), cdr(assoc(cadr(u), names))]),
    edges(gr),
  )
  let mut e_val : Value = Fix(0L)
  let mut v : Value = Fix(0L)
  // Sort the edges
  edges = sort_list(edges, (u, v) => {
    num_lt(cadr(u), cadr(v)) ||
    (num_eq(cadr(u), cadr(v)) && num_lt(car(u), car(v)))
  })
  for e in edges.iter() {
    let x = car(e)
    let y = cadr(e)
    if num_eq(y, v) {
      e_val = num_add(ash(e_val, 1 + k), x)
    } else {
      e_val = num_add(ash(e_val, 1), Fix(1L))
      v = num_add(v, Fix(1L))
      if num_eq(y, v) {
        e_val = num_add(ash(e_val, k), x)
      } else {
        e_val = num_add(ash(e_val, k), y)
        v = y
        e_val = num_add(ash(e_val, 1 + k), x)
      }
    }
  }
  if integer_length(e_val) % 6 != 0 {
    let n1 = integer_length(e_val) % 6
    e_val = num_sub(ash(num_add(e_val, Fix(1L)), 6 - n1), Fix(1L))
  }
  share_graphs__codes_string(":", append(get_n(n), get_r(e_val)))
}

///|
fn d_sparse6_export(graphs : Value, fl : Value) -> Value raise {
  if !stringp(fl) {
    merr("`sparse6_export': second argument is not a string.", []) |> ignore
  }
  if !d_listp(graphs).truthy() {
    merr("`sparse6_export': first argument is not a list.", []) |> ignore
  }
  share_graphs__export(graphs, fl, d_sparse6_encode)
  q_done
}

// ---------------------------------------------------------------------------
// dig6 is similar to graph6 but for directed graphs (dig6 is used in SAGE)

///|
fn d_dig6_encode(gr : Value) -> Value raise {
  require_digraph(q_dig6_decode, Fix(1L), gr) |> ignore
  dig6_string(gr)
}

///|
fn dig6_string(gr : Value) -> Value raise {
  let n = d_graph_order(gr)
  let names = get_canonical_names(vertices(gr))
  // encode edges
  let mut e_val : Value = Fix(1L)
  let nn = to_int(n)
  for i in 0..<nn {
    for j in 0..<nn {
      let u = car(rassoc(int(i), names))
      let v = car(rassoc(int(j), names))
      e_val = ash(e_val, 1)
      if is_h_edge_h_in_h_graph(list([u, v]), gr).truthy() {
        e_val = num_add(e_val, Fix(1L))
      }
    }
  }
  // add zeros to the right
  let n1 = num_mod(num_mul(n, n), Fix(6L))
  if !num_eq(n1, Fix(0L)) {
    e_val = ash(e_val, 6 - to_int(n1))
  }
  // change bits to string
  share_graphs__codes_string("", append(get_n(n), cdr(get_r(e_val))))
}

///|
fn d_dig6_export(graphs : Value, fl : Value) -> Value raise {
  if !stringp(fl) {
    merr("`dig6_export': second argument is not a string.", []) |> ignore
  }
  if !d_listp(graphs).truthy() {
    merr("`dig6_export': first argument is not a list.", []) |> ignore
  }
  share_graphs__export(graphs, fl, d_dig6_encode)
  q_done
}

///|
fn d_dig6_decode(str : Value) -> Value raise {
  // get a lisp string
  if !stringp(str) {
    merr("`dig6_decode': argument is not a string.", []) |> ignore
  }
  let s = match str {
    Str(s) => s
    _ => ""
  }
  // read bits from string (the Lisp code keeps the ">>dig6<<" header:
  // (subseq str 0))
  // read the data
  let mut e_val : Value = Fix(0L)
  let bits = share_graphs__string_codes(s)
  let (n, e_bits) = share_graphs__read_n(bits)
  for v in e_bits.iter() {
    e_val = ash(e_val, 6)
    e_val = num_add(e_val, num_sub(v, Fix(63L)))
  }
  // remove trailing zeros
  let n1 = num_mod(num_mul(n, n), Fix(6L))
  if !num_eq(n1, Fix(0L)) {
    e_val = ash(e_val, to_int(n1) - 6)
  }
  // construct graph
  let g = d_empty_digraph(n)
  let mut i = to_int(n) - 1
  while i >= 0 {
    let mut j = to_int(n) - 1
    while j >= 0 {
      if num_gt(logand(e_val, Fix(1L)), Fix(0L)) {
        add_h_edge(list([int(j), int(i)]), g) |> ignore
      }
      e_val = ash(e_val, -1)
      j = j - 1
    }
    i = i - 1
  }
  g
}

///|
fn d_dig6_import(fl : Value) -> Value raise {
  if !stringp(fl) {
    merr("`dig6_import': argument is not a string.", []) |> ignore
  }
  share_graphs__import(fl, d_dig6_decode)
}

///|
fn init_share_graph6() -> Unit raise {
  ()
}
