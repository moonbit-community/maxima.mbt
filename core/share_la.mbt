// Port of share/nelder_mead/la.lisp (package NELDERMEAD): a simple
// matrix-vector facility over double-float arrays.

///|
/// `(aref v i)` of a double-float vector, as a Double.
fn la__ref(v : Value, i : Int) -> Double raise {
  to_double(aref1(v, i))
}

///|
fn neldermead_ip(v : Value, w : Value, start? : Value = Fix(0L)) -> Value raise {
  let l = length(v)
  let start = to_int(start)
  let mut ax = 0.0
  for i in 0..<(l - start) {
    ax = ax + la__ref(v, i + start) * la__ref(w, i + start)
  }
  Flo(ax)
}

///|
fn neldermead_norm(v : Value, start? : Value = Fix(0L)) -> Value raise {
  Flo(to_double(neldermead_ip(v, v, start~)).sqrt())
}

///|
fn neldermead_make_matrix(m : Value, n : Value) -> Value raise {
  make_array([to_int(m), to_int(n)], initial=Flo(0.0))
}

///|
fn neldermead_make_vector(
  n : Value,
  initial_element? : Value = Flo(0.0),
) -> Value raise {
  make_array([to_int(n)], initial=initial_element)
}

///|
fn neldermead_v_starc(vector_ : Value, constant : Value) -> Value raise {
  let n = length(vector_)
  let res = neldermead_make_vector(int(n))
  let c = to_double(constant)
  for i in 0..<n {
    aset1(res, i, Flo(c * la__ref(vector_, i))) |> ignore
  }
  res
}

///|
fn neldermead_v_plusw_starc(v : Value, w : Value, c : Value) -> Value raise {
  if length(v) != length(w) {
    lisp_error("The assertion (= (LENGTH V) (LENGTH W)) failed.") |> ignore
  }
  let n = length(v)
  let res = neldermead_make_vector(int(n))
  let c = to_double(c)
  for i in 0..<n {
    aset1(res, i, Flo(la__ref(v, i) + c * la__ref(w, i))) |> ignore
  }
  res
}

///|
/// Givens QR factorization of MAT, in place: returns (R, Q).
fn neldermead_qr_factorization(
  mat : Value,
  with_q? : Value = t,
) -> (Value, Value) raise {
  let dims = array_dimensions(mat)
  let m = to_int(car(dims))
  let n = to_int(cadr(dims))
  let q = if with_q.truthy() {
    let pq = neldermead_make_matrix(int(m), int(n))
    for i in 0..<@cmp.minimum(m, n) {
      aset(pq, [i, i], Flo(1.0)) |> ignore
    }
    pq
  } else {
    Nil
  }
  let get = (a : Value, i : Int, j : Int) => to_double(aref(a, [i, j]))
  for i in 0..<(m - 1) {
    for j in (i + 1)..<m {
      let a = get(mat, i, i)
      let b = get(mat, j, i)
      if b != 0.0 {
        let r = (a * a + b * b).sqrt()
        let c = a / r
        let s = b / r
        for k in i..<m {
          let olda = get(mat, i, k)
          let oldb = get(mat, j, k)
          aset(mat, [i, k], Flo(c * olda + s * oldb)) |> ignore
          aset(mat, [j, k], Flo(-s * olda + c * oldb)) |> ignore
        }
        if with_q.truthy() {
          for k in 0..<m {
            let olda = get(q, k, i)
            let oldb = get(q, k, j)
            aset(q, [k, i], Flo(c * olda + s * oldb)) |> ignore
            aset(q, [k, j], Flo(-s * olda + c * oldb)) |> ignore
          }
        }
      }
    }
  }
  (mat, q)
}
