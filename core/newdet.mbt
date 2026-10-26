// Port of src/newdet.lisp: a version of the Gentleman-Johnson tree-minor
// determinant using rational functions. "A" can be a matrix or an array.
// Answer is in rational form. (RJF 5/2/73)
//
// The minors of the first m columns are computed and stored, developing
// each on its last column, so that the determinant of an n*n matrix takes
// n*(2^(n-1)-1) multiplications of (rational function) entries.

///|
fn d_newdet(mat : Value) -> Value raise {
  if !(mbagp(mat).truthy() || d_matrixp(mat).truthy()) {
    if d_scalarp(mat).truthy() {
      mat
    } else {
      list2(list2(q_p_newdet, q_simp), mat)
    }
  } else {
    let mat = check(mat)
    if length(mat) != length(cadr(mat)) {
      merr("newdet: Matrix must be square; found ~M rows, ~M columns.", [
        int(length(cdr(mat))),
        int(length(cdadr(mat))),
      ])
      |> ignore
    }
    newdet(mat, int(length(cdr(mat))), Nil)
  }
}

///|
fn d_permanent(mat : Value) -> Value raise {
  if !(mbagp(mat).truthy() || d_matrixp(mat).truthy()) {
    if d_scalarp(mat).truthy() {
      mat
    } else {
      list2(list2(q_p_permanent, q_simp), mat)
    }
  } else {
    let mat = check(mat)
    if length(mat) != length(cadr(mat)) {
      merr("permanent: Matrix must be square; found ~M rows, ~M columns.", [
        int(length(cdr(mat))),
        int(length(cdadr(mat))),
      ])
      |> ignore
    }
    newdet(mat, int(length(cdr(mat))), t)
  }
}

///|
fn newdet__get(s : Value, i : Int, j : Int) -> Value raise {
  aref(symval(s), [i, j])
}

///|
fn newdet__set(s : Value, i : Int, j : Int, v : Value) -> Unit raise {
  aset(symval(s), [i, j], v) |> ignore
}

///|
fn newdet__iget(i : Int) -> Int raise {
  to_int(aref1(symval(q_ear_i), i))
}

///|
fn newdet__iset(i : Int, v : Int) -> Unit raise {
  aset1(symval(q_ear_i), i, int(v)) |> ignore
}

///|
fn newdet__binom(i : Int, j : Int) -> Int raise {
  to_int(newdet__get(q_ear_binom, i, j))
}

///|
fn newdet(a : Value, n : Value, perm : Value) -> Value raise {
  with_special(q_vlist, Nil, () => {
    if num_gt(n, Fix(50L)) {
      merr("newdet: matrix must be 50 by 50 or smaller; found size: ~M", [n])
      |> ignore
    }
    let n = to_int(n)
    let zero = cons(Fix(0L), Fix(1L))
    set(q_ear_binom, make_array([1 + n, 1 + n], initial=Fix(0L))) |> ignore
    let rr = to_int(pascal(int(n)))
    set(q_ear_minor1, make_array([2, 1 + rr], initial=Fix(0L))) |> ignore
    set(q_ear_i, make_array([2 + n], initial=Fix(0L))) |> ignore
    for k in 0..=1 {
      for j in 0..=rr {
        newdet__set(q_ear_minor1, k, j, zero)
      }
    }
    for k in 0..=(n + 1) {
      newdet__iset(k, -1)
    }
    set(q_ear_input, make_array([1 + n, 1 + n], initial=Fix(0L))) |> ignore
    for k in 1..=n {
      for j in 1..=n {
        let v = with_special(q_aryp, t, () => linnew__maref1(a, [int(k), int(j)]))
        newdet__set(q_ear_input, k, j, v)
        newvar1(v) |> ignore
      }
    }
    newvar(cons(list1(q_mtimes), symval(q_vlist))) |> ignore
    for k in 1..=n {
      for j in 1..=n {
        newdet__set(
          q_ear_input,
          k,
          j,
          cdr(ratrep_star(newdet__get(q_ear_input, k, j))),
        )
      }
    }
    let mut new = 1
    let mut old = 0
    newdet__iset(0, n)
    for loc in 1..=n {
      newdet__set(q_ear_minor1, old, loc - 1, newdet__get(q_ear_input, 1, loc))
    }
    let mut m = 1
    let mut loc = 0
    let mut j = 0
    let mut k = 0
    let mut addr = 0
    let mut sign = 1
    // States: 0 = G0193, 1 = NEXTMINOR, 2 = NEXTUSE, 3 = OVER, 4 = BACK,
    // 5 = RET
    let mut state = 0
    while state != 5 {
      match state {
        0 => {
          if m > n - 1 {
            state = 5
            continue
          }
          loc = 0
          j = 1
          while j <= m {
            newdet__iset(j, m - j)
            j = j + 1
          }
          state = 1
        }
        1 =>
          if !equal(newdet__get(q_ear_minor1, old, loc), zero) {
            k = n - 1
            j = 0
            addr = loc + newdet__binom(k, m + 1)
            sign = 1
            state = 2
          } else {
            state = 3
          }
        2 => {
          if k == newdet__iget(j + 1) {
            j = j + 1
            sign = -sign
          } else {
            let e = newdet__get(q_ear_input, m + 1, k + 1)
            newdet__set(
              q_ear_minor1,
              new,
              addr,
              ratplus(
                newdet__get(q_ear_minor1, new, addr),
                rattimes(
                  newdet__get(q_ear_minor1, old, loc),
                  if sign == 1 || perm.truthy() {
                    e
                  } else {
                    ratminus(e)
                  },
                  t,
                ),
              ),
            )
          }
          if k > 0 {
            k = k - 1
            addr = addr - newdet__binom(k, m - j)
            continue
          }
          newdet__set(q_ear_minor1, old, loc, zero)
          state = 3
        }
        3 => {
          loc = loc + 1
          j = m
          state = 4
        }
        _ => {
          if 1 > j {
            m = m + 1
            old = 1 - old
            new = 1 - new
            state = 0
            continue
          }
          newdet__iset(j, newdet__iget(j) + 1)
          if newdet__iget(j - 1) > newdet__iget(j) {
            state = 1
            continue
          } else {
            newdet__iset(j, m - j)
          }
          j = j - 1
        }
      }
    }
    cons(
      list([q_mrat, q_simp, symval(q_varlist), symval(q_genvar)]),
      newdet__get(q_ear_minor1, old, 0),
    )
  })
}

///|
fn pascal(n : Value) -> Value raise {
  let n = to_int(n)
  newdet__set(q_ear_binom, 0, 0, Fix(1L))
  for h in 1..=n {
    newdet__set(q_ear_binom, h, 0, Fix(1L))
    newdet__set(q_ear_binom, h - 1, h, Fix(0L))
    for j in 1..=h {
      newdet__set(
        q_ear_binom,
        h,
        j,
        num_add(
          newdet__get(q_ear_binom, h - 1, j - 1),
          newdet__get(q_ear_binom, h - 1, j),
        ),
      )
    }
  }
  one_minus(newdet__get(q_ear_binom, n, n / 2))
}
