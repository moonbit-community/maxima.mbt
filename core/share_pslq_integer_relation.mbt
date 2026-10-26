// Port of share/pslq/pslq_integer_relation.lisp (Andrej Vodopivec, 2006):
// the PSLQ algorithm to find integer relations between bigfloat numbers.
//
// For a given vector x of floating point numbers we want to find a
// vector of integers m such that m.x=0 (in given precision).
//
// This implementation of PSLQ may be derived from D.H. Bailey and
// S. Plouffe, "Recognizing Numerical Constants" (1995), section "The PSLQ
// Integer Relation Algorithm".
//
// The Lisp computes gamma = (sqrt (/ 4 3)), a CL single-float, and the
// scale factors derived from it in single-float arithmetic; the port
// emulates this with MoonBit's Float.

///|
fn d_pslq_integer_relation(l : Value) -> Value raise {
  if !d_listp(l).truthy() {
    merror(
      Str("pslq_integer_relation: argument must be a list; found: ~M"),
      list1(l),
    )
    |> ignore
  }
  let n = d_length(l)
  let mut l = cdr(l)
  let a = make_array([to_int(n)], initial=Nil)
  with_special(q_d_float2bf, t, () => {
    for i in 0..<to_int(n) {
      let mut elm = car(l)
      if d_floatnump(elm).truthy() {
        aset1(a, i, elm) |> ignore
      } else {
        elm = d_bfloat(elm)
        if !d_freeof(list2(q_d__pcti, elm)).truthy() {
          return Nil
        }
        if !d_bfloatp(elm).truthy() {
          merror(
            Str(
              "pslq_integer_relation: element can't be converted to bigfloat: ~M",
            ),
            list1(elm),
          )
          |> ignore
        }
        aset1(a, i, elm) |> ignore
      }
      l = cdr(l)
    }
    let ans = pslq_integer_relations(a, n)
    if ans.truthy() {
      cons(list2(q_mlist, q_simp), ans)
    } else {
      Nil
    }
  })
}

///|
fn pslq_mabs(x : Value) -> Value raise {
  if mlsp(x, Fix(0L)).truthy() {
    m_(x)
  } else {
    x
  }
}

///|
fn pslq_nearest_integer(x : Value) -> Value raise {
  let nx = d_entier(x)
  if mlsp(Flo(0.5), m_(x, a2=nx)).truthy() {
    num_add(nx, Fix(1L))
  } else {
    nx
  }
}

///|
fn my_write_lisp_array(a : Value, s : Value, args : Value) -> Value raise {
  ignore(args)
  let d = array_dimensions(a)
  if length(d) == 1 {
    for i in 0..<to_int(first(d)) {
      format(s, " ~18a", [aref1(a, i)]) |> ignore
    }
    write_char('\n', stream=s)
  } else {
    for i in 0..<to_int(first(d)) {
      for j in 0..<to_int(second(d)) {
        format(s, " ~18a", [aref(a, [i, j])]) |> ignore
      }
      write_char('\n', stream=s)
    }
    write_char('\n', stream=s)
  }
  Nil
}

///|
/// (expt gamma i) for a single-float gamma: SBCL's repeated squaring.
fn share_pslq_integer_relation__expt(base : Float, power : Int) -> Float {
  let mut result : Float = 1.0
  let mut b = base
  let mut p = power
  while p > 0 {
    if p % 2 == 1 {
      result = result * b
    }
    p = p / 2
    if p > 0 {
      b = b * b
    }
  }
  result
}

///|
fn share_pslq_integer_relation__debug_dump(
  title : String,
  arrays : Array[(String, Value)],
) -> Unit raise {
  let out = symval(standard_output)
  print(Str(title), stream=out) |> ignore
  write_char('\n', stream=out)
  for p in arrays {
    let (name, arr) = p
    print(Str(name), stream=out) |> ignore
    write_char('\n', stream=out)
    my_write_lisp_array(arr, out, list2(q_d_comma, q_text)) |> ignore
  }
}

///|
fn pslq_integer_relations(x : Value, n : Value) -> Value raise {
  let nn = to_int(n)
  let a = make_array([nn, nn], initial=Fix(0L))
  let b = make_array([nn, nn], initial=Fix(0L))
  let h = make_array([nn, nn - 1], initial=Fix(0L))
  let gamma : Float = Float::from_double(
    Float::from_double(4.0 / 3.0).to_double().sqrt(),
  )
  let s = make_array([nn], initial=Fix(0L))
  let y = make_array([nn], initial=Fix(0L))
  let precision = if symval(q_d_pslq_precision).truthy() {
    symval(q_d_pslq_precision)
  } else {
    power(Fix(10L), num_sub(symval(q_d_fpprec), Fix(2L)))
  }
  let threshold = if symval(q_d_pslq_threshold).truthy() {
    symval(q_d_pslq_threshold)
  } else {
    power(Fix(10L), num_sub(Fix(2L), symval(q_d_fpprec)))
  }
  let depth = if symval(q_d_pslq_depth).truthy() {
    symval(q_d_pslq_depth)
  } else {
    num_mul(Fix(20L), n)
  }
  with_specials(
    [
      (q_d_pslq_precision, precision),
      (q_d_pslq_threshold, threshold),
      (q_d_pslq_depth, depth),
    ],
    () => {
      let debugging = () => symval(q_ear_pslq_debugging).truthy()
      let get2 = (arr : Value, i : Int, j : Int) => aref(arr, [i, j])
      let set2 = (arr : Value, i : Int, j : Int, v : Value) => {
        aset(arr, [i, j], v) |> ignore
      }
      let get1 = (arr : Value, i : Int) => aref1(arr, i)
      let set1 = (arr : Value, i : Int, v : Value) => {
        aset1(arr, i, v) |> ignore
      }
      let mut tt : Value = Nil
      if debugging() {
        format(
          t,
          "PSLQ-INTEGER-RELATIONS: n = ~a, gamma = ~a, pslq_precision = ~a, pslq_threshold =  ~a, pslq_depth = ~a~%",
          [
            n,
            Flo(gamma.to_double()),
            symval(q_d_pslq_precision),
            symval(q_d_pslq_threshold),
            symval(q_d_pslq_depth),
          ],
        )
        |> ignore
      }

      // Initialize A, B and s
      for k in 0..<nn {
        set2(a, k, k, Fix(1L))
        set2(b, k, k, Fix(1L))
        for j in k..<nn {
          set1(s, k, m_plus(list2(get1(s, k), power(get1(x, j), Fix(2L)))))
        }
        set1(s, k, d_sqrt(get1(s, k)))
      }
      tt = get1(s, 0)

      // Initialize y, normalize s
      for k in 0..<nn {
        set1(y, k, m_sl_sl(get1(x, k), a2=tt))
        set1(s, k, m_sl_sl(get1(s, k), a2=tt))
      }

      // Initialize H
      for i in 0..<nn {
        if i < nn - 1 {
          set2(h, i, i, m_sl_sl(get1(s, i + 1), a2=get1(s, i)))
        }
        for j in 0..<i {
          set2(
            h,
            i,
            j,
            m_(
              m_sl_sl(
                m_star(list2(get1(y, i), get1(y, j))),
                a2=m_star(list2(get1(s, j), get1(s, j + 1))),
              ),
            ),
          )
        }
      }
      if debugging() {
        share_pslq_integer_relation__debug_dump(
          "PSLQ-INTEGER-RELATIONS: just before initial reduce h:",
          [("A =", a), ("B =", b), ("s =", s), ("y =", y), ("H =", h)],
        )
      }

      // Perform reduction on H, update A, B, y
      for i in 1..=(nn - 1) {
        let mut j = i - 1
        while j >= 0 {
          tt = pslq_nearest_integer(m_sl_sl(get2(h, i, j), a2=get2(h, j, j)))
          set1(y, j, m_plus(list2(get1(y, j), m_star(list2(tt, get1(y, i))))))
          for k in 0..=j {
            let bar = get2(h, i, k)
            let baz = tt
            let quux = get2(h, j, k)
            let foo = m_(bar, a2=m_star(list2(baz, quux)))
            if debugging() {
              format(
                t,
                "PSLQ-INTEGER-RELATIONS: assign ~a = ~a - ~a * ~a to H[~d, ~d]~%",
                [foo, bar, baz, quux, int(i), int(k)],
              )
              |> ignore
            }
            set2(h, i, k, foo)
          }
          for k in 0..<nn {
            set2(a, i, k, m_(get2(a, i, k), a2=m_star(list2(tt, get2(a, j, k)))))
            set2(
              b,
              k,
              j,
              m_plus(list2(get2(b, k, j), m_star(list2(tt, get2(b, k, i))))),
            )
          }
          j = j - 1
        }
      }
      let mut r : Value = Fix(1L)
      while !num_eq(r, symval(q_d_pslq_depth)) {
        let mut m = 0
        let mut mm : Value = Fix(0L)
        let mut sf : Float = 1.0
        if debugging() {
          share_pslq_integer_relation__debug_dump(
            "PSLQ-INTEGER-RELATIONS: just before bound check:",
            [("A =", a), ("B =", b), ("y =", y), ("H =", h)],
          )
        }

        // Find the bound M
        let mut max_norm : Value = Fix(0L)
        for j in 0..<nn {
          let mut abs_hj : Value = Fix(0L)
          for i in 0..=(nn - 2) {
            if mlsp(abs_hj, pslq_mabs(get2(h, j, i))).truthy() {
              abs_hj = get2(h, j, i)
            }
          }
          if mlsp(max_norm, abs_hj).truthy() {
            max_norm = abs_hj
          }
        }
        set(q_d_pslq_fail_norm, m_sl_sl(Fix(1L), a2=max_norm)) |> ignore

        // Check to see if we have a relation
        for j in 0..<nn {
          if mlsp(pslq_mabs(get1(y, j)), symval(q_d_pslq_threshold)).truthy() {
            let mut ans : Value = Nil
            for i in 0..<nn {
              ans = append(ans, list1(get2(b, i, j)))
            }
            set(q_d_pslq_status, Fix(1L)) |> ignore
            return ans
          }
        }

        // Check to see if we exhausted the precision
        for i in 0..<nn {
          for j in 0..<nn {
            if mlsp(symval(q_d_pslq_precision), pslq_mabs(get2(a, i, j))).truthy() {
              set(q_d_pslq_status, Fix(2L)) |> ignore
              return Nil
            }
          }
        }

        // Find maximal value in H
        for i in 0..=(nn - 2) {
          sf = gamma * sf
          if mlsp(
              mm,
              m_star(list2(Flo(sf.to_double()), pslq_mabs(get2(h, i, i)))),
            ).truthy() {
            m = i
            mm = m_star(
              list2(
                Flo(share_pslq_integer_relation__expt(gamma, i).to_double()),
                pslq_mabs(get2(h, i, i)),
              ),
            )
          }
        }

        // Swap entries in y
        let ym = get1(y, m)
        set1(y, m, get1(y, m + 1))
        set1(y, m + 1, ym)
        // Swap rows in A and columns in B
        for i in 0..<nn {
          let am = get2(a, m, i)
          set2(a, m, i, get2(a, m + 1, i))
          set2(a, m + 1, i, am)
          let bm = get2(b, i, m)
          set2(b, i, m, get2(b, i, m + 1))
          set2(b, i, m + 1, bm)
        }
        // Swap rows in H
        for i in 0..=(nn - 2) {
          let hm = get2(h, m, i)
          set2(h, m, i, get2(h, m + 1, i))
          set2(h, m + 1, i, hm)
        }

        // Update H
        if m < nn - 2 {
          let t0 = d_sqrt(
            m_plus(
              list2(
                power(get2(h, m, m), Fix(2L)),
                power(get2(h, m, m + 1), Fix(2L)),
              ),
            ),
          )
          let t1 = m_sl_sl(get2(h, m, m), a2=t0)
          let t2 = m_sl_sl(get2(h, m, m + 1), a2=t0)
          for i in m..<nn {
            let t3 = get2(h, i, m)
            let t4 = get2(h, i, m + 1)
            set2(
              h,
              i,
              m,
              m_plus(list2(m_star(list2(t1, t3)), m_star(list2(t2, t4)))),
            )
            set2(
              h,
              i,
              m + 1,
              m_(m_star(list2(t1, t4)), a2=m_star(list2(t2, t3))),
            )
          }
        }

        // Block reduction on H
        for i in (m + 1)..<nn {
          let mut j = if i - 1 < m + 1 { i - 1 } else { m + 1 }
          while j >= 0 {
            tt = pslq_nearest_integer(m_sl_sl(get2(h, i, j), a2=get2(h, j, j)))
            set1(
              y,
              j,
              m_plus(list2(get1(y, j), m_star(list2(tt, get1(y, i))))),
            )
            for k in 0..=j {
              set2(
                h,
                i,
                k,
                m_(get2(h, i, k), a2=m_star(list2(tt, get2(h, j, k)))),
              )
            }
            for k in 0..<nn {
              set2(
                a,
                i,
                k,
                m_(get2(a, i, k), a2=m_star(list2(tt, get2(a, j, k)))),
              )
              set2(
                b,
                k,
                j,
                m_plus(list2(get2(b, k, j), m_star(list2(tt, get2(b, k, i))))),
              )
            }
            j = j - 1
          }
        }
        r = num_add(r, Fix(1L))
      }
      set(q_d_pslq_status, Fix(3L)) |> ignore
      Nil
    },
  )
}

///|
/// The MAYBE-RESET part of DEFMVAR: record the initial value of a
/// variable so that `reset` restores it.
fn share_pslq_integer_relation__defmvar_reset(
  var_ : Value,
  val : Value,
) -> Unit raise {
  let table = symval(q_ear_variable_initial_values)
  if hash_table_p(table) && gethash(var_, table) is Nil {
    sethash(var_, table, val) |> ignore
  }
}

///|
fn init_share_pslq_integer_relation() -> Unit raise {
  d_put(q_d_pslq_integer_relation, Flo(1.0), q_d_version) |> ignore
  share_pslq_integer_relation__defmvar_reset(q_d_pslq_precision, Nil)
  share_pslq_integer_relation__defmvar_reset(q_d_pslq_threshold, Nil)
  share_pslq_integer_relation__defmvar_reset(q_d_pslq_depth, Nil)
  share_pslq_integer_relation__defmvar_reset(q_d_pslq_status, Fix(0L))
  share_pslq_integer_relation__defmvar_reset(q_d_pslq_fail_norm, Nil)
}
