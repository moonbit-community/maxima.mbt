// Port of share/descriptive/descriptive_util.lisp: additional functions
// needed by package descriptive.

///|
fn d_unique_in_sorted_array(a : Value) -> Value raise {
  let mut prev = gensym()
  let acc = Collector::new()
  let n = length(a)
  for i in 0..<n {
    let x = aref1(a, i)
    let old = prev
    prev = x
    if !alike1(old, x).truthy() {
      acc.add(x)
    }
  }
  cons(list1(q_mlist), acc.result())
}

///|
/// Returns NIL if A is empty.
fn d_vector_min_max(a : Value) -> Value raise {
  if length(a) > 0 {
    let mut min_a = q_d_inf
    let mut max_a = q_d_minf
    with_special(q_d_ratprint, Nil, () => {
      let n = length(a)
      for i in 0..<n {
        let x = aref1(a, i)
        let cmp_min = d_compare(x, min_a)
        let cmp_max = d_compare(x, max_a)
        if share_descriptive_util__string_eq(cmp_min, "<") {
          min_a = x
        }
        if share_descriptive_util__string_eq(cmp_max, ">") {
          max_a = x
        }
      }
    })
    list([list1(q_mlist), min_a, max_a])
  } else {
    Nil
  }
}

///|
/// (string= x s) for a string designator X.
fn share_descriptive_util__string_eq(x : Value, s : String) -> Bool raise {
  match x {
    Str(xs) => xs == s
    _ => lstring(x) == s
  }
}

///|
fn init_share_descriptive_util() -> Unit raise {

}
